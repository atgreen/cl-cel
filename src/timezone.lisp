;;;; SPDX-FileCopyrightText: 2026 Anthony Green <green@moxielogic.com>
;;;; SPDX-License-Identifier: MIT

(in-package #:cl-cel)

(define-condition invalid-time-zone (error)
  ((text :initarg :text :reader invalid-time-zone-text))
  (:report (lambda (condition stream)
             (write-string (invalid-time-zone-text condition) stream)))
  (:documentation "A named time zone that cannot be resolved."))

(defun time-zone-error (control &rest arguments)
  "Signal that a named time zone cannot be resolved."
  (error 'invalid-time-zone :text (apply #'format nil control arguments)))

;;; Time zones: an offset table read from a compiled TZif file.

(defstruct time-zone
  "Transition times in universal time, with the UTC offset each begins and the offset before the first."
  transitions offsets initial)

(defparameter +unix-epoch-universal+ 2208988800
  "The universal time of the Unix epoch.")

(defvar *time-zones* (make-hash-table :test #'equal)
  "Time zones already loaded, by name.")

(defvar *time-zones-lock* (bt:make-lock "cl-cel time zones")
  "Guards *TIME-ZONES*.")

(defparameter *zoneinfo-directory* "/usr/share/zoneinfo/"
  "The host's compiled time zone database.")

(defun time-zone-offset (zone time)
  "Return the seconds east of UTC in ZONE at universal TIME; a NIL ZONE is UTC."
  (if (null zone)
      0
      (let* ((transitions (time-zone-transitions zone)) (low 0) (high (length transitions)))
        (loop while (< low high)
              do (let ((middle (floor (+ low high) 2)))
                   (if (<= (aref transitions middle) time) (setf low (1+ middle)) (setf high middle))))
        (if (zerop low) (time-zone-initial zone) (aref (time-zone-offsets zone) (1- low))))))

(defun tzif-integer (bytes start size)
  "Read a signed big-endian integer of SIZE bytes."
  (let ((value (loop with total = 0
                     for index from start below (+ start size)
                     do (setf total (+ (* total 256) (aref bytes index)))
                     finally (return total))))
    (if (logbitp (1- (* 8 size)) value) (- value (ash 1 (* 8 size))) value)))

(defun posix-tz-offset-end (text start)
  "Parse a POSIX TZ [+-]hh[:mm[:ss]] at START, returning its seconds and where it ends."
  (let* ((sign (case (and (< start (length text)) (char text start)) (#\- -1) (t 1)))
         (position (if (and (< start (length text)) (find (char text start) "+-")) (1+ start) start))
         (total 0))
    (loop for unit in '(3600 60 1)
          do (multiple-value-bind (value end) (parse-integer text :start position :junk-allowed t)
               (unless value (time-zone-error "Malformed time zone rule"))
               (incf total (* unit value))
               (setf position end)
               (if (and (< position (length text)) (char= #\: (char text position)))
                   (incf position)
                   (return))))
    (values (* sign total) position)))

(defun posix-tz-name-end (text start)
  "Return where the POSIX TZ zone name at START ends: quoted in angle brackets, or letters."
  (if (and (< start (length text)) (char= #\< (char text start)))
      (1+ (or (position #\> text :start start) (time-zone-error "Malformed time zone rule")))
      (or (position-if-not #'alpha-char-p text :start start) (length text))))

(defun parse-posix-tz-rule (text)
  "Parse a Mm.w.d[/time] date rule into (month week weekday seconds).
The other two POSIX date forms name fixed days, which no recurring zone in the database uses."
  (let* ((slash (position #\/ text))
         (parts (uiop:split-string (subseq text 1 slash) :separator '(#\.)))
         (fields (mapcar (lambda (part) (parse-integer part :junk-allowed t)) parts)))
    (unless (and (char= #\M (char text 0)) (= 3 (length fields)) (every #'identity fields))
      (time-zone-error "Unsupported time zone rule ~S" text))
    (append fields (list (if slash (posix-tz-offset-end text (1+ slash)) 7200)))))

(defun posix-tz-rule-time (rule year offset)
  "Return the universal time RULE falls on in YEAR, where clocks read OFFSET seconds east of UTC."
  (destructuring-bind (month week weekday seconds) rule
    (let* ((first (encode-universal-time 0 0 0 1 month year 0))
           (first-weekday (mod (1+ (nth-value 6 (decode-universal-time first 0))) 7))
           (next-month (if (= month 12)
                           (encode-universal-time 0 0 0 1 1 (1+ year) 0)
                           (encode-universal-time 0 0 0 1 (1+ month) year 0)))
           (day (+ (mod (- weekday first-weekday) 7) (* 7 (1- week)))))
      (loop while (>= (+ first (* day 86400)) next-month) do (decf day 7))
      (- (+ first (* day 86400) seconds) offset))))

(defun extend-zone-transitions (transitions offsets footer now)
  "Append the changes FOOTER's recurring rule makes through decades past NOW to the zone's tables."
  (let* ((std-end (posix-tz-name-end footer 0)))
    (multiple-value-bind (std-west std-next) (posix-tz-offset-end footer std-end)
      (let* ((dst-end (posix-tz-name-end footer std-next))
             (comma (position #\, footer))
             (std (- std-west))
             (dst (if (< dst-end comma) (- (posix-tz-offset-end footer dst-end)) (+ std 3600)))
             (rules (uiop:split-string (subseq footer (1+ comma)) :separator '(#\,)))
             (times (length transitions))
             (last (if (plusp times) (aref transitions (1- times)) (- now (* 366 86400))))
             (first-year (nth-value 5 (decode-universal-time last 0)))
             (last-year (+ 25 (nth-value 5 (decode-universal-time now 0))))
             (added nil))
        (unless (= 2 (length rules)) (time-zone-error "Malformed time zone rule"))
        (let ((start (parse-posix-tz-rule (first rules))) (end (parse-posix-tz-rule (second rules))))
          (loop for year from first-year to last-year
                do (let ((to-dst (posix-tz-rule-time start year std))
                         (to-std (posix-tz-rule-time end year dst)))
                     (when (> to-dst last) (push (cons to-dst dst) added))
                     (when (> to-std last) (push (cons to-std std) added)))))
        (let ((sorted (sort added #'< :key #'car)))
          (values (concatenate 'vector transitions (mapcar #'car sorted))
                  (concatenate 'vector offsets (mapcar #'cdr sorted))))))))

(defun parse-tzif (bytes now)
  "Build a TIME-ZONE from TZif BYTES, refusing one whose rules for times past its table are unread."
  (flet ((check (start)
           (unless (and (>= (length bytes) (+ start 44))
                        (equalp (subseq bytes start (+ start 4)) #(84 90 105 102)))
             (time-zone-error "Malformed time zone file")))
         (count-at (start index) (tzif-integer bytes (+ start 20 (* 4 index)) 4)))
    (check 0)
    (let* ((version2 (plusp (aref bytes 4))) (start 0) (size 4))
      (when version2
        (setf start (+ 44 (* 4 (count-at 0 3)) (* 1 (count-at 0 3)) (* 6 (count-at 0 4)) (count-at 0 5)
                       (* 8 (count-at 0 2)) (count-at 0 1) (count-at 0 0))
              size 8)
        (check start))
      (let* ((times (count-at start 3)) (types (count-at start 4)) (chars (count-at start 5))
             (leaps (count-at start 2)) (standard (count-at start 1)) (universal (count-at start 0))
             (time-base (+ start 44)) (index-base (+ time-base (* size times)))
             (type-base (+ index-base times))
             (end (+ type-base (* 6 types) chars (* (+ size 4) leaps) standard universal))
             (footer (if (and version2 (< (1+ end) (length bytes)))
                         (map 'string #'code-char (subseq bytes (1+ end) (max (1+ end) (1- (length bytes)))))
                         ""))
             (transitions (make-array times)) (offsets (make-array times)))
        (when (or (zerop types) (> end (length bytes))) (time-zone-error "Malformed time zone file"))
        (dotimes (position times)
          (setf (aref transitions position)
                (+ +unix-epoch-universal+ (tzif-integer bytes (+ time-base (* size position)) size))
                (aref offsets position)
                (tzif-integer bytes (+ type-base (* 6 (aref bytes (+ index-base position)))) 4)))
        ;; Slim zone files stop listing changes once a recurring rule covers them.
        (when (and (find #\, footer) (or (zerop times) (< (aref transitions (1- times)) (+ now (* 366 86400)))))
          (multiple-value-setq (transitions offsets) (extend-zone-transitions transitions offsets footer now)))
        (make-time-zone :transitions transitions :offsets offsets
                        :initial (tzif-integer bytes type-base 4))))))

(defun load-time-zone (name)
  "Return NAME's zone, NIL for UTC, signalling INVALID-CRON-SCHEDULE for one that cannot be used."
  (when (member name '("UTC" "Etc/UTC") :test #'equal) (return-from load-time-zone nil))
  (bt:with-lock-held (*time-zones-lock*)
    (or (gethash name *time-zones*)
        (progn
          (unless (and (stringp name) (<= 1 (length name) 255)
                       (not (search ".." name)) (not (char= #\/ (char name 0))) (not (equal name "Local"))
                       (every (lambda (character) (or (alphanumericp character) (find character "/_+-"))) name))
            (time-zone-error "Invalid time zone name ~S" name))
          (let ((path (concatenate 'string *zoneinfo-directory* name)))
            (unless (and (probe-file path) (pathname-name (probe-file path)))
              (time-zone-error "Unknown time zone ~S" name))
            (setf (gethash name *time-zones*)
                  (parse-tzif (handler-case
                                  (with-open-file (stream path :element-type '(unsigned-byte 8))
                                    (let ((bytes (make-array (file-length stream) :element-type '(unsigned-byte 8))))
                                      (read-sequence bytes stream)
                                      bytes))
                                (error () (time-zone-error "Cannot read time zone ~S" name)))
                              (get-universal-time))))))))

