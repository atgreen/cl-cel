;;;; SPDX-FileCopyrightText: 2026 Anthony Green <green@moxielogic.com>
;;;; SPDX-License-Identifier: MIT
;;;;
;;;; Purpose:
;;;; The standard CEL functions and reusable libraries as overload tables:
;;;; conversions, strings, lists, sets, regular expressions, time, quantities,
;;;; URLs, IP addresses and CIDRs, semantic versions, formats and optionals.
;;;; A function that is not listed fails compilation rather than misbehaving.

(in-package #:cl-cel)

(defstruct (cel-overload (:conc-name overload-)) receiver parameters result function)

(defmacro define-cel-function (name (receiver &rest parameters) result lambda-list &body body)
  "Add an overload of NAME: RECEIVER and PARAMETERS are type specs, RESULT a type or function of the static types."
  `(setf (gethash ,name *cel-functions*)
         (append (gethash ,name *cel-functions*)
                 (list (make-cel-overload :receiver ',receiver :parameters ',parameters :result ,result
                                          :function (lambda ,lambda-list (declare (ignorable ,@lambda-list)) ,@body))))))

(defun cel-spec-accepts-type-p (spec type)
  "Test whether a parameter SPEC can statically accept TYPE."
  (let ((head (cel-type-head type)))
    (cond ((eq spec :any) t)
          ((eq head :dyn) t)
          ((consp spec) (and (eq head (first spec)) (consp type) (eq (second type) (second spec))))
          ((eq spec :map) (member head '(:map :object)))
          (t (eq head spec)))))

(defun cel-spec-accepts-value-p (spec value)
  "Test whether a parameter SPEC accepts the evaluated VALUE."
  (if (consp spec)
      (and (cel-opaque-p value) (eq (cel-opaque-kind value) (second spec)))
      (ecase spec
        (:any t)
        (:string (stringp value))
        (:int (integerp value))
        (:uint (cel-uint-p value))
        (:double (floatp value))
        (:bool (cel-bool-p value))
        (:bytes (cel-bytes-p value))
        (:list (cel-list-p value))
        (:map (hash-table-p value))
        (:timestamp (cel-timestamp-p value))
        (:duration (cel-duration-p value))
        (:optional (cel-optional-p value)))))

(defun cel-check-library-call (name receiver argument-types)
  "Find NAME's overloads for these static types and return the call's result type."
  (let ((overloads (gethash name *cel-functions*)))
    (unless overloads
      (cel-check-error "undeclared reference to '~A'" name))
    (let ((matching
            (remove-if-not
             (lambda (overload)
               (and (= (length (overload-parameters overload)) (length argument-types))
                    (if receiver
                        (and (overload-receiver overload) (cel-spec-accepts-type-p (overload-receiver overload) receiver))
                        (null (overload-receiver overload)))
                    (every #'cel-spec-accepts-type-p (overload-parameters overload) argument-types)))
             overloads)))
      (unless matching
        (cel-overload-error name (if receiver (cons receiver argument-types) argument-types)))
      (let ((results (remove-duplicates
                      (mapcar (lambda (overload)
                                (let ((result (overload-result overload)))
                                  (if (functionp result) (funcall result receiver argument-types) result)))
                              matching)
                      :test #'equal)))
        (if (rest results) :dyn (first results))))))

(defun cel-apply-library-call (name target arguments)
  "Apply the overload of NAME that accepts these evaluated values."
  (let* ((receiver (and target (first target)))
         (overload (find-if
                    (lambda (overload)
                      (and (= (length (overload-parameters overload)) (length arguments))
                           (if target
                               (and (overload-receiver overload) (cel-spec-accepts-value-p (overload-receiver overload) receiver))
                               (null (overload-receiver overload)))
                           (every #'cel-spec-accepts-value-p (overload-parameters overload) arguments)))
                    (gethash name *cel-functions*))))
    (unless overload (cel-fail "no such overload: ~A" name))
    (if target
        (apply (overload-function overload) receiver arguments)
        (apply (overload-function overload) arguments))))

(defun cel-opaque (kind value)
  "Wrap VALUE as the library object KIND."
  (make-cel-opaque :kind kind :value value))

(defun cel-opaque-type (kind)
  "Return the static type of the library object KIND."
  (list :opaque kind))

(defun cel-some (value)
  "Wrap VALUE as a present optional."
  (make-cel-optional :value value :present t))

(defun cel-receiver-type (receiver arguments)
  "Return a call's static receiver type, for result functions."
  (declare (ignore arguments))
  receiver)

;;; Field name escaping, used by CEL object fields.

(defun cel-unescape-field (field)
  "Undo CEL property name escaping: __dot__ __dash__ __slash__ __underscores__ and __keyword__."
  (let ((result field))
    (when (and (> (length result) 4) (uiop:string-prefix-p "__" result) (uiop:string-suffix-p result "__"))
      (let ((inner (subseq result 2 (- (length result) 2))))
        (when (member inner '("true" "false" "null" "in" "as" "break" "const" "continue" "else" "for" "function"
                              "if" "import" "let" "loop" "package" "namespace" "return" "var" "void" "while")
                      :test #'equal)
          (return-from cel-unescape-field inner))))
    (dolist (pair '(("__underscores__" . "__") ("__dot__" . ".") ("__dash__" . "-") ("__slash__" . "/")) result)
      (setf result (cl-ppcre:regex-replace-all (car pair) result (cdr pair))))))

;;; Conversions

(defparameter +cel-minimum-timestamp-seconds+ -62135596800 "0001-01-01T00:00:00Z.")
(defparameter +cel-maximum-timestamp-seconds+ 253402300799 "9999-12-31T23:59:59Z.")
(defparameter +cel-maximum-duration-seconds+ 315576000000 "Ten thousand years, CEL's duration range.")

(defun cel-checked-timestamp (nanos)
  "Wrap NANOS as a timestamp when within CEL's range."
  (unless (<= +cel-minimum-timestamp-seconds+ (floor nanos 1000000000) +cel-maximum-timestamp-seconds+)
    (cel-fail "timestamp out of range"))
  (make-cel-timestamp :nanos nanos))

(defun cel-checked-duration (nanos)
  "Wrap NANOS as a duration when within CEL's range."
  (unless (<= (abs nanos) (* +cel-maximum-duration-seconds+ 1000000000))
    (cel-fail "duration out of range"))
  (make-cel-duration :nanos nanos))

(defun cel-days-from-civil (year month day)
  "Count days from the Unix epoch to a proleptic Gregorian date."
  (let* ((y (if (<= month 2) (1- year) year))
         (era (floor y 400))
         (yoe (- y (* era 400)))
         (doy (+ (floor (+ (* 153 (+ month (if (> month 2) -3 9))) 2) 5) (1- day)))
         (doe (+ (* yoe 365) (floor yoe 4) (- (floor yoe 100)) doy)))
    (+ (* era 146097) doe -719468)))

(defun cel-civil-from-days (days)
  "Return the year, month and day of a count of days from the Unix epoch."
  (let* ((z (+ days 719468))
         (era (floor z 146097))
         (doe (- z (* era 146097)))
         (yoe (floor (- doe (floor doe 1460) (- (floor doe 36524)) (floor doe 146096)) 365))
         (doy (- doe (- (+ (* 365 yoe) (floor yoe 4)) (floor yoe 100))))
         (mp (floor (+ (* 5 doy) 2) 153))
         (day (1+ (- doy (floor (+ (* 153 mp) 2) 5))))
         (month (if (< mp 10) (+ mp 3) (- mp 9))))
    (values (+ yoe (* era 400) (if (<= month 2) 1 0)) month day)))

(defun cel-parse-rfc3339 (text)
  "Parse an RFC 3339 timestamp into nanoseconds since the epoch, or NIL."
  (cl-ppcre:register-groups-bind (year month day hour minute second fraction offset)
      ("^([0-9]{4})-([0-9]{2})-([0-9]{2})[Tt]([0-9]{2}):([0-9]{2}):([0-9]{2})(?:\\.([0-9]{1,9}))?([Zz]|[+-][0-9]{2}:[0-9]{2})$" text)
    (let ((year (parse-integer year)) (month (parse-integer month)) (day (parse-integer day))
          (hour (parse-integer hour)) (minute (parse-integer minute)) (second (parse-integer second)))
      (when (and (<= 1 month 12) (<= 1 day 31) (<= hour 23) (<= minute 59) (<= second 59)
                 (multiple-value-bind (y m d) (cel-civil-from-days (cel-days-from-civil year month day))
                   (and (= y year) (= m month) (= d day))))
        (let ((seconds (+ (* 86400 (cel-days-from-civil year month day)) (* 3600 hour) (* 60 minute) second))
              (nanos (if fraction (* (parse-integer fraction) (expt 10 (- 9 (length fraction)))) 0)))
          (unless (find (char offset 0) "Zz")
            (let ((shift (+ (* 3600 (parse-integer offset :start 1 :end 3)) (* 60 (parse-integer offset :start 4)))))
              (setf seconds (if (char= #\+ (char offset 0)) (- seconds shift) (+ seconds shift)))))
          (+ (* seconds 1000000000) nanos))))))

(defun cel-format-timestamp (nanos)
  "Print NANOS since the epoch as RFC 3339 in UTC."
  (multiple-value-bind (total fraction) (floor nanos 1000000000)
    (multiple-value-bind (days rest) (floor total 86400)
      (multiple-value-bind (year month day) (cel-civil-from-days days)
        (format nil "~4,'0D-~2,'0D-~2,'0DT~2,'0D:~2,'0D:~2,'0D~@[.~A~]Z"
                year month day (floor rest 3600) (floor (mod rest 3600) 60) (mod rest 60)
                (when (plusp fraction)
                  (string-right-trim "0" (format nil "~9,'0D" fraction))))))))

(defun cel-parse-duration (text)
  "Parse a Go duration string such as 1h30m or -1.5s into nanoseconds, or NIL."
  (let ((position 0) (total 0) (negative nil) (size (length text)))
    (when (zerop size) (return-from cel-parse-duration nil))
    (when (find (char text 0) "+-")
      (setf negative (char= (char text 0) #\-))
      (incf position))
    (when (equal (subseq text position) "0") (return-from cel-parse-duration 0))
    (when (>= position size) (return-from cel-parse-duration nil))
    (loop while (< position size)
          do (let* ((start position)
                    (dot nil))
               (loop while (and (< position size) (or (digit-char-p (char text position)) (char= #\. (char text position))))
                     do (when (char= #\. (char text position))
                          (when dot (return-from cel-parse-duration nil))
                          (setf dot position))
                        (incf position))
               (when (or (= start position) (and dot (= (- position start) 1)))
                 (return-from cel-parse-duration nil))
               (let* ((unit-start position)
                      (unit-end (or (position-if (lambda (character) (or (digit-char-p character) (char= #\. character)))
                                                 text :start position)
                                    size))
                      (scale (cdr (assoc (subseq text unit-start unit-end)
                                         '(("ns" . 1) ("us" . 1000) ("ms" . 1000000) ("s" . 1000000000)
                                           ("m" . 60000000000) ("h" . 3600000000000)
                                           ("µs" . 1000) ("μs" . 1000))
                                         :test #'equal))))
                 (unless scale (return-from cel-parse-duration nil))
                 (let* ((whole (subseq text start (or dot unit-start)))
                        (fraction (if dot (subseq text (1+ dot) unit-start) ""))
                        (amount (+ (if (plusp (length whole)) (parse-integer whole) 0)
                                   (if (plusp (length fraction))
                                       (/ (parse-integer fraction) (expt 10 (length fraction)))
                                       0))))
                   (incf total (floor (* amount scale))))
                 (setf position unit-end))))
    (if negative (- total) total)))

(defun cel-format-duration (nanos)
  "Print a duration as CEL's string conversion does, in seconds with an s suffix."
  (multiple-value-bind (seconds fraction) (truncate (abs nanos) 1000000000)
    (format nil "~:[~;-~]~D~@[.~A~]s" (minusp nanos) seconds
            (when (plusp fraction) (string-right-trim "0" (format nil "~9,'0D" fraction))))))

(define-cel-function "int" (nil :int) :int (value) value)
(define-cel-function "int" (nil :uint) :int (value) (cel-int64 (cel-uint-value value)))
(define-cel-function "int" (nil :double) :int (value)
  (handler-case (cel-int64 (truncate value))
    (arithmetic-error () (cel-fail "integer overflow"))))
(define-cel-function "int" (nil :string) :int (value)
  (unless (cl-ppcre:scan "^[+-]?[0-9]+$" value) (cel-fail "type conversion error to int"))
  (cel-int64 (parse-integer value)))
(define-cel-function "int" (nil :timestamp) :int (value) (floor (cel-timestamp-nanos value) 1000000000))
(define-cel-function "int" (nil :duration) :int (value) (cel-duration-nanos value))

(define-cel-function "uint" (nil :uint) :uint (value) value)
(define-cel-function "uint" (nil :int) :uint (value) (cel-uint64 value))
(define-cel-function "uint" (nil :double) :uint (value)
  (handler-case (cel-uint64 (truncate value))
    (arithmetic-error () (cel-fail "unsigned integer overflow"))))
(define-cel-function "uint" (nil :string) :uint (value)
  (unless (cl-ppcre:scan "^[0-9]+$" value) (cel-fail "type conversion error to uint"))
  (cel-uint64 (parse-integer value)))

(define-cel-function "double" (nil :double) :double (value) value)
(define-cel-function "double" (nil :int) :double (value) (coerce value 'double-float))
(define-cel-function "double" (nil :uint) :double (value) (coerce (cel-uint-value value) 'double-float))
(define-cel-function "double" (nil :string) :double (value)
  (handler-case
      (multiple-value-bind (number next type) (cel-read-number value (if (find (char value 0) "+-") 1 0))
        (declare (ignore type))
        (unless (= next (length value)) (error "trailing text"))
        (let ((magnitude (coerce number 'double-float)))
          (if (char= #\- (char value 0)) (- magnitude) magnitude)))
    (error () (cel-fail "type conversion error to double"))))

(define-cel-function "string" (nil :string) '(:string nil) (value) value)
(define-cel-function "string" (nil :int) :string (value) (write-to-string value :base 10 :radix nil))
(define-cel-function "string" (nil :uint) :string (value) (write-to-string (cel-uint-value value) :base 10 :radix nil))
(define-cel-function "string" (nil :double) :string (value)
  (com.inuoe.jzon:stringify value))
(define-cel-function "string" (nil :bool) :string (value) (if value "true" "false"))
(define-cel-function "string" (nil :bytes) :string (value)
  (handler-case (trivial-utf-8:utf-8-bytes-to-string value)
    (error () (cel-fail "invalid UTF-8 in bytes, cannot convert to string"))))
(define-cel-function "string" (nil :timestamp) :string (value) (cel-format-timestamp (cel-timestamp-nanos value)))
(define-cel-function "string" (nil :duration) :string (value) (cel-format-duration (cel-duration-nanos value)))

(define-cel-function "bool" (nil :bool) :bool (value) value)
(define-cel-function "bool" (nil :string) :bool (value)
  (cond ((member value '("1" "t" "T" "true" "TRUE" "True") :test #'equal) t)
        ((member value '("0" "f" "F" "false" "FALSE" "False") :test #'equal) nil)
        (t (cel-fail "type conversion error to bool"))))

(define-cel-function "bytes" (nil :bytes) :bytes (value) value)
(define-cel-function "bytes" (nil :string) :bytes (value) (trivial-utf-8:string-to-utf-8-bytes value))

(define-cel-function "timestamp" (nil :timestamp) :timestamp (value) value)
(define-cel-function "timestamp" (nil :int) :timestamp (value) (cel-checked-timestamp (* value 1000000000)))
(define-cel-function "timestamp" (nil :string) :timestamp (value)
  (cel-checked-timestamp (or (cel-parse-rfc3339 value) (cel-fail "type conversion error to timestamp"))))

(define-cel-function "duration" (nil :duration) :duration (value) value)
(define-cel-function "duration" (nil :int) :duration (value) (cel-checked-duration value))
(define-cel-function "duration" (nil :string) :duration (value)
  (cel-checked-duration (or (cel-parse-duration value) (cel-fail "type conversion error to duration"))))

;;; Size

(flet ((size (value)
         (cond ((stringp value) (length value))
               ((or (cel-bytes-p value) (cel-list-p value)) (length value))
               ((hash-table-p value) (hash-table-count value))
               (t (cel-fail "no such overload: size")))))
  (dolist (spec '(:string :bytes :list :map))
    (setf (gethash "size" *cel-functions*)
          (append (gethash "size" *cel-functions*)
                  (list (make-cel-overload :receiver nil :parameters (list spec) :result :int :function #'size)
                        (make-cel-overload :receiver spec :parameters nil :result :int :function #'size))))))

;;; Time getters

(defun cel-timezone-offset (zone seconds)
  "Return ZONE's offset from UTC in seconds at SECONDS past the Unix epoch.
A ZONE with a colon is a fixed offset, as cel-go reads it; any other names a zone in the
host's time zone database, as Go's time.LoadLocation does."
  (cond ((member zone '("UTC" "") :test #'equal) 0)
        ((cl-ppcre:scan "^[+-]?[0-9]{1,2}:[0-9]{2}$" zone)
         (let* ((signed (find (char zone 0) "+-"))
                (colon (position #\: zone))
                (hours (parse-integer zone :start (if signed 1 0) :end colon))
                (minutes (parse-integer zone :start (1+ colon)))
                (magnitude (+ (* 3600 hours) (* 60 minutes))))
           (if (eql signed #\-) (- magnitude) magnitude)))
        ((find #\: zone) (cel-fail "unknown time zone ~A" zone))
        (t (let ((loaded (handler-case (load-time-zone zone)
                           (invalid-time-zone () (cel-fail "unknown time zone ~A" zone)))))
             (time-zone-offset loaded (+ seconds +unix-epoch-universal+))))))

(defun cel-timestamp-field (timestamp zone field)
  "Read the calendar FIELD of TIMESTAMP in ZONE."
  (multiple-value-bind (seconds fraction) (floor (cel-timestamp-nanos timestamp) 1000000000)
    (multiple-value-bind (days rest) (floor (+ seconds (cel-timezone-offset zone seconds)) 86400)
      (multiple-value-bind (year month day) (cel-civil-from-days days)
        (ecase field
          (:year year)
          (:month (1- month))
          (:date day)
          (:day-of-month (1- day))
          (:day-of-week (mod (+ 4 days) 7))
          (:day-of-year (- days (cel-days-from-civil year 1 1)))
          (:hours (floor rest 3600))
          (:minutes (floor (mod rest 3600) 60))
          (:seconds (mod rest 60))
          (:milliseconds (floor fraction 1000000)))))))

(macrolet ((getters (&rest pairs)
             `(progn
                ,@(loop for (name field) on pairs by #'cddr
                        collect `(define-cel-function ,name (:timestamp) :int (value) (cel-timestamp-field value "UTC" ,field))
                        collect `(define-cel-function ,name (:timestamp :string) :int (value zone)
                                   (cel-timestamp-field value zone ,field))))))
  (getters "getFullYear" :year "getMonth" :month "getDate" :date "getDayOfMonth" :day-of-month
           "getDayOfWeek" :day-of-week "getDayOfYear" :day-of-year "getHours" :hours
           "getMinutes" :minutes "getSeconds" :seconds "getMilliseconds" :milliseconds))

(define-cel-function "getHours" (:duration) :int (value) (truncate (cel-duration-nanos value) 3600000000000))
(define-cel-function "getMinutes" (:duration) :int (value) (truncate (cel-duration-nanos value) 60000000000))
(define-cel-function "getSeconds" (:duration) :int (value) (truncate (cel-duration-nanos value) 1000000000))
(define-cel-function "getMilliseconds" (:duration) :int (value) (truncate (cel-duration-nanos value) 1000000))

;;; Strings

(defun cel-split-limited (text separator limit)
  "Split TEXT on SEPARATOR into at most LIMIT parts (a negative LIMIT means all), as Go does."
  (cond
    ((zerop limit) #())
    ((zerop (length separator))
     ;; An empty separator splits into characters.
     (let* ((count (if (minusp limit) (length text) (min limit (length text))))
            (parts (loop for index from 0 below count
                         collect (if (and (= index (1- count)) (> (length text) count))
                                     (subseq text index)
                                     (string (char text index))))))
       (coerce parts 'vector)))
    (t
     (coerce (loop with start = 0
                   for taken from 1
                   for found = (if (and (plusp limit) (>= taken limit)) nil (search separator text :start2 start))
                   collect (subseq text start found)
                   while found
                   do (setf start (+ found (length separator))))
             'vector))))

(defun cel-replace-limited (text old new limit)
  "Replace up to LIMIT occurrences of OLD in TEXT with NEW (a negative LIMIT means all), as Go does."
  (with-output-to-string (out)
    (if (zerop (length old))
        (let ((count 0))
          (loop for index from 0 to (length text)
                do (when (or (minusp limit) (< count limit))
                     (write-string new out)
                     (incf count))
                   (when (< index (length text)) (write-char (char text index) out))))
        (loop with start = 0 with count = 0
              for found = (and (or (minusp limit) (< count limit)) (search old text :start2 start))
              do (write-string text out :start start :end found)
              while found
              do (write-string new out)
                 (incf count)
                 (setf start (+ found (length old)))))))

(defun cel-ascii-case (text upcase)
  "Change the case of only the ASCII letters in TEXT."
  (map 'string (lambda (character)
                 (if (< (char-code character) 128)
                     (if upcase (char-upcase character) (char-downcase character))
                     character))
       text))

(defun cel-string-result-size (receiver arguments)
  "Keep a string's bound through a function that does not grow it."
  (declare (ignore arguments))
  (if (consp receiver) receiver :string))

(defun cel-trim-string (text)
  "Remove Unicode whitespace from both ends of TEXT, as ext.strings' trim does."
  (string-trim (list #\Space #\Tab #\Newline #\Return #\Page (code-char 11) (code-char #x85) (code-char #xA0)) text))

(defun cel-index-of (text substring start)
  "Find SUBSTRING in TEXT from START, or -1."
  (unless (<= 0 start (length text)) (cel-fail "index out of range: ~D" start))
  (or (search substring text :start2 start) -1))

(defun cel-last-index-of (text substring end)
  "Find the last SUBSTRING in TEXT starting at or before END, or -1."
  (unless (<= 0 end (length text)) (cel-fail "index out of range: ~D" end))
  (or (search substring text :from-end t :end2 (min (length text) (+ end (length substring)))) -1))

(define-cel-function "startsWith" (:string :string) :bool (text prefix)
  (and (>= (length text) (length prefix)) (string= prefix text :end2 (length prefix))))
(define-cel-function "endsWith" (:string :string) :bool (text suffix)
  (and (>= (length text) (length suffix)) (string= suffix text :start2 (- (length text) (length suffix)))))
(define-cel-function "contains" (:string :string) :bool (text part) (and (search part text) t))
(define-cel-function "lowerAscii" (:string) #'cel-string-result-size (text) (cel-ascii-case text nil))
(define-cel-function "upperAscii" (:string) #'cel-string-result-size (text) (cel-ascii-case text t))
(define-cel-function "trim" (:string) #'cel-string-result-size (text) (cel-trim-string text))
(define-cel-function "split" (:string :string) '(:list (:string nil) nil) (text separator)
  (cel-split-limited text separator -1))
(define-cel-function "split" (:string :string :int) '(:list (:string nil) nil) (text separator limit)
  (cel-split-limited text separator limit))
(define-cel-function "replace" (:string :string :string) :string (text old new)
  (cel-replace-limited text old new -1))
(define-cel-function "replace" (:string :string :string :int) :string (text old new limit)
  (cel-replace-limited text old new limit))

;;; JSON patch keys

(define-cel-function "jsonpatch.escapeKey" (nil :string) :string (key)
  (cel-replace-limited (cel-replace-limited key "~" "~0" -1) "/" "~1" -1))

;;; Authorizer: the check itself comes from *CEL-AUTHORIZER-CHECK*, bound by admission.

(defun cel-authorizer-step (kind state key value)
  "Return a copy of a builder object with KEY set."
  (cel-opaque kind (list* key value state)))

(macrolet ((builder (name from to key)
             `(define-cel-function ,name ((:opaque ,from) :string) (cel-opaque-type ,to) (object value)
                (cel-authorizer-step ,to (cel-opaque-value object) ,key value))))
  (builder "group" :authorizer :group-check :group)
  (builder "path" :authorizer :path-check :path)
  (builder "resource" :group-check :resource-check :resource)
  (builder "subresource" :resource-check :resource-check :subresource)
  (builder "namespace" :resource-check :resource-check :namespace)
  (builder "name" :resource-check :resource-check :name))

(define-cel-function "serviceAccount" ((:opaque :authorizer) :string :string) (cel-opaque-type :authorizer) (object namespace name)
  (cel-opaque :authorizer
              (list* :user (format nil "system:serviceaccount:~A:~A" namespace name)
                     :groups (list "system:serviceaccounts" (format nil "system:serviceaccounts:~A" namespace)
                                   "system:authenticated")
                     (cel-opaque-value object))))

(flet ((check (object verb)
         (unless *cel-authorizer-check* (cel-fail "the authorizer is not available in this expression"))
         (multiple-value-bind (allowed reason problem)
             (funcall *cel-authorizer-check* (cel-opaque-value object) verb)
           (cel-opaque :decision (list allowed (or reason "") problem)))))
  (dolist (kind '(:path-check :resource-check))
    (setf (gethash "check" *cel-functions*)
          (append (gethash "check" *cel-functions*)
                  (list (make-cel-overload :receiver (list :opaque kind) :parameters '(:string)
                                           :result (cel-opaque-type :decision) :function #'check))))))

(define-cel-function "allowed" ((:opaque :decision)) :bool (decision) (and (first (cel-opaque-value decision)) t))
(define-cel-function "reason" ((:opaque :decision)) :string (decision) (second (cel-opaque-value decision)))
(define-cel-function "errored" ((:opaque :decision)) :bool (decision) (and (third (cel-opaque-value decision)) t))
(define-cel-function "error" ((:opaque :decision)) :string (decision) (or (third (cel-opaque-value decision)) ""))

(define-cel-function "charAt" (:string :int) :string (text index)
  (cond ((= index (length text)) "")
        ((< -1 index (length text)) (string (char text index)))
        (t (cel-fail "index out of range: ~D" index))))
(define-cel-function "indexOf" (:string :string) :int (text part) (cel-index-of text part 0))
(define-cel-function "indexOf" (:string :string :int) :int (text part start) (cel-index-of text part start))
(define-cel-function "lastIndexOf" (:string :string) :int (text part) (cel-last-index-of text part (length text)))
(define-cel-function "lastIndexOf" (:string :string :int) :int (text part end) (cel-last-index-of text part end))
(define-cel-function "substring" (:string :int) #'cel-string-result-size (text start)
  (unless (<= 0 start (length text)) (cel-fail "index out of range: ~D" start))
  (subseq text start))
(define-cel-function "substring" (:string :int :int) #'cel-string-result-size (text start end)
  (unless (<= 0 start end (length text)) (cel-fail "invalid substring range. start: ~D, end: ~D" start end))
  (subseq text start end))
(define-cel-function "join" (:list) :string (items)
  (unless (every #'stringp items) (cel-fail "no such overload: join"))
  (format nil "~{~A~}" (coerce items 'list)))
(define-cel-function "join" (:list :string) :string (items separator)
  (unless (every #'stringp items) (cel-fail "no such overload: join"))
  (with-output-to-string (out)
    (loop for item across items for index from 0
          do (when (plusp index) (write-string separator out))
             (write-string item out))))
(define-cel-function "strings.quote" (nil :string) :string (text)
  (with-output-to-string (out)
    (write-char #\" out)
    (loop for character across text
          do (case character
               (#\" (write-string "\\\"" out))
               (#\\ (write-string "\\\\" out))
               (#\Newline (write-string "\\n" out))
               (#\Tab (write-string "\\t" out))
               (#\Return (write-string "\\r" out))
               (t (write-char character out))))
    (write-char #\" out)))

(defun cel-format-value (verb value precision)
  "Render VALUE for one format verb."
  (flet ((number-value () (or (cel-numeric-value value) (cel-fail "format verb %~A requires a number" verb))))
    (case verb
      (#\s (cond ((stringp value) value)
                 ((cel-numeric-value value) (cel-format-plain value))
                 ((cel-bool-p value) (if value "true" "false"))
                 ((eq value 'null) "null")
                 ((cel-bytes-p value) (trivial-utf-8:utf-8-bytes-to-string value))
                 ((cel-timestamp-p value) (cel-format-timestamp (cel-timestamp-nanos value)))
                 ((cel-duration-p value) (cel-format-duration (cel-duration-nanos value)))
                 (t (com.inuoe.jzon:stringify value))))
      (#\d (let ((number (number-value)))
             (unless (integerp number) (cel-fail "decimal clause can only be used on integers"))
             (format nil "~D" number)))
      (#\f (format nil "~,vF" (or precision 6) (coerce (number-value) 'double-float)))
      (#\e (let ((text (format nil "~,v,2E" (or precision 6) (coerce (number-value) 'double-float)))) text))
      (#\b (format nil "~B" (number-value)))
      (#\o (format nil "~O" (number-value)))
      (#\x (if (stringp value)
               (format nil "~(~{~2,'0X~}~)" (coerce (trivial-utf-8:string-to-utf-8-bytes value) 'list))
               (format nil "~(~X~)" (number-value))))
      (#\X (if (stringp value)
               (format nil "~{~2,'0X~}" (coerce (trivial-utf-8:string-to-utf-8-bytes value) 'list))
               (format nil "~:@(~X~)" (number-value))))
      (t (cel-fail "unrecognized formatting clause \"~A\"" verb)))))

(defun cel-format-plain (value)
  "Print a number as %s does."
  (cond ((integerp value) (format nil "~D" value))
        ((cel-uint-p value) (format nil "~D" (cel-uint-value value)))
        (t (com.inuoe.jzon:stringify value))))

(define-cel-function "format" (:string :list) :string (template arguments)
  (with-output-to-string (out)
    (let ((position 0) (used 0) (size (length template)))
      (loop while (< position size)
            do (let ((character (char template position)))
                 (incf position)
                 (if (char/= character #\%)
                     (write-char character out)
                     (progn
                       (when (>= position size) (cel-fail "unexpected end of format string"))
                       (if (char= #\% (char template position))
                           (progn (write-char #\% out) (incf position))
                           (let ((precision nil))
                             (when (char= #\. (char template position))
                               (incf position)
                               (let ((end (or (position-if-not #'digit-char-p template :start position) size)))
                                 (setf precision (parse-integer template :start position :end end) position end)))
                             (when (>= position size) (cel-fail "unexpected end of format string"))
                             (unless (< used (length arguments))
                               (cel-fail "index ~D out of range" used))
                             (write-string (cel-format-value (char template position) (aref arguments used) precision) out)
                             (incf position)
                             (incf used))))))))))

;;; Regular expressions

(defun cel-regex (pattern)
  "Compile PATTERN for a runtime call, failing the call when it is outside RE2."
  (handler-case (cl-re2:re2-compile pattern)
    (cl-re2:re2-syntax-error (condition) (cel-fail "~A" (cl-re2:re2-syntax-error-message condition)))))

(defun cel-find-all (text pattern limit)
  "Return up to LIMIT matches of PATTERN in TEXT, a negative LIMIT meaning all."
  (let ((program (cel-regex pattern)) (start 0) (matches nil) (count 0))
    (loop while (and (<= start (length text)) (or (minusp limit) (< count limit)))
          do (multiple-value-bind (from to) (cl-re2:re2-search program text :start start)
               (unless from (return))
               (push (subseq text from to) matches)
               (incf count)
               (setf start (if (= from to) (1+ to) to))))
    (coerce (nreverse matches) 'vector)))

(define-cel-function "matches" (:string :string) :bool (text pattern) (cl-re2:re2-match-p (cel-regex pattern) text))
(define-cel-function "matches" (nil :string :string) :bool (text pattern) (cl-re2:re2-match-p (cel-regex pattern) text))
(define-cel-function "find" (:string :string) :string (text pattern)
  (multiple-value-bind (from to) (cl-re2:re2-search (cel-regex pattern) text)
    (if from (subseq text from to) "")))
(define-cel-function "findAll" (:string :string) '(:list (:string nil) nil) (text pattern) (cel-find-all text pattern -1))
(define-cel-function "findAll" (:string :string :int) '(:list (:string nil) nil) (text pattern limit)
  (cel-find-all text pattern limit))

;;; Lists

(defun cel-element-result (receiver arguments)
  "Return a list receiver's element type."
  (declare (ignore arguments))
  (cel-list-element receiver))

(defun cel-list-result (receiver arguments)
  "Keep a list receiver's type."
  (declare (ignore arguments))
  (or receiver :list))

(defun cel-require-comparable-items (items name)
  "Refuse a list whose elements have no common ordering."
  (loop for index from 1 below (length items)
        do (cel-compare-values (aref items (1- index)) (aref items index) name)))

(defun cel-extreme (items name wanted)
  "Return the extreme element of ITEMS, where WANTED is -1 for smallest and 1 for largest."
  (when (zerop (length items)) (cel-fail "~A called on empty list" name))
  (reduce (lambda (best item) (if (= wanted (cel-compare-values item best name)) item best)) items))

(define-cel-function "isSorted" (:list) :bool (items)
  (loop for index from 1 below (length items)
        always (<= (cel-compare-values (aref items (1- index)) (aref items index) "isSorted") 0)))
(define-cel-function "sum" (:list) #'cel-element-result (items)
  (cond ((zerop (length items)) 0)
        (t (reduce (lambda (left right) (cel-arithmetic "_+_" left right)) items))))
(define-cel-function "min" (:list) #'cel-element-result (items) (cel-extreme items "min" -1))
(define-cel-function "max" (:list) #'cel-element-result (items) (cel-extreme items "max" 1))
(define-cel-function "indexOf" (:list :any) :int (items value)
  (or (position value items :test #'cel-equal) -1))
(define-cel-function "lastIndexOf" (:list :any) :int (items value)
  (or (position value items :test #'cel-equal :from-end t) -1))
(define-cel-function "slice" (:list :int :int) #'cel-list-result (items start end)
  (unless (<= 0 start end (length items))
    (cel-fail "invalid slice range. start: ~D, end: ~D" start end))
  (subseq items start end))
(define-cel-function "distinct" (:list) #'cel-list-result (items)
  (let ((seen nil))
    (coerce (loop for item across items
                  unless (member item seen :test #'cel-equal)
                    collect (progn (push item seen) item))
            'vector)))
(define-cel-function "reverse" (:list) #'cel-list-result (items) (reverse items))
(define-cel-function "sort" (:list) #'cel-list-result (items)
  (cel-require-comparable-items items "sort")
  (stable-sort (copy-seq items)
               (lambda (left right) (minusp (cel-compare-values left right "sort")))))
(defun cel-flatten (items depth)
  "Flatten nested lists in ITEMS by DEPTH levels."
  (coerce (loop for item across items
                append (if (and (plusp depth) (cel-list-p item))
                           (coerce (cel-flatten item (1- depth)) 'list)
                           (list item)))
          'vector))
(define-cel-function "flatten" (:list) :list (items) (cel-flatten items 1))
(define-cel-function "flatten" (:list :int) :list (items depth)
  (when (minusp depth) (cel-fail "level must be non-negative"))
  (cel-flatten items depth))
(define-cel-function "lists.range" (nil :int) '(:list :int nil) (count)
  (coerce (loop for index from 0 below count collect index) 'vector))
(define-cel-function "first" (:list) (lambda (receiver arguments)
                                       (declare (ignore arguments))
                                       (list :optional (cel-list-element receiver)))
    (items)
  (if (plusp (length items)) (cel-some (aref items 0)) (make-cel-optional)))
(define-cel-function "last" (:list) (lambda (receiver arguments)
                                      (declare (ignore arguments))
                                      (list :optional (cel-list-element receiver)))
    (items)
  (if (plusp (length items)) (cel-some (aref items (1- (length items)))) (make-cel-optional)))

;;; Sets

(define-cel-function "sets.contains" (nil :list :list) :bool (items wanted)
  (every (lambda (item) (find item items :test #'cel-equal)) wanted))
(define-cel-function "sets.equivalent" (nil :list :list) :bool (left right)
  (and (every (lambda (item) (find item right :test #'cel-equal)) left)
       (every (lambda (item) (find item left :test #'cel-equal)) right)))
(define-cel-function "sets.intersects" (nil :list :list) :bool (left right)
  (and (some (lambda (item) (find item right :test #'cel-equal)) left) t))
;;; Optionals

(defun cel-optional-result (receiver arguments)
  "Unwrap an optional receiver's type."
  (declare (ignore arguments))
  (if (consp receiver) (second receiver) :dyn))

(define-cel-function "optional.of" (nil :any) (lambda (receiver arguments)
                                                (declare (ignore receiver))
                                                (list :optional (first arguments)))
    (value)
  (cel-some value))
(define-cel-function "optional.none" (nil) '(:optional :dyn) () (make-cel-optional))
(define-cel-function "optional.ofNonZeroValue" (nil :any) (lambda (receiver arguments)
                                                            (declare (ignore receiver))
                                                            (list :optional (first arguments)))
    (value)
  (if (or (member value '(nil 0 "" null) :test #'equal) (and (floatp value) (zerop value))
          (and (or (cel-list-p value) (cel-bytes-p value)) (zerop (length value)))
          (and (hash-table-p value) (zerop (hash-table-count value))))
      (make-cel-optional)
      (cel-some value)))
(define-cel-function "hasValue" (:optional) :bool (optional) (and (cel-optional-present optional) t))
(define-cel-function "value" (:optional) #'cel-optional-result (optional)
  (unless (cel-optional-present optional) (cel-fail "optional.none() dereference"))
  (cel-optional-value optional))
(define-cel-function "orValue" (:optional :any) #'cel-optional-result (optional fallback)
  (if (cel-optional-present optional) (cel-optional-value optional) fallback))
(define-cel-function "or" (:optional :optional) #'cel-list-result (optional fallback)
  (if (cel-optional-present optional) optional fallback))

;;; Quantities

(defun cel-quantity-parse (text)
  "Parse TEXT as a decimal quantity, or return NIL."
  (handler-case (parse-decimal-quantity text)
    (error () nil)))

(defun cel-quantity-of (value)
  "Return the underlying quantity of a CEL quantity object."
  (cel-opaque-value value))

(defun cel-quantity-rational (quantity)
  "Return QUANTITY's exact amount."
  (* (decimal-quantity-coefficient quantity) (expt 10 (decimal-quantity-scale quantity))))

(defun cel-make-quantity (amount)
  "Build a quantity object from an exact AMOUNT with at most nanosecond precision."
  (let* ((scaled (ceiling (* amount 1000000000))))
    (cel-opaque :quantity
                (normalize-decimal-quantity
                 (make-decimal-quantity :coefficient scaled :scale -9)))))

(defun cel-quantity-int (quantity)
  "Return QUANTITY as an int64 when it is a whole number in range."
  (let ((amount (cel-quantity-rational quantity)))
    (unless (and (integerp amount) (typep amount '(signed-byte 64)))
      (cel-fail "cannot convert value to integer"))
    amount))

(let ((quantity '(:opaque :quantity)))
  (setf (gethash "quantity" *cel-functions*)
        (list (make-cel-overload
               :receiver nil :parameters '(:string) :result (cel-opaque-type :quantity)
               :function (lambda (text)
                           (cel-opaque :quantity (or (cel-quantity-parse text) (cel-fail "quantities must match the regular expression")))))))
  (setf (gethash "isQuantity" *cel-functions*)
        (list (make-cel-overload :receiver nil :parameters '(:string) :result :bool
                                 :function (lambda (text) (and (cel-quantity-parse text) t)))))
  (flet ((method-on (name parameters result function)
           (setf (gethash name *cel-functions*)
                 (append (gethash name *cel-functions*)
                         (list (make-cel-overload :receiver quantity :parameters parameters
                                                  :result result :function function))))))
    (method-on "sign" nil :int
               (lambda (value) (signum (decimal-quantity-coefficient (cel-quantity-of value)))))
    (method-on "isInteger" nil :bool
               (lambda (value) (integerp (cel-quantity-rational (cel-quantity-of value)))))
    (method-on "asInteger" nil :int (lambda (value) (cel-quantity-int (cel-quantity-of value))))
    (method-on "asApproximateFloat" nil :double
               (lambda (value) (coerce (cel-quantity-rational (cel-quantity-of value)) 'double-float)))
    (dolist (parameters (list (list quantity) '(:int)))
      (let ((operand (lambda (value)
                       (if (integerp value) value (cel-quantity-rational (cel-quantity-of value))))))
        (method-on "add" parameters (cel-opaque-type :quantity)
                   (lambda (left right)
                     (cel-make-quantity (+ (cel-quantity-rational (cel-quantity-of left)) (funcall operand right)))))
        (method-on "sub" parameters (cel-opaque-type :quantity)
                   (lambda (left right)
                     (cel-make-quantity (- (cel-quantity-rational (cel-quantity-of left)) (funcall operand right)))))))
    (flet ((order (left right)
             (decimal-quantity-compare (cel-quantity-of left) (cel-quantity-of right))))
      (method-on "compareTo" (list quantity) :int #'order)
      (method-on "isGreaterThan" (list quantity) :bool (lambda (left right) (plusp (order left right))))
      (method-on "isLessThan" (list quantity) :bool (lambda (left right) (minusp (order left right)))))))

;;; URLs

(defun cel-parse-url (text)
  "Parse an absolute URL into a list of scheme, host, escaped path and query, or NIL."
  (cl-ppcre:register-groups-bind (scheme authority path query)
      ("^([A-Za-z][A-Za-z0-9+.-]*)://([^/?#]*)([^?#]*)(?:\\?([^#]*))?$" text)
    (unless (or (find #\@ authority) (find #\Space text))
      (list scheme authority path (or query "")))))

(defun cel-url-decode (text)
  "Decode percent escapes and plus signs in a URL query component."
  (with-output-to-string (output)
    (loop for position from 0 below (length text)
          for character = (char text position)
          do (cond
               ((char= character #\+) (write-char #\Space output))
               ((char= character #\%)
                (when (> (+ position 2) (1- (length text)))
                  (cel-fail "incomplete URL escape"))
                (let ((high (digit-char-p (char text (1+ position)) 16))
                      (low (digit-char-p (char text (+ position 2)) 16)))
                  (unless (and high low) (cel-fail "invalid URL escape"))
                  (write-char (code-char (+ (* high 16) low)) output)
                  (incf position 2)))
               (t (write-char character output))))))

(defun cel-url-query (query)
  "Decode a query string into a map from name to a list of values."
  (let ((result (make-hash-table :test #'equal)))
    (dolist (pair (uiop:split-string query :separator '(#\&)) result)
      (when (plusp (length pair))
        (let* ((equals (position #\= pair))
               (key (cel-url-decode (subseq pair 0 equals)))
               (value (if equals (cel-url-decode (subseq pair (1+ equals))) "")))
          (setf (gethash key result) (concatenate 'vector (gethash key result #()) (vector value))))))))

(defun cel-url-host-parts (authority)
  "Split AUTHORITY into hostname and port strings."
  (if (and (plusp (length authority)) (char= #\[ (char authority 0)))
      (let ((close (position #\] authority)))
        (values (subseq authority 1 close)
                (if (and close (< (1+ close) (length authority))) (subseq authority (+ close 2)) "")))
      (let ((colon (position #\: authority)))
        (if colon
            (values (subseq authority 0 colon) (subseq authority (1+ colon)))
            (values authority "")))))

(define-cel-function "isURL" (nil :string) :bool (text) (and (cel-parse-url text) t))
(define-cel-function "url" (nil :string) (cel-opaque-type :url) (text)
  (cel-opaque :url (or (cel-parse-url text) (cel-fail "URL is invalid: ~A" text))))
(define-cel-function "getScheme" ((:opaque :url)) :string (url) (first (cel-opaque-value url)))
(define-cel-function "getHost" ((:opaque :url)) :string (url) (second (cel-opaque-value url)))
(define-cel-function "getHostname" ((:opaque :url)) :string (url)
  (values (cel-url-host-parts (second (cel-opaque-value url)))))
(define-cel-function "getPort" ((:opaque :url)) :string (url)
  (nth-value 1 (cel-url-host-parts (second (cel-opaque-value url)))))
(define-cel-function "getEscapedPath" ((:opaque :url)) :string (url) (third (cel-opaque-value url)))
(define-cel-function "getQuery" ((:opaque :url)) '(:map :string (:list :string nil) nil) (url)
  (cel-url-query (fourth (cel-opaque-value url))))

;;; IP addresses and CIDRs: (family . integer) and ((family . integer) . prefix).

(defun cel-parse-ipv4 (text)
  "Parse a dotted IPv4 address into an integer, or NIL; leading zeros are refused as upstream does."
  (let ((parts (uiop:split-string text :separator '(#\.))))
    (when (and (= 4 (length parts))
               (every (lambda (part)
                        (and (<= 1 (length part) 3) (every #'digit-char-p part)
                             (or (= 1 (length part)) (char/= #\0 (char part 0)))
                             (<= (parse-integer part) 255)))
                      parts))
      (reduce (lambda (total part) (+ (* total 256) (parse-integer part))) parts :initial-value 0))))

(defun cel-parse-ipv6 (text)
  "Parse an IPv6 address into an integer, or NIL. A zone or an IPv4-mapped form is refused, as upstream's ip() does."
  (when (and (find #\: text) (not (find #\% text)) (not (find #\. text)))
    (handler-case
        (let ((bytes (0conf:parse-ipv6 text)))
          (reduce (lambda (total octet) (+ (* total 256) octet)) bytes :initial-value 0))
      (error () nil))))

(defun cel-parse-ip (text)
  "Parse TEXT as an IP address into (family . integer), or NIL."
  (let ((v4 (cel-parse-ipv4 text)))
    (if v4
        (cons 4 v4)
        (let ((v6 (cel-parse-ipv6 text)))
          (and v6 (cons 6 v6))))))

(defun cel-format-ip (address)
  "Print (family . integer) in canonical form."
  (destructuring-bind (family . value) address
    (if (= family 4)
        (format nil "~D.~D.~D.~D" (ldb (byte 8 24) value) (ldb (byte 8 16) value) (ldb (byte 8 8) value) (ldb (byte 8 0) value))
        (let* ((groups (loop for shift from 112 downto 0 by 16 collect (ldb (byte 16 shift) value)))
               (best-start nil) (best-length 0))
          ;; RFC 5952: compress the longest run of two or more zero groups, the first when tied.
          (loop with index = 0
                while (< index 8)
                do (if (zerop (nth index groups))
                       (let ((end (or (position-if-not #'zerop groups :start index) 8)))
                         (when (and (>= (- end index) 2) (> (- end index) best-length))
                           (setf best-start index best-length (- end index)))
                         (setf index end))
                       (incf index)))
          (flet ((part (from to)
                   (format nil "~(~{~X~^:~}~)" (subseq groups from to))))
            (if best-start
                (format nil "~A::~A" (part 0 best-start) (part (+ best-start best-length) 8))
                (part 0 8)))))))

(defun cel-parse-cidr (text)
  "Parse TEXT as a CIDR into (address . prefix), or NIL."
  (let ((slash (position #\/ text)))
    (when slash
      (let* ((address (cel-parse-ip (subseq text 0 slash)))
             (digits (subseq text (1+ slash)))
             (prefix (and (plusp (length digits)) (every #'digit-char-p digits)
                          (or (= 1 (length digits)) (char/= #\0 (char digits 0)))
                          (parse-integer digits))))
        (when (and address prefix (<= prefix (if (= 4 (car address)) 32 128)))
          (cons address prefix))))))

(defun cel-ip-bits (address)
  "Return the width of ADDRESS in bits."
  (if (= 4 (car address)) 32 128))

(defun cel-masked-address (address prefix)
  "Clear the host bits of ADDRESS beyond PREFIX."
  (let ((bits (cel-ip-bits address)))
    (cons (car address) (ash (ash (cdr address) (- prefix bits)) (- bits prefix)))))

(defun cel-ip-in-range-p (address low high)
  "Test whether ADDRESS's value is between LOW and HIGH."
  (<= low (cdr address) high))

(define-cel-function "isIP" (nil :string) :bool (text) (and (cel-parse-ip text) t))
(define-cel-function "ip" (nil :string) (cel-opaque-type :ip) (text)
  (cel-opaque :ip (or (cel-parse-ip text) (cel-fail "IP Address ~S parse error during conversion from string" text))))
(define-cel-function "string" (nil (:opaque :ip)) :string (ip) (cel-format-ip (cel-opaque-value ip)))
(define-cel-function "ip.isCanonical" (nil :string) :bool (text)
  (let ((address (or (cel-parse-ip text)
                     (cel-fail "IP Address ~S parse error during conversion from string" text))))
    (equal text (cel-format-ip address))))
(define-cel-function "family" ((:opaque :ip)) :int (ip) (car (cel-opaque-value ip)))
(define-cel-function "isUnspecified" ((:opaque :ip)) :bool (ip) (zerop (cdr (cel-opaque-value ip))))
(define-cel-function "isLoopback" ((:opaque :ip)) :bool (ip)
  (let ((address (cel-opaque-value ip)))
    (if (= 4 (car address))
        (= 127 (ldb (byte 8 24) (cdr address)))
        (= 1 (cdr address)))))
(define-cel-function "isLinkLocalMulticast" ((:opaque :ip)) :bool (ip)
  (let ((address (cel-opaque-value ip)))
    (if (= 4 (car address))
        (= #xE00000 (ash (cdr address) -8))
        (= #xFF02 (logand #xFF0F (ash (cdr address) -112))))))
(define-cel-function "isLinkLocalUnicast" ((:opaque :ip)) :bool (ip)
  (let ((address (cel-opaque-value ip)))
    (if (= 4 (car address))
        (= #xA9FE (ash (cdr address) -16))
        (= #xFE8 (ash (cdr address) -116)))))
(define-cel-function "isGlobalUnicast" ((:opaque :ip)) :bool (ip)
  (let* ((address (cel-opaque-value ip)) (value (cdr address)))
    (if (= 4 (car address))
        (not (or (zerop value) (= #xFFFFFFFF value)
                 (= 127 (ldb (byte 8 24) value))
                 (= 14 (ldb (byte 4 28) value))
                 (= #xA9FE (ash value -16))))
        (not (or (zerop value) (= 1 value)
                 (= #xFF (ash value -120))
                 (= #xFE8 (ash value -116)))))))
(define-cel-function "isCIDR" (nil :string) :bool (text) (and (cel-parse-cidr text) t))
(define-cel-function "cidr" (nil :string) (cel-opaque-type :cidr) (text)
  (cel-opaque :cidr (or (cel-parse-cidr text) (cel-fail "network address parse error during conversion from string"))))
(define-cel-function "string" (nil (:opaque :cidr)) :string (cidr)
  (destructuring-bind (address . prefix) (cel-opaque-value cidr)
    (format nil "~A/~D" (cel-format-ip address) prefix)))
(define-cel-function "ip" ((:opaque :cidr)) (cel-opaque-type :ip) (cidr)
  (cel-opaque :ip (car (cel-opaque-value cidr))))
(define-cel-function "prefixLength" ((:opaque :cidr)) :int (cidr) (cdr (cel-opaque-value cidr)))
(define-cel-function "masked" ((:opaque :cidr)) (cel-opaque-type :cidr) (cidr)
  (destructuring-bind (address . prefix) (cel-opaque-value cidr)
    (cel-opaque :cidr (cons (cel-masked-address address prefix) prefix))))
(flet ((contains-ip (cidr address)
         (destructuring-bind (network . prefix) (cel-opaque-value cidr)
           (and (= (car network) (car address))
                (equal (cel-masked-address network prefix) (cel-masked-address address prefix))))))
  (setf (gethash "containsIP" *cel-functions*)
        (list (make-cel-overload :receiver '(:opaque :cidr) :parameters '((:opaque :ip)) :result :bool
                                 :function (lambda (cidr ip) (contains-ip cidr (cel-opaque-value ip))))
              (make-cel-overload :receiver '(:opaque :cidr) :parameters '(:string) :result :bool
                                 :function (lambda (cidr text)
                                             (contains-ip cidr (or (cel-parse-ip text) (cel-fail "IP Address ~S parse error" text)))))))
  (flet ((contains-cidr (cidr other)
           (and (>= (cdr other) (cdr (cel-opaque-value cidr)))
                (contains-ip cidr (car other)))))
    (setf (gethash "containsCIDR" *cel-functions*)
          (list (make-cel-overload :receiver '(:opaque :cidr) :parameters '((:opaque :cidr)) :result :bool
                                   :function (lambda (cidr other) (contains-cidr cidr (cel-opaque-value other))))
                (make-cel-overload :receiver '(:opaque :cidr) :parameters '(:string) :result :bool
                                   :function (lambda (cidr text)
                                               (contains-cidr cidr (or (cel-parse-cidr text) (cel-fail "network address parse error")))))))))

;;; Semantic versions: (major minor patch prerelease).

(defun cel-parse-semver (text normalize)
  "Parse TEXT as a semantic version, tolerating v prefixes and short forms when NORMALIZE."
  (let ((text (if (and normalize (plusp (length text)) (char-equal #\v (char text 0))) (subseq text 1) text)))
    (cl-ppcre:register-groups-bind (major minor patch prerelease)
        ((if normalize
             "^(0|[1-9][0-9]*|0[0-9]+)(?:\\.([0-9]+))?(?:\\.([0-9]+))?(?:-([0-9A-Za-z.-]+))?(?:\\+[0-9A-Za-z.-]+)?$"
             "^(0|[1-9][0-9]*)\\.(0|[1-9][0-9]*)\\.(0|[1-9][0-9]*)(?:-([0-9A-Za-z.-]+))?(?:\\+[0-9A-Za-z.-]+)?$")
         text)
      (list (parse-integer major) (if minor (parse-integer minor) 0) (if patch (parse-integer patch) 0) prerelease))))

(defun cel-semver-compare (left right)
  "Order two parsed versions as Semantic Versioning does."
  (loop for a in left for b in right repeat 3
        do (cond ((< a b) (return-from cel-semver-compare -1))
                 ((> a b) (return-from cel-semver-compare 1))))
  (let ((a (fourth left)) (b (fourth right)))
    (cond
      ((and (null a) (null b)) 0)
      ((null a) 1)
      ((null b) -1)
      (t
       (let ((as (uiop:split-string a :separator '(#\.))) (bs (uiop:split-string b :separator '(#\.))))
         (loop
           (when (and (null as) (null bs)) (return 0))
           (when (null as) (return -1))
           (when (null bs) (return 1))
           (let* ((x (pop as)) (y (pop bs))
                  (x-number (and (every #'digit-char-p x) (parse-integer x)))
                  (y-number (and (every #'digit-char-p y) (parse-integer y))))
             (cond ((and x-number y-number)
                    (cond ((< x-number y-number) (return -1)) ((> x-number y-number) (return 1))))
                   (x-number (return -1))
                   (y-number (return 1))
                   ((string< x y) (return -1))
                   ((string> x y) (return 1))))))))))

(define-cel-function "isSemver" (nil :string) :bool (text) (and (cel-parse-semver text nil) t))
(define-cel-function "isSemver" (nil :string :bool) :bool (text normalize) (and (cel-parse-semver text normalize) t))
(define-cel-function "semver" (nil :string) (cel-opaque-type :semver) (text)
  (cel-opaque :semver (or (cel-parse-semver text nil) (cel-fail "Unable to parse semver"))))
(define-cel-function "semver" (nil :string :bool) (cel-opaque-type :semver) (text normalize)
  (cel-opaque :semver (or (cel-parse-semver text normalize) (cel-fail "Unable to parse semver"))))
(define-cel-function "major" ((:opaque :semver)) :int (version) (first (cel-opaque-value version)))
(define-cel-function "minor" ((:opaque :semver)) :int (version) (second (cel-opaque-value version)))
(define-cel-function "patch" ((:opaque :semver)) :int (version) (third (cel-opaque-value version)))
(define-cel-function "compareTo" ((:opaque :semver) (:opaque :semver)) :int (left right)
  (cel-semver-compare (cel-opaque-value left) (cel-opaque-value right)))
(define-cel-function "isGreaterThan" ((:opaque :semver) (:opaque :semver)) :bool (left right)
  (plusp (cel-semver-compare (cel-opaque-value left) (cel-opaque-value right))))
(define-cel-function "isLessThan" ((:opaque :semver) (:opaque :semver)) :bool (left right)
  (minusp (cel-semver-compare (cel-opaque-value left) (cel-opaque-value right))))

;;; Common string formats

(defparameter +cel-named-formats+
  '("dns1123Label" "dns1123Subdomain" "dns1035Label" "qualifiedName"
    "dns1123LabelPrefix" "dns1123SubdomainPrefix" "dns1035LabelPrefix"
    "labelValue" "uri" "uuid" "byte" "date" "datetime")
  "String formats exposed by format.named and format.x(), including the
Kubernetes name/label validators.")

(defun cel-qualified-name-valid-p (text)
  "Return true when TEXT is a Kubernetes qualified name: an optional DNS-1123
subdomain prefix, a '/', and a name part of alphanumerics, '-', '_' or '.'."
  (flet ((name-part-p (part)
           (and (<= 1 (length part) 63)
                (cl-ppcre:scan "^[A-Za-z0-9]([-A-Za-z0-9_.]*[A-Za-z0-9])?$" part) t)))
    (let ((slash (position #\/ text)))
      (if slash
          (and (name-part-p (subseq text (1+ slash)))
               (cel-format-valid-p "dns1123Subdomain" (subseq text 0 slash)))
          (name-part-p text)))))

(defun cel-format-valid-p (format text)
  "Return true when TEXT satisfies FORMAT."
  (cond
    ((equal format "dns1123Label")
     (and (<= 1 (length text) 63)
          (cl-ppcre:scan "^[a-z0-9]([-a-z0-9]*[a-z0-9])?$" text) t))
    ((equal format "dns1123Subdomain")
     (and (<= 1 (length text) 253)
          (cl-ppcre:scan "^[a-z0-9]([-a-z0-9]*[a-z0-9])?(\\.[a-z0-9]([-a-z0-9]*[a-z0-9])?)*$" text) t))
    ((equal format "dns1035Label")
     (and (<= 1 (length text) 63)
          (cl-ppcre:scan "^[a-z]([-a-z0-9]*[a-z0-9])?$" text) t))
    ((equal format "qualifiedName")
     (cel-qualified-name-valid-p text))
    ((equal format "dns1123LabelPrefix")
     (cel-format-valid-p "dns1123Label" (string-right-trim "-" text)))
    ((equal format "dns1123SubdomainPrefix")
     (cel-format-valid-p "dns1123Subdomain" (string-right-trim "-" text)))
    ((equal format "dns1035LabelPrefix")
     (cel-format-valid-p "dns1035Label" (string-right-trim "-" text)))
    ((equal format "labelValue")
     (and (<= (length text) 63)
          (or (zerop (length text))
              (and (cl-ppcre:scan "^[A-Za-z0-9]([-A-Za-z0-9_.]*[A-Za-z0-9])?$" text) t))))
    ((equal format "uri")
     (and (plusp (length text)) (not (find #\Space text))
          (or (char= #\/ (char text 0))
              (cl-ppcre:scan "^[A-Za-z][A-Za-z0-9+.-]*:" text))))
    ((equal format "uuid")
     (and (cl-ppcre:scan
           "(?i)^[0-9a-f]{8}-?[0-9a-f]{4}-?[0-9a-f]{4}-?[0-9a-f]{4}-?[0-9a-f]{12}$"
           text)
          t))
    ((equal format "byte")
     (and (cl-ppcre:scan
           "^(?:[A-Za-z0-9+/]{4})*(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?$"
           text)
          t))
    ((equal format "date")
     (and (cl-ppcre:scan "^[0-9]{4}-[0-9]{2}-[0-9]{2}$" text)
          (cel-parse-rfc3339 (concatenate 'string text "T00:00:00Z"))
          t))
    ((equal format "datetime")
     (and (cel-parse-rfc3339 text) t))
    (t nil)))

(dolist (format +cel-named-formats+)
  (setf (gethash (concatenate 'string "format." format) *cel-functions*)
        (list (make-cel-overload
               :receiver nil :parameters nil :result (cel-opaque-type :format)
               :function (lambda () (cel-opaque :format format))))))

(define-cel-function "format.named" (nil :string)
    (list :optional (cel-opaque-type :format)) (name)
  (if (member name +cel-named-formats+ :test #'equal)
      (cel-some (cel-opaque :format name))
      (make-cel-optional)))

(define-cel-function "validate" ((:opaque :format) :string)
    '(:optional (:list :string nil)) (format text)
  (if (cel-format-valid-p (cel-opaque-value format) text)
      (make-cel-optional)
      (cel-some (vector (format nil "invalid ~A" (cel-opaque-value format))))))

