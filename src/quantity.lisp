;;;; SPDX-FileCopyrightText: 2026 Anthony Green <green@moxielogic.com>
;;;; SPDX-License-Identifier: MIT

(in-package #:cl-cel)

(defstruct decimal-quantity
  "An exact decimal coefficient times ten to SCALE."
  (coefficient 0) (scale 0))

(defparameter +decimal-quantity-suffixes+
  '(("n" . -9) ("u" . -6) ("m" . -3) ("" . 0) ("k" . 3) ("M" . 6)
    ("G" . 9) ("T" . 12) ("P" . 15) ("E" . 18)))

(defparameter +binary-quantity-suffixes+
  '(("Ki" . 10) ("Mi" . 20) ("Gi" . 30) ("Ti" . 40) ("Pi" . 50) ("Ei" . 60)))

(defun normalize-decimal-quantity (quantity)
  (let ((coefficient (decimal-quantity-coefficient quantity)))
    (if (zerop coefficient)
        (setf (decimal-quantity-scale quantity) 0)
        (loop while (zerop (mod coefficient 10))
              do (setf coefficient (/ coefficient 10))
                 (incf (decimal-quantity-scale quantity))))
    (setf (decimal-quantity-coefficient quantity) coefficient)
    quantity))

(defun decimal-quantity-round (quantity scale)
  "Round magnitude away from zero to SCALE."
  (let ((result (copy-decimal-quantity quantity)))
    (when (< (decimal-quantity-scale result) scale)
      (let* ((amount (decimal-quantity-coefficient result))
             (difference (- scale (decimal-quantity-scale result)))
             (rounded (ceiling (abs amount) (expt 10 difference))))
        (setf (decimal-quantity-coefficient result) (* (signum amount) rounded)
              (decimal-quantity-scale result) scale)))
    (normalize-decimal-quantity result)))

(defun decimal-quantity-compare (left right)
  "Compare exact scaled quantities."
  (let* ((scale (min (decimal-quantity-scale left) (decimal-quantity-scale right)))
         (a (* (decimal-quantity-coefficient left)
               (expt 10 (- (decimal-quantity-scale left) scale))))
         (b (* (decimal-quantity-coefficient right)
               (expt 10 (- (decimal-quantity-scale right) scale)))))
    (cond ((< a b) -1) ((> a b) 1) (t 0))))

(defun parse-decimal-quantity (text)
  "Parse decimal, exponent, and binary-SI quantity notation."
  (multiple-value-bind (match groups)
      (cl-ppcre:scan-to-strings
       "^([+-]?(?:[0-9]+(?:\\.[0-9]*)?|\\.[0-9]+))([eE][+-]?[0-9]+|[A-Za-z]*)$"
       text)
    (unless match (error "invalid quantity ~S" text))
    (let* ((number (aref groups 0)) (suffix (aref groups 1))
           (negative (char= (char number 0) #\-))
           (unsigned (if (find (char number 0) "+-") (subseq number 1) number))
           (dot (position #\. unsigned))
           (coefficient (parse-integer (remove #\. unsigned)))
           (scale (if dot (- (1+ dot) (length unsigned)) 0))
           (decimal (assoc suffix +decimal-quantity-suffixes+ :test #'equal))
           (binary (assoc suffix +binary-quantity-suffixes+ :test #'equal)))
      (cond (decimal (incf scale (cdr decimal)))
            (binary (setf coefficient (ash coefficient (cdr binary))))
            ((and (> (length suffix) 1) (find (char suffix 0) "eE"))
             (incf scale (parse-integer suffix :start 1)))
            (t (error "invalid quantity suffix ~S" suffix)))
      (when negative (setf coefficient (- coefficient)))
      (decimal-quantity-round
       (make-decimal-quantity :coefficient coefficient :scale scale) -9))))
