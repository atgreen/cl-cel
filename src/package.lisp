;;;; SPDX-FileCopyrightText: 2026 Anthony Green <green@moxielogic.com>
;;;; SPDX-License-Identifier: MIT

(defpackage #:cl-cel
  (:use #:cl)
  (:export #:compile-cel-expression #:compile-cel-condition
           #:evaluate-cel-value #:evaluate-cel-condition
           #:with-cel-budget #:with-cel-environment
           #:cel-compile-error #:cel-evaluation-error
           #:cel-cost-exceeded #:cel-budget-exhausted #:cel-error-message))
