;;;; SPDX-FileCopyrightText: 2026 Anthony Green <green@moxielogic.com>
;;;; SPDX-License-Identifier: MIT

(asdf:defsystem "cl-cel"
  :description "A cost-bounded Common Expression Language compiler and evaluator"
  :author "Anthony Green <green@moxielogic.com>"
  :license "MIT"
  :version "0.1.0"
  :depends-on ("0conf" "bordeaux-threads" "cl-re2" "cl-ppcre" "com.inuoe.jzon" "trivial-utf-8")
  :serial t
  :components ((:module "src"
                :components ((:file "package") (:file "timezone") (:file "quantity") (:file "core")
                             (:file "library") (:file "environment"))))
  :in-order-to ((test-op (test-op "cl-cel/tests"))))

(asdf:defsystem "cl-cel/tests"
  :depends-on ("cl-cel" "com.inuoe.jzon" "fiveam")
  :serial t
  :components ((:module "tests" :components ((:file "package") (:file "core-test"))))
  :perform (test-op (operation component)
             (declare (ignore operation component))
             (unless (uiop:symbol-call :fiveam :run!
                                       (find-symbol "CL-CEL" "CL-CEL/TESTS"))
               (error "cl-cel tests failed"))))
