;;;; SPDX-FileCopyrightText: 2026 Anthony Green <green@moxielogic.com>
;;;; SPDX-License-Identifier: MIT

(in-package #:cl-cel)

(defmacro with-cel-environment ((&key variables functions) &body body)
  "Evaluate BODY with caller-owned variable declarations and optional overload table."
  `(let ((*cel-declared-variables* ,variables)
         (*cel-functions* (or ,functions *cel-functions*)))
     ,@body))
