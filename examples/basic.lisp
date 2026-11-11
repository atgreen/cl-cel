;;;; SPDX-FileCopyrightText: 2026 Anthony Green <green@moxielogic.com>
;;;; SPDX-License-Identifier: MIT

(require :asdf)
(asdf:load-system :cl-cel)

(let ((bindings
        `(("address" . "10.23.4.5")
          ("release" . "2.1.0"))))
  (cl-cel:with-cel-environment (:variables '("address" "release"))
    (let ((condition
            (cl-cel:compile-cel-condition
             "cidr('10.0.0.0/8').containsIP(address) && semver(release).major() >= 2")))
      (format t "matches: ~:[no~;yes~]~%"
              (cl-cel:evaluate-cel-condition condition bindings)))))
