;;;; SPDX-FileCopyrightText: 2026 Anthony Green <green@moxielogic.com>
;;;; SPDX-License-Identifier: MIT

(in-package #:cl-cel/tests)
(in-suite cl-cel)

(defun evaluate-condition (expression &rest bindings)
  (with-cel-environment (:variables (mapcar #'car bindings))
    (evaluate-cel-condition (compile-cel-condition expression) bindings)))

(test evaluates-core-language-and-macros
  (let ((object (com.inuoe.jzon:parse
                 "{\"metadata\":{\"name\":\"demo\",\"labels\":{\"a\":\"b\"}},\"items\":[1,2,3]}")))
    (is-true (evaluate-condition "object.metadata.name == 'demo'" (cons "object" object)))
    (is-true (evaluate-condition "has(object.metadata.labels)" (cons "object" object)))
    (is-true (evaluate-condition "object.items.all(x, x > 0)" (cons "object" object)))
    (is-true (evaluate-condition "object.items.filter(x, x > 1).size() == 2" (cons "object" object)))
    (is-true (evaluate-condition "object.items.map(x, x * 2)[2] == 6" (cons "object" object)))))

(test implements-cel-error-absorbing-logic
  (let ((object (com.inuoe.jzon:parse "{\"metadata\":{}}")))
    (signals cel-evaluation-error
      (evaluate-condition "object.metadata.name == 'x'" (cons "object" object)))
    (is-false (evaluate-condition "object.metadata.name == 'x' && false" (cons "object" object)))
    (is-true (evaluate-condition "true || object.metadata.name == 'x'" (cons "object" object)))))

(test checks-types-and-bounds-cost
  (signals cel-compile-error (compile-cel-condition "1 + 1"))
  (signals cel-compile-error (compile-cel-condition "missing == 1"))
  (let ((cl-cel::+cel-evaluation-budget+ 100))
    (signals cel-cost-exceeded
      (evaluate-condition
       "[1,2,3,4,5].all(a, [1,2,3,4,5].all(b, [1,2,3,4,5].all(c, a+b+c>0)))"))))

(test resolves-named-time-zones
  (is-true
   (evaluate-condition
    "timestamp('2026-03-10T23:30:00Z').getHours('America/New_York') == 19"))
  (signals cel-evaluation-error
    (evaluate-condition
     "timestamp('2026-03-10T23:30:00Z').getHours('Not/A_Real_Zone') == 19")))

(test evaluates-general-purpose-library-types
  (is-true (evaluate-condition "quantity('1500m').asApproximateFloat() == 1.5"))
  (is-true (evaluate-condition "quantity('1Gi').isGreaterThan(quantity('1000M'))"))
  (is-true (evaluate-condition "url('https://example.test/a?x=hello+world').getQuery().x[0] == 'hello world'"))
  (is-true (evaluate-condition "string(ip('2001:db8::1')) == '2001:db8::1'"))
  (is-true (evaluate-condition "cidr('10.0.0.0/8').containsIP('10.2.3.4')"))
  (is-true (evaluate-condition "semver('1.2.3').isLessThan(semver('2.0.0'))"))
  (is-true (evaluate-condition "!format.uuid().validate('c56a4180-65aa-42ec-a945-5fd21dec0538').hasValue()"))
  (is-true (evaluate-condition "format.date().validate('2026-02-30').hasValue()")))

(test covers-cel-operators-and-standard-library
  (dolist (expression
           '("1 + 2 == 3"
             "7 / 2 == 3"
             "7 % 4 == 3"
             "1u < 2.0"
             "'abc' + 'def' == 'abcdef'"
             "b'abc'.size() == 3"
             "[1, 2] + [3] == [1, 2, 3]"
             "{'a': 1}.a == 1"
             "2 in [1, 2, 3]"
             "'a' in {'a': 1}"
             "true ? 1 == 1 : false"
             "optional.of(3).value() == 3"
             "!optional.none().hasValue()"
             "'Hello'.lowerAscii() == 'hello'"
             "' hello '.trim() == 'hello'"
             "'a,b,c'.split(',').size() == 3"
             "'abc123'.matches('[a-z]+[0-9]+')"
             "sets.equivalent([1,2], [2,1])"
             "lists.range(4)[3] == 3"
             "duration('1h30m').getMinutes() == 90"
             "timestamp('2026-01-02T03:04:05Z').getDayOfMonth() == 1"
             "ip('127.0.0.1').isLoopback()"
             "cidr('2001:db8::/32').containsIP('2001:db8::42')"
             "semver('1.0.0-alpha').isLessThan(semver('1.0.0'))"))
    (is-true (evaluate-condition expression))))

(test rejects-invalid-programs-and-values
  (dolist (expression '("1 + true" "unknown()" "[1, true]" "true[0]"))
    (signals cel-compile-error (compile-cel-condition expression)))
  (dolist (expression
           '("int('abc') == 0"
             "optional.none().value() == 0"
             "ip('999.1.1.1').family() == 4"
             "timestamp('not-a-time').getHours() == 0"))
    (signals cel-evaluation-error (evaluate-condition expression))))
