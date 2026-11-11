;;;; SPDX-FileCopyrightText: 2026 Anthony Green <green@moxielogic.com>
;;;; SPDX-License-Identifier: MIT
;;;;
;;;; Purpose:
;;;; Compile and evaluate the part of CEL that general-purpose expression evaluation
;;;; use: the complete expression grammar, static result and operator type checks,
;;;; error-absorbing logic, macros and a bounded evaluation budget. Literals,
;;;; functions or variables outside this subset fail compilation with a clear
;;;; message rather than being accepted and evaluated incorrectly.

(in-package #:cl-cel)

(define-condition cel-compile-error (error)
  ((message :initarg :message :reader cel-error-message))
  (:report (lambda (condition stream) (write-string (cel-error-message condition) stream)))
  (:documentation "An expression that is malformed, mistyped or outside the supported subset."))

(define-condition cel-evaluation-error (error)
  ((message :initarg :message :reader cel-error-message))
  (:report (lambda (condition stream) (write-string (cel-error-message condition) stream)))
  (:documentation "A runtime CEL error, which logical operators may absorb."))

(define-condition cel-cost-exceeded (cel-evaluation-error) ()
  (:documentation "An expression ran out of cost budget, which nothing absorbs."))

(define-condition cel-budget-exhausted (cel-cost-exceeded) ()
  (:documentation "A group of expressions ran out of the budget they share, so none of the rest run."))

;;; Values beyond JSON's. JSON strings, numbers, booleans, null, vectors and hash
;;; tables stand for themselves; bytes are octet vectors.

(defstruct cel-uint "A CEL uint, kept apart from JSON's int." (value 0))
(defstruct cel-timestamp "Nanoseconds since the Unix epoch." (nanos 0))
(defstruct cel-duration "A signed count of nanoseconds." (nanos 0))
(defstruct cel-optional "A value that may be absent." (value nil) (present nil))
(defstruct cel-opaque "A library object such as a quantity, URL or authorizer." (kind nil) (value nil))

(defparameter +cel-maximum-expression-length+ 100000
  "Largest expression accepted, matching the upstream parser's code point limit.")

(defparameter +cel-maximum-nesting+ 64
  "Deepest accepted expression nesting, bounding parser and evaluator recursion.")

(defparameter +cel-evaluation-budget+ 1000000
  "Cost one expression may use before it fails instead of running on, upstream's PerCallLimit.")

(defvar *cel-remaining-steps* 0
  "Cost left for the expression being evaluated.")

(defvar *cel-shared-budget* nil
  "A cell holding the cost left for the group of expressions being evaluated, or NIL when
each expression has only its own per-call limit.")

(defparameter +cel-runtime-budget+ 10000000
  "Upstream's RuntimeCELCostBudget, shared by one policy binding's expressions.")

(defparameter +cel-match-conditions-budget+ 2500000
  "Upstream's RuntimeCELCostBudgetMatchConditions, shared by one object's matchConditions.")

(defmacro with-cel-budget ((amount) &body body)
  "Run BODY with the expressions it evaluates sharing AMOUNT of cost, as upstream's runtime budgets do."
  `(let ((*cel-shared-budget* (list ,amount))) ,@body))

(defvar *cel-declared-variables* '("object" "oldObject" "request" "authorizer")
  "Default variables declared by the expression environment.")

(defvar *cel-functions* (make-hash-table :test #'equal)
  "Overloads of the library functions, by name.")

(defvar *cel-authorizer-check* nil
  "Function from a plist of attributes and a verb to allowed, reason and error, for the current request.")

(defvar *cel-request-resource* nil
  "Attributes of the request's resource, which authorizer.requestResource starts from.")

(defvar *cel-construction-types* nil
  "Root type names the expression being compiled may construct, as Object or JSONPatch.")

(defun cel-syntax-error (position control &rest arguments)
  "Signal a compile error at the zero-based POSITION of the expression."
  (error 'cel-compile-error
         :message (format nil "ERROR: <input>:1:~D: Syntax error: ~?" (1+ position) control arguments)))

(defun cel-check-error (control &rest arguments)
  "Signal a type or support error found after parsing."
  (error 'cel-compile-error :message (format nil "ERROR: <input>: ~?" control arguments)))

(defun cel-fail (control &rest arguments)
  "Signal a runtime evaluation error."
  (error 'cel-evaluation-error :message (format nil "~?" control arguments)))

;;; Lexer

(defparameter +cel-reserved-words+
  '("as" "break" "const" "continue" "else" "for" "function" "if" "import" "let" "loop"
    "package" "namespace" "return" "var" "void" "while")
  "Identifiers the CEL grammar reserves.")

(defun cel-identifier-start-p (character)
  "Match the first character of a CEL identifier."
  (or (char<= #\a character #\z) (char<= #\A character #\Z) (char= character #\_)))

(defun cel-identifier-part-p (character)
  "Match a later character of a CEL identifier."
  (or (cel-identifier-start-p character) (char<= #\0 character #\9)))

(defun cel-read-escape (text position)
  "Decode the escape after a backslash at POSITION, returning a character and the next position."
  (when (>= (1+ position) (length text)) (cel-syntax-error position "unterminated escape"))
  (let* ((start (1+ position)) (character (char text start)))
    (flet ((code (digits radix from)
             (let ((end (+ from digits)))
               (unless (and (<= end (length text))
                            (every (lambda (digit) (digit-char-p digit radix)) (subseq text from end)))
                 (cel-syntax-error position "invalid escape"))
               (let ((value (parse-integer text :start from :end end :radix radix)))
                 (unless (and (< value char-code-limit) (not (<= #xD800 value #xDFFF)))
                   (cel-syntax-error position "invalid escape"))
                 (values (code-char value) end)))))
      (case character
        (#\a (values (code-char 7) (1+ start))) (#\b (values (code-char 8) (1+ start)))
        (#\f (values (code-char 12) (1+ start))) (#\n (values (code-char 10) (1+ start)))
        (#\r (values (code-char 13) (1+ start))) (#\t (values (code-char 9) (1+ start)))
        (#\v (values (code-char 11) (1+ start)))
        ((#\\ #\' #\" #\`) (values character (1+ start)))
        ((#\x #\X) (code 2 16 (1+ start)))
        (#\u (code 4 16 (1+ start)))
        (#\U (code 8 16 (1+ start)))
        (t (if (char<= #\0 character #\3)
               (code 3 8 start)
               (cel-syntax-error position "invalid escape")))))))

(defun cel-read-string (text position)
  "Read a string literal at POSITION, handling raw and triple-quoted forms."
  (let* ((raw (char-equal (char text position) #\r))
         (open (if raw (1+ position) position))
         (quote-character (char text open))
         (triple (and (< (+ open 2) (length text))
                      (char= quote-character (char text (+ open 1)) (char text (+ open 2)))))
         (cursor (+ open (if triple 3 1))))
    (values
     (with-output-to-string (out)
       (loop
         (when (>= cursor (length text)) (cel-syntax-error position "unterminated string"))
         (let ((character (char text cursor)))
           (cond
             ((and triple (char= character quote-character) (< (+ cursor 2) (length text))
                   (char= quote-character (char text (+ cursor 1)) (char text (+ cursor 2))))
              (incf cursor 3) (return))
             ((and (not triple) (char= character quote-character)) (incf cursor) (return))
             ((and (not triple) (member character '(#\Newline #\Return)))
              (cel-syntax-error position "newline in string"))
             ((and (char= character #\\) (not raw))
              (multiple-value-bind (decoded next) (cel-read-escape text cursor)
                (write-char decoded out) (setf cursor next)))
             (t (write-char character out) (incf cursor))))))
     cursor)))

(defun cel-read-number (text position)
  "Read an int, uint or double literal at POSITION."
  (let ((cursor position) (size (length text)) (double nil))
    (flet ((digits ()
             (loop while (and (< cursor size) (digit-char-p (char text cursor))) do (incf cursor))))
      (when (and (< (1+ position) size) (char= (char text position) #\0)
                 (char-equal (char text (1+ position)) #\x))
        (setf cursor (+ position 2))
        (loop while (and (< cursor size) (digit-char-p (char text cursor) 16)) do (incf cursor))
        (when (= cursor (+ position 2)) (cel-syntax-error position "invalid hexadecimal literal"))
        (let ((value (parse-integer text :start (+ position 2) :end cursor :radix 16)))
          (return-from cel-read-number
            (if (and (< cursor size) (char-equal (char text cursor) #\u))
                (values value (1+ cursor) :uint)
                (values value cursor :int)))))
      (digits)
      (when (and (< (1+ cursor) size) (char= (char text cursor) #\.) (digit-char-p (char text (1+ cursor))))
        (setf double t) (incf cursor) (digits))
      (when (and (< cursor size) (char-equal (char text cursor) #\e))
        (let ((mark cursor))
          (incf cursor)
          (when (and (< cursor size) (find (char text cursor) "+-")) (incf cursor))
          (if (and (< cursor size) (digit-char-p (char text cursor)))
              (progn (setf double t) (digits))
              (setf cursor mark))))
      (when (and (not double) (< cursor size) (char-equal (char text cursor) #\u))
        (return-from cel-read-number
          (values (parse-integer text :start position :end cursor) (1+ cursor) :uint)))
      (if double
          (let ((value (let ((*read-default-float-format* 'double-float) (*read-eval* nil))
                         (handler-case (read-from-string (subseq text position cursor))
                           (error () (cel-syntax-error position "invalid floating-point literal"))))))
            (values (coerce value 'double-float) cursor :double))
          (values (parse-integer text :start position :end cursor) cursor :int)))))

(defun cel-tokenize (text)
  "Split TEXT into a vector of (type value position) tokens."
  (let ((tokens (make-array 16 :adjustable t :fill-pointer 0)) (cursor 0) (size (length text)))
    (flet ((token (type value position) (vector-push-extend (list type value position) tokens)))
      (loop while (< cursor size)
            do (let ((character (char text cursor)))
                 (cond
                   ((member character '(#\Space #\Tab #\Newline #\Return #\Page)) (incf cursor))
                   ((and (char= character #\/) (< (1+ cursor) size) (char= (char text (1+ cursor)) #\/))
                    (setf cursor (or (position #\Newline text :start cursor) size)))
                   ((or (member character '(#\' #\"))
                        (and (char-equal character #\r) (< (1+ cursor) size)
                             (member (char text (1+ cursor)) '(#\' #\"))))
                    (multiple-value-bind (value next) (cel-read-string text cursor)
                      (token :string value cursor) (setf cursor next)))
                   ((and (char-equal character #\b) (< (1+ cursor) size)
                         (member (char text (1+ cursor)) '(#\' #\")))
                    (multiple-value-bind (value next) (cel-read-string text (1+ cursor))
                      (token :bytes (trivial-utf-8:string-to-utf-8-bytes value) cursor)
                      (setf cursor next)))
                   ((or (digit-char-p character)
                        (and (char= character #\.) (< (1+ cursor) size) (digit-char-p (char text (1+ cursor)))))
                    (if (char= character #\.)
                        (multiple-value-bind (value next type)
                            (cel-read-number (concatenate 'string "0" (subseq text cursor)) 0)
                          (token type value cursor) (incf cursor (1- next)))
                        (multiple-value-bind (value next type) (cel-read-number text cursor)
                          (token type value cursor) (setf cursor next))))
                   ((cel-identifier-start-p character)
                    (let* ((end (or (position-if-not #'cel-identifier-part-p text :start cursor) size))
                           (word (subseq text cursor end)))
                      (cond ((equal word "true") (token :bool t cursor))
                            ((equal word "false") (token :bool nil cursor))
                            ((equal word "null") (token :null 'null cursor))
                            ((equal word "in") (token :op "in" cursor))
                            (t (token :identifier word cursor)))
                      (setf cursor end)))
                   (t
                    (let ((operator (find-if (lambda (candidate)
                                               (let ((end (+ cursor (length candidate))))
                                                 (and (<= end size) (string= candidate text :start2 cursor :end2 end))))
                                             '("||" "&&" "==" "!=" "<=" ">=" "<" ">" "+" "-" "*" "/" "%" "!"
                                               "?" ":" "." "," "(" ")" "[" "]" "{" "}"))))
                      (unless operator (cel-syntax-error cursor "token recognition error at: '~A'" character))
                      (token :op operator cursor)
                      (incf cursor (length operator)))))))
      (token :eof nil size))
    tokens))

;;; Parser: nodes are lists headed by a keyword.

(defstruct (cel-parser (:constructor make-cel-parser (tokens)))
  "Mutable cursor over one expression's tokens."
  tokens (position 0) (depth 0))

(defun cel-peek (parser)
  "Return the current token."
  (aref (cel-parser-tokens parser) (cel-parser-position parser)))

(defun cel-operator-p (parser operator)
  "Test whether the current token is OPERATOR."
  (let ((token (cel-peek parser)))
    (and (eq :op (first token)) (equal operator (second token)))))

(defun cel-accept (parser operator)
  "Consume OPERATOR when it is next, returning whether it was."
  (when (cel-operator-p parser operator)
    (incf (cel-parser-position parser))
    t))

(defun cel-expect (parser operator)
  "Consume the required OPERATOR."
  (unless (cel-accept parser operator)
    (cel-syntax-error (third (cel-peek parser)) "expected '~A'" operator)))

(defun cel-next-identifier (parser)
  "Consume and return a required identifier."
  (let ((token (cel-peek parser)))
    (unless (eq :identifier (first token))
      (cel-syntax-error (third token) "expected an identifier"))
    (incf (cel-parser-position parser))
    (second token)))

(defun cel-binary-levels (parser operators next)
  "Parse a left-associative chain of OPERATORS over NEXT."
  (let ((left (funcall next parser)))
    (loop
      (let ((operator (find-if (lambda (candidate) (cel-operator-p parser candidate)) operators)))
        (unless operator (return left))
        (incf (cel-parser-position parser))
        (setf left (list :call (concatenate 'string "_" operator "_") nil (list left (funcall next parser))))))))

(defun cel-parse-expression (parser)
  "Parse Expr, tracking nesting so hostile input cannot exhaust the stack."
  (when (> (incf (cel-parser-depth parser)) +cel-maximum-nesting+)
    (cel-syntax-error (third (cel-peek parser)) "expression nesting exceeds ~D" +cel-maximum-nesting+))
  (prog1
      (let ((condition (cel-parse-or parser)))
        (if (cel-accept parser "?")
            (let ((then (cel-parse-or parser)))
              (cel-expect parser ":")
              (list :cond condition then (cel-parse-expression parser)))
            condition))
    (decf (cel-parser-depth parser))))

(defun cel-parse-or (parser)
  "Parse ConditionalOr."
  (let ((left (cel-parse-and parser)))
    (loop while (cel-accept parser "||")
          do (setf left (list :or left (cel-parse-and parser))))
    left))

(defun cel-parse-and (parser)
  "Parse ConditionalAnd."
  (let ((left (cel-parse-relation parser)))
    (loop while (cel-accept parser "&&")
          do (setf left (list :and left (cel-parse-relation parser))))
    left))

(defun cel-parse-relation (parser)
  "Parse Relation."
  (cel-binary-levels parser '("<=" ">=" "==" "!=" "<" ">" "in") #'cel-parse-addition))

(defun cel-parse-addition (parser)
  "Parse Addition."
  (cel-binary-levels parser '("+" "-") #'cel-parse-multiplication))

(defun cel-parse-multiplication (parser)
  "Parse Multiplication."
  (cel-binary-levels parser '("*" "/" "%") #'cel-parse-unary))

(defun cel-parse-unary (parser)
  "Parse Unary, nesting repeated negation."
  (cond ((cel-accept parser "!") (list :call "!_" nil (list (cel-parse-unary parser))))
        ((cel-accept parser "-") (cel-negate (cel-parse-unary parser)))
        (t (cel-parse-member parser))))

(defun cel-negate (operand)
  "Fold negated number literals so the smallest int64 stays expressible."
  (if (and (eq :lit (first operand)) (member (third operand) '(:int :double)))
      (list :lit (- (second operand)) (third operand))
      (list :call "-_" nil (list operand))))

(defun cel-parse-arguments (parser)
  "Parse a call's arguments after its opening parenthesis."
  (let ((arguments nil))
    (unless (cel-accept parser ")")
      (loop
        (push (cel-parse-expression parser) arguments)
        (unless (cel-accept parser ",")
          (cel-expect parser ")")
          (return))))
    (nreverse arguments)))

(defun cel-comprehension-variable (parser node)
  "Require a macro's iteration variable to be a simple identifier."
  (unless (eq :ident (first node))
    (cel-syntax-error (third (cel-peek parser)) "argument must be a simple name"))
  (second node))

(defun cel-expand-method (parser target name arguments)
  "Expand comprehension macros, leaving ordinary method calls alone."
  (let ((count (length arguments)))
    (cond
      ((and (equal '(:ident "cel") target) (equal name "bind"))
       (unless (= count 3) (cel-syntax-error (third (cel-peek parser)) "cel.bind requires three arguments"))
       (list :bind (cel-comprehension-variable parser (first arguments)) (second arguments) (third arguments)))
      ;; A dotted library function reads as a method call on its container's name.
      ((and (eq :ident (first target))
            (gethash (format nil "~A.~A" (second target) name) *cel-functions*))
       (list :call (format nil "~A.~A" (second target) name) nil arguments))
      ((and (member name '("all" "exists" "exists_one" "existsOne" "filter") :test #'equal) (= count 2))
       (list :comprehension (cel-comprehension-kind name) target
             (cel-comprehension-variable parser (first arguments)) (second arguments) nil nil))
      ((and (member name '("all" "exists" "exists_one" "existsOne") :test #'equal) (= count 3))
       (list :comprehension (cel-comprehension-kind name) target
             (cel-comprehension-variable parser (first arguments)) (third arguments) nil
             (cel-comprehension-variable parser (second arguments))))
      ((and (equal name "sortBy") (= count 2))
       (list :comprehension :sort-by target (cel-comprehension-variable parser (first arguments)) (second arguments) nil nil))
      ((and (equal name "map") (= count 2))
       (list :comprehension :map target (cel-comprehension-variable parser (first arguments)) (second arguments) nil nil))
      ((and (equal name "map") (= count 3))
       (list :comprehension :map target (cel-comprehension-variable parser (first arguments))
             (third arguments) (second arguments) nil))
      ((and (member name '("transformList" "transformMap") :test #'equal) (= count 3))
       (list :comprehension (if (equal name "transformList") :transform-list :transform-map) target
             (cel-comprehension-variable parser (first arguments)) (third arguments) nil
             (cel-comprehension-variable parser (second arguments))))
      ((and (member name '("transformList" "transformMap") :test #'equal) (= count 4))
       (list :comprehension (if (equal name "transformList") :transform-list :transform-map) target
             (cel-comprehension-variable parser (first arguments)) (fourth arguments) (third arguments)
             (cel-comprehension-variable parser (second arguments))))
      ((and (member name '("optMap" "optFlatMap") :test #'equal) (= count 2))
       (list :opt-map (equal name "optFlatMap") target
             (cel-comprehension-variable parser (first arguments)) (second arguments)))
      (t (list :call name target arguments)))))

(defun cel-comprehension-kind (name)
  "Map a comprehension macro's name to its node kind."
  (cond ((equal name "all") :all) ((equal name "exists") :exists)
        ((equal name "filter") :filter) (t :exists_one)))

(defun cel-construction-root (node)
  "Return the root name of a dotted type name such as Object.spec, or NIL for any other NODE."
  (case (first node)
    (:ident (second node))
    (:select (cel-construction-root (second node)))))

(defun cel-parse-construction-fields (parser)
  "Parse the field initializers of a message construction, allowing a trailing comma."
  (let ((fields nil))
    (loop
      (when (cel-accept parser "}") (return))
      (let ((name (cel-next-identifier parser)))
        (cel-expect parser ":")
        (push (cons name (cel-parse-expression parser)) fields))
      (unless (cel-accept parser ",")
        (cel-expect parser "}")
        (return)))
    (nreverse fields)))

(defun cel-parse-member (parser)
  "Parse Member: selections, indexes and method calls on a Primary."
  (let ((node (cel-parse-primary parser)))
    (loop
      (cond
        ((cel-accept parser ".")
         (if (cel-accept parser "?")
             (setf node (list :opt-select node (cel-next-identifier parser)))
             (let ((name (cel-next-identifier parser)))
               (setf node (if (cel-accept parser "(")
                              (cel-expand-method parser node name (cel-parse-arguments parser))
                              (list :select node name))))))
        ((cel-accept parser "[")
         (let* ((optional (cel-accept parser "?")) (index (cel-parse-expression parser)))
           (cel-expect parser "]")
           (setf node (list (if optional :opt-index :index) node index))))
        ((cel-operator-p parser "{")
         (unless (member (cel-construction-root node) *cel-construction-types* :test #'equal)
           (cel-check-error "message construction is not supported"))
         (cel-accept parser "{")
         (setf node (list :construct (cel-parse-construction-fields parser))))
        (t (return node))))))

(defun cel-parse-primary (parser)
  "Parse Primary: literals, identifiers, global calls, groups, lists and maps."
  (let* ((token (cel-peek parser)) (type (first token)) (value (second token)))
    (case type
      ((:int :uint :double :string :bytes :bool :null)
       (incf (cel-parser-position parser))
       (when (and (eq type :int) (> value 9223372036854775808))
         (cel-syntax-error (third token) "integer literal is out of range"))
       (when (and (eq type :uint) (> value 18446744073709551615))
         (cel-syntax-error (third token) "integer literal is out of range"))
       (list :lit (if (eq type :uint) (make-cel-uint :value value) value) type))
      (:identifier
       ;; Reserved words remain legal after a dot, as in object.metadata.namespace.
       (when (member value +cel-reserved-words+ :test #'equal)
         (cel-syntax-error (third token) "reserved identifier: ~A" value))
       (incf (cel-parser-position parser))
       (if (cel-accept parser "(")
           (cel-expand-global parser value (cel-parse-arguments parser))
           (list :ident value)))
      (:op
       (cond
         ((cel-accept parser ".") (list :ident (cel-next-identifier parser)))
         ((cel-accept parser "(")
          (let ((inner (cel-parse-expression parser)))
            (cel-expect parser ")")
            inner))
         ((cel-accept parser "[") (list :list (cel-parse-elements parser "]")))
         ((cel-accept parser "{") (list :map (cel-parse-map parser)))
         (t (cel-syntax-error (third token) "mismatched input '~A'" value))))
      (t (cel-syntax-error (third token) "unexpected end of expression")))))

(defun cel-expand-global (parser name arguments)
  "Expand the has macro, leaving ordinary global calls alone."
  (if (equal name "has")
      (let ((selection (first arguments)))
        (unless (and (= 1 (length arguments)) (eq :select (first selection)))
          (cel-syntax-error (third (cel-peek parser)) "invalid argument to has() macro"))
        (list :has (second selection) (third selection)))
      (list :call name nil arguments)))

(defun cel-parse-elements (parser closer)
  "Parse list elements up to CLOSER, allowing a trailing comma."
  (let ((elements nil))
    (loop
      (when (cel-accept parser closer) (return))
      (let ((optional (cel-accept parser "?")) (element (cel-parse-expression parser)))
        (push (if optional (list :opt-element element) element) elements))
      (unless (cel-accept parser ",")
        (cel-expect parser closer)
        (return)))
    (nreverse elements)))

(defun cel-parse-map (parser)
  "Parse map initializers, allowing a trailing comma."
  (let ((pairs nil))
    (loop
      (when (cel-accept parser "}") (return))
      (let* ((optional (cel-accept parser "?")) (key (cel-parse-expression parser)))
        (cel-expect parser ":")
        (let ((value (cel-parse-expression parser)))
          (push (cons (if optional (list :opt-element key) key) value) pairs)))
      (unless (cel-accept parser ",")
        (cel-expect parser "}")
        (return)))
    (nreverse pairs)))

;;; Static checks. A type is a keyword (:int :uint :double :string :bytes :bool :null
;;; :timestamp :duration :dyn and :list :map :object) or a list refining one with what
;;; a schema says: (:string MAX), (:bytes MAX), (:list ELEMENT MAX), (:map KEY VALUE MAX),
;;; (:object FIELD-FUNCTION), (:optional INNER) and (:opaque KIND).

(defparameter +cel-admission-request-fields+
  '("kind" "resource" "subResource" "requestKind" "requestResource" "requestSubResource"
    "name" "namespace" "operation" "userInfo" "dryRun" "options" "uid")
  "Fields the upstream admission environment declares on the request variable.")

(defvar *cel-variable-types* '(("authorizer" . (:opaque :authorizer)))
  "Alist from declared variable name to a static type more precise than dyn.")

(defvar *cel-node-types* nil
  "Table from checked node to its static type, which cost estimation reads.")

(defun cel-type-head (type)
  "Return the keyword naming TYPE, without what a schema refines it with."
  (if (consp type) (first type) type))

(defun cel-compatible-p (type &rest accepted)
  "Test a static TYPE against ACCEPTED, where dyn is compatible with everything."
  (let ((head (cel-type-head type)))
    (or (eq head :dyn) (member head accepted))))

(defun cel-list-element (type)
  "Return the element type of a list TYPE, or dyn."
  (if (and (consp type) (eq :list (first type))) (second type) :dyn))

(defun cel-map-value (type)
  "Return the value type of a map TYPE, or dyn."
  (if (and (consp type) (eq :map (first type))) (third type) :dyn))

(defun cel-map-key (type)
  "Return the key type of a map TYPE, or dyn."
  (if (and (consp type) (eq :map (first type))) (second type) :dyn))

(defun cel-type-name (type)
  "Print TYPE as a check error names it."
  (case (cel-type-head type)
    (:list (format nil "list(~A)" (cel-type-name (cel-list-element type))))
    (:map (format nil "map(~A, ~A)" (cel-type-name (cel-map-key type)) (cel-type-name (cel-map-value type))))
    (:optional (format nil "optional(~A)" (cel-type-name (second type))))
    (:opaque (string-downcase (second type)))
    (t (string-downcase (cel-type-head type)))))

(defun cel-overload-error (name types)
  "Report that no overload of NAME accepts TYPES."
  (cel-check-error "found no matching overload for '~A' applied to '(~{~A~^, ~})'" name (mapcar #'cel-type-name types)))

(defun cel-same-head-p (left right)
  "Test whether two static types share a head, or one of them is dyn."
  (let ((a (cel-type-head left)) (b (cel-type-head right)))
    (or (eq a b) (eq a :dyn) (eq b :dyn))))

(defun cel-check-call (name target arguments scope)
  "Return the result type of a call, refusing mistyped and unsupported functions."
  (let* ((full-types (mapcar (lambda (argument) (cel-check argument scope)) arguments))
         (types (mapcar #'cel-type-head full-types))
         (receiver (and target (cel-check target scope)))
         (first-type (first types)) (second-type (second types)) (count (length types)))
    (flet ((operands (&rest accepted)
             (unless (and (= 2 count) (apply #'cel-compatible-p first-type accepted)
                          (apply #'cel-compatible-p second-type accepted))
               (cel-overload-error name full-types)))
           (arithmetic-result ()
             (if (eq first-type :dyn) (second full-types) (first full-types))))
      (cond
        ((and (null target) (member name '("_==_" "_!=_") :test #'equal))
         (unless (or (eq first-type second-type) (member first-type '(:dyn :null)) (member second-type '(:dyn :null))
                     (and (member first-type '(:int :uint :double)) (member second-type '(:int :uint :double)))
                     (and (member first-type '(:map :object)) (member second-type '(:map :object))))
           (cel-overload-error name full-types))
         :bool)
        ((and (null target) (member name '("_<_" "_<=_" "_>_" "_>=_") :test #'equal))
         (unless (or (and (cel-compatible-p first-type :int :uint :double) (cel-compatible-p second-type :int :uint :double))
                     (some (lambda (kind) (and (cel-compatible-p first-type kind) (cel-compatible-p second-type kind)))
                           '(:string :bool :bytes :timestamp :duration)))
           (cel-overload-error name full-types))
         :bool)
        ((and (null target) (equal name "_in_"))
         (unless (cel-compatible-p second-type :list :map) (cel-overload-error name full-types))
         :bool)
        ((and (null target) (equal name "_+_"))
         (cond
           ((and (cel-compatible-p first-type :timestamp) (cel-compatible-p second-type :duration)
                 (not (and (eq first-type :dyn) (eq second-type :dyn))))
            :timestamp)
           ((and (cel-compatible-p first-type :duration) (cel-compatible-p second-type :timestamp)
                 (not (and (eq first-type :dyn) (eq second-type :dyn))))
            (if (eq first-type :duration)
                (if (eq second-type :dyn) :dyn :timestamp)
                :timestamp))
           (t
            (unless (cel-same-head-p first-type second-type) (cel-overload-error name full-types))
            (operands :int :uint :double :string :bytes :list :duration)
            (arithmetic-result))))
        ((and (null target) (equal name "_-_"))
         (cond
           ((and (eq first-type :timestamp) (cel-compatible-p second-type :timestamp :duration))
            (if (eq second-type :timestamp) :duration (if (eq second-type :dyn) :dyn :timestamp)))
           (t
            (unless (cel-same-head-p first-type second-type) (cel-overload-error name full-types))
            (operands :int :uint :double :duration)
            (arithmetic-result))))
        ((and (null target) (member name '("_*_" "_/_") :test #'equal))
         (unless (cel-same-head-p first-type second-type) (cel-overload-error name full-types))
         (operands :int :uint :double)
         (arithmetic-result))
        ((and (null target) (equal name "_%_"))
         (unless (cel-same-head-p first-type second-type) (cel-overload-error name full-types))
         (operands :int :uint)
         (arithmetic-result))
        ((and (null target) (equal name "-_"))
         (unless (cel-compatible-p first-type :int :double :duration) (cel-overload-error name full-types))
         first-type)
        ((and (null target) (equal name "!_"))
         (unless (cel-compatible-p first-type :bool) (cel-overload-error name full-types))
         :bool)
        ((and (null target) (= 1 count) (equal name "dyn")) :dyn)
        (t (cel-check-library-call name receiver full-types))))))

(defun cel-select-type (operand field node-name)
  "Return the type of selecting FIELD from an OPERAND type, or signal it does not exist."
  (let ((head (cel-type-head operand)))
    (case head
      (:dyn :dyn)
      (:map (cel-map-value operand))
      (:opaque
       (if (and (eq :authorizer (second operand)) (equal field "requestResource"))
           (list :opaque :resource-check)
           (cel-check-error "type '~A' does not support field selection~@[: ~A~]" (cel-type-name operand) node-name)))
      (:object
       (or (and (consp operand) (funcall (second operand) field))
           (if (consp operand)
               (cel-check-error "undefined field '~A'" field)
               :dyn)))
      (t (cel-check-error "type '~A' does not support field selection~@[: ~A~]" (cel-type-name operand) node-name)))))

(defun cel-check (node scope)
  "Return NODE's static type, where SCOPE is an alist of macro variables in force."
  (let ((type (cel-check-node node scope)))
    (when *cel-node-types* (setf (gethash node *cel-node-types*) type))
    type))

(defun cel-check-comprehension (node scope)
  "Check a comprehension macro and return its result type."
  (destructuring-bind (kind iterable variable body predicate second-variable) (rest node)
    (let* ((source (cel-check iterable scope)))
      (unless (cel-compatible-p source :list :map)
        (cel-check-error "expression of type '~A' cannot be range of a comprehension" (cel-type-name source)))
      (when second-variable
        (when (equal variable second-variable)
          (cel-check-error "duplicate variable name: ~A" variable)))
      (let* ((list-source (eq :list (cel-type-head source)))
             ;; A comprehension visits every element once, so its result holds
             ;; at most as many entries as the source. Carrying that bound keeps
             ;; a later size-sensitive operation (==, in, a nested macro) from
             ;; costing as if the mapped/filtered list were unbounded.
             (source-bound (cond (list-source (and (consp source) (third source)))
                                 ((eq :map (cel-type-head source)) (and (consp source) (fourth source)))
                                 (t nil)))
             (first-type (cond ((and second-variable list-source) :int)
                               (list-source (cel-list-element source))
                               ((consp source) (cel-map-key source))
                               (t :dyn)))
             (second-type (when second-variable
                            (if list-source (cel-list-element source) (cel-map-value source))))
             (inner (append (when second-variable (list (cons second-variable second-type)))
                            (list (cons variable first-type)) scope))
             (type (cel-check body inner)))
        (when predicate
          (unless (cel-compatible-p (cel-check predicate inner) :bool)
            (cel-check-error "comprehension filter must be bool")))
        (when (and (eq kind :sort-by) (not list-source) (not (eq :dyn (cel-type-head source))))
          (cel-check-error "sortBy can only be applied to a list, got: ~A" (cel-type-name source)))
        (ecase kind
          (:sort-by
           (unless (cel-compatible-p type :int :uint :double :bool :string :timestamp :duration)
             (cel-check-error "sortBy key must be a comparable type, got: ~A" (cel-type-name type)))
           source)
          ((:all :exists :exists_one :filter)
           (unless (cel-compatible-p type :bool)
             (cel-check-error "comprehension predicate must be bool"))
           (if (eq kind :filter)
               (list :list (cel-list-element source) source-bound)
               :bool))
          (:map (list :list type source-bound))
          (:transform-list (list :list type source-bound))
          (:transform-map (list :map first-type type source-bound)))))))

(defun cel-check-node (node scope)
  "Compute NODE's static type."
  (ecase (first node)
    (:lit
     (when (and (eq :int (third node)) (not (typep (second node) '(signed-byte 64))))
       (cel-check-error "integer literal is out of range"))
     (case (third node)
       (:string (list :string (length (second node))))
       (:bytes (list :bytes (length (second node))))
       (t (third node))))
    (:ident
     (let* ((name (second node)) (local (assoc name scope :test #'equal)))
       (cond (local (cdr local))
             ((assoc name *cel-variable-types* :test #'equal)
              (cdr (assoc name *cel-variable-types* :test #'equal)))
             ((member name *cel-declared-variables* :test #'equal) :dyn)
             (t (cel-check-error "undeclared reference to '~A'" name)))))
    (:select
     (destructuring-bind (operand field) (rest node)
       (when (and (equal '(:ident "request") operand) (not (assoc "request" scope :test #'equal))
                  (not (member field +cel-admission-request-fields+ :test #'equal)))
         (cel-check-error "undefined field '~A' on request" field))
       (let ((type (cel-check operand scope)))
         (if (eq :optional (cel-type-head type))
             (list :optional (cel-select-type (second type) field field))
             (cel-select-type type field field)))))
    (:opt-select
     (destructuring-bind (operand field) (rest node)
       (let* ((type (cel-check operand scope))
              (inner (if (eq :optional (cel-type-head type)) (second type) type)))
         (list :optional (cel-select-type inner field field)))))
    (:opt-index
     (destructuring-bind (operand index) (rest node)
       (let* ((type (cel-check operand scope)) (inner (if (eq :optional (cel-type-head type)) (second type) type)))
         (cel-check index scope)
         (list :optional (case (cel-type-head inner)
                           (:list (cel-list-element inner))
                           (:map (cel-map-value inner))
                           (t :dyn))))))
    (:has
     (let ((type (cel-check (second node) scope)))
       (unless (cel-compatible-p type :map :object :optional)
         (cel-check-error "invalid argument to has() macro"))
       (when (and (eq :object (cel-type-head type)) (consp type))
         (cel-select-type type (third node) nil))
       :bool))
    (:index
     (let* ((operand (cel-check (second node) scope)) (index (cel-check (third node) scope))
            (optional (eq :optional (cel-type-head operand)))
            (inner (if optional (second operand) operand))
            (head (cel-type-head inner)))
       (unless (or (eq head :dyn)
                   (and (eq head :list) (cel-compatible-p index :int :uint))
                   (eq head :map))
         (cel-overload-error "_[_]" (list operand index)))
       (let ((result (case head
                       (:list (cel-list-element inner))
                       (:map (cel-map-value inner))
                       (t :dyn))))
         (if optional (list :optional result) result))))
    (:call (destructuring-bind (name target arguments) (rest node)
             (cel-check-call name target arguments scope)))
    (:list
     (let ((element nil) (dynamic nil))
       (dolist (item (second node))
         (let* ((optional (eq :opt-element (first item)))
                (type (cel-check (if optional (second item) item) scope))
                (type (if optional (if (eq :optional (cel-type-head type)) (second type) :dyn) type)))
           (cond ((null element) (setf element type))
                 ((member :dyn (list (cel-type-head element) (cel-type-head type))) (setf dynamic t))
                 ((not (equal (cel-type-head element) (cel-type-head type)))
                  (cel-check-error "expected type '~A' but found '~A'" (cel-type-name element) (cel-type-name type))))))
       (list :list (if (or dynamic (null element)) :dyn element) (length (second node)))))
    (:construct
     (dolist (field (second node)) (cel-check (cdr field) scope))
     :map)
    (:map
     (let ((value-type nil) (dynamic nil))
       (dolist (pair (second node))
         (let* ((optional (eq :opt-element (first (car pair))))
                (key (cel-check (if optional (second (car pair)) (car pair)) scope)))
           (unless (cel-compatible-p key :string :int :uint :bool)
             (cel-check-error "unsupported map key type '~A'" (cel-type-name key)))
           (let ((type (cel-check (cdr pair) scope)))
             (cond ((null value-type) (setf value-type type))
                   ((member :dyn (list (cel-type-head value-type) (cel-type-head type))) (setf dynamic t))
                   ((not (equal (cel-type-head value-type) (cel-type-head type)))
                    (cel-check-error "expected type '~A' but found '~A'" (cel-type-name value-type) (cel-type-name type)))))))
       (list :map :dyn (if (or dynamic (null value-type)) :dyn value-type) (length (second node)))))
    (:cond
     (destructuring-bind (condition then else) (rest node)
       (unless (cel-compatible-p (cel-check condition scope) :bool)
         (cel-overload-error "_?_:_" (list (cel-check condition scope))))
       (let ((left (cel-check then scope)) (right (cel-check else scope)))
         (cond ((eq (cel-type-head left) (cel-type-head right)) left)
               ((or (eq left :dyn) (eq right :dyn) (eq left :null) (eq right :null)) :dyn)
               (t (cel-overload-error "_?_:_" (list left right)))))))
    ((:and :or)
     (let ((left (cel-check (second node) scope)) (right (cel-check (third node) scope)))
       (unless (and (cel-compatible-p left :bool) (cel-compatible-p right :bool))
         (cel-overload-error (if (eq :and (first node)) "_&&_" "_||_") (list left right)))
       :bool))
    (:bind
     (destructuring-bind (variable init body) (rest node)
       (cel-check body (acons variable (cel-check init scope) scope))))
    (:opt-map
     (destructuring-bind (flat target variable body) (rest node)
       (let* ((type (cel-check target scope))
              (inner (if (eq :optional (cel-type-head type)) (second type) :dyn))
              (result (cel-check body (acons variable inner scope))))
         (if flat result (list :optional result)))))
    (:comprehension (cel-check-comprehension node scope))))

(defun compile-cel-expression (expression)
  "Parse and check EXPRESSION, returning its program and static result type."
  (when (> (length expression) +cel-maximum-expression-length+)
    (cel-check-error "expression exceeds ~D characters" +cel-maximum-expression-length+))
  (let* ((parser (make-cel-parser (cel-tokenize expression)))
         (node (cel-parse-expression parser))
         (token (cel-peek parser)))
    (unless (eq :eof (first token))
      (cel-syntax-error (third token) "extraneous input '~A'" (second token)))
    (values node (cel-check node nil))))

(defun compile-cel-condition (expression)
  "Parse and check EXPRESSION, which must have the static result type bool."
  (multiple-value-bind (node type) (compile-cel-expression expression)
    (unless (eq (cel-type-head type) :bool)
      (cel-check-error "must evaluate to bool, found ~A" (cel-type-name type)))
    node))

(defun cel-references-variable-p (node name)
  "Test whether the tree NODE reads the variable NAME."
  (cond ((atom node) nil)
        ((and (eq :ident (first node)) (equal name (second node))) t)
        (t (loop for rest = node then (cdr rest)
                 while (consp rest)
                 thereis (cel-references-variable-p (car rest) name)))))

;;; Cost estimation, after cel-go's checker. Sizes and costs saturate well above any limit.

(defparameter +cel-unknown-size+ (expt 2 63) "Size of a value nothing bounds.")
(defparameter +cel-traversal-factor+ 1/10 "Cost per character to traverse a string.")
(defparameter +cel-regex-factor+ 1/4 "Cost per character of a regex pattern per unit of text.")

(defun cel-type-size (type)
  "Return the largest size TYPE can have, one for a scalar."
  (case (cel-type-head type)
    (:string (if (and (consp type) (second type)) (second type) +cel-unknown-size+))
    (:bytes (if (and (consp type) (second type)) (second type) +cel-unknown-size+))
    (:list (if (and (consp type) (third type)) (third type) +cel-unknown-size+))
    (:map (if (and (consp type) (fourth type)) (fourth type) +cel-unknown-size+))
    ;; Schema-backed object types have MaxElements=0. Their
    ;; fields are statically known; treating them as unbounded maps rejects
    ;; ordinary object immutability rules such as self == oldSelf.
    (:object 0)
    (:dyn +cel-unknown-size+)
    (t 1)))

(defun cel-saturate (value)
  "Keep estimates in a range where repeated multiplication stays cheap."
  (min value (expt 2 80)))

(defun cel-node-size (node)
  "Return the estimated size of NODE's value."
  (cel-type-size (or (and *cel-node-types* (gethash node *cel-node-types*)) :dyn)))

(defun cel-estimate-call (node)
  "Estimate one call node's largest cost, with its operands."
  (destructuring-bind (name target arguments) (rest node)
    (let* ((operand-cost (+ (if target (cel-estimate target) 0)
                            (loop for argument in arguments sum (cel-estimate argument))))
           (subject (or target (first arguments)))
           (subject-size (if subject (cel-node-size subject) 1)))
      (flet ((traversal (size) (ceiling (* size +cel-traversal-factor+))))
        (+ operand-cost
           (cond
             ((member name '("_==_" "_!=_" "_<_" "_<=_" "_>_" "_>=_") :test #'equal)
              (traversal (min (cel-node-size (first arguments)) (cel-node-size (second arguments)))))
             ((equal name "_in_") (cel-node-size (second arguments)))
             ((equal name "_+_")
              (if (member (cel-type-head (gethash (first arguments) *cel-node-types*)) '(:string :bytes))
                  (traversal (+ (cel-node-size (first arguments)) (cel-node-size (second arguments))))
                  1))
             ((member name '("startsWith" "endsWith") :test #'equal) (traversal (cel-node-size (first arguments))))
             ((equal name "contains")
              (* (traversal subject-size) (traversal (cel-node-size (first arguments)))))
             ((member name '("matches" "find" "findAll") :test #'equal)
              (* (ceiling (* (1+ subject-size) +cel-traversal-factor+))
                 (max 1 (ceiling (* (cel-node-size (if target (first arguments) (second arguments))) +cel-regex-factor+)))))
             ((member name '("isSorted" "sum" "max" "min" "indexOf" "lastIndexOf") :test #'equal)
              (if (and target (eq :string (cel-type-head (gethash target *cel-node-types*))))
                  (* (traversal subject-size) (traversal (cel-node-size (first arguments))))
                  (let ((element (cel-list-element (or (and target (gethash target *cel-node-types*)) :dyn))))
                    (* subject-size (max 1 (traversal (cel-type-size element)))))))
             ((member name '("lowerAscii" "upperAscii" "substring" "trim" "url" "jsonpatch.escapeKey" "cidr" "isIP"
                             "isCIDR" "ip" "quantity" "isQuantity" "semver" "isSemver" "isURL" "format")
                      :test #'equal)
              (traversal subject-size))
             ((member name '("replace" "split") :test #'equal) (traversal (* 2 subject-size)))
             ((equal name "join") (traversal subject-size))
             ((equal name "check") 350000)
             ((equal name "validate") (traversal (* 16 subject-size)))
             (t 1)))))))

(defun cel-estimate (node)
  "Estimate NODE's largest cost, as cel-go's checker does for a checked expression."
  (cel-saturate
   (ecase (first node)
     (:lit 0)
     (:ident 1)
     ((:select :opt-select) (+ 1 (cel-estimate (second node))))
     (:has (cel-estimate (second node)))
     ((:index :opt-index) (+ 1 (cel-estimate (second node)) (cel-estimate (third node))))
     (:call (cel-estimate-call node))
     (:list (+ 10 (loop for item in (second node)
                        sum (cel-estimate (if (eq :opt-element (first item)) (second item) item)))))
     (:construct (+ 40 (loop for field in (second node) sum (cel-estimate (cdr field)))))
     (:map (+ 30 (loop for pair in (second node)
                       sum (+ (cel-estimate (if (eq :opt-element (first (car pair))) (second (car pair)) (car pair)))
                              (cel-estimate (cdr pair))))))
     (:cond (+ (cel-estimate (second node)) (max (cel-estimate (third node)) (cel-estimate (fourth node)))))
     ((:and :or) (+ (cel-estimate (second node)) (cel-estimate (third node))))
     (:bind (+ (cel-estimate (third node)) (cel-estimate (fourth node))))
     (:opt-map (+ 2 (cel-estimate (third node)) (cel-estimate (fifth node))))
     (:comprehension
      (destructuring-bind (kind iterable variable body predicate second-variable) (rest node)
        (declare (ignore variable second-variable))
        (let* ((range (cel-estimate iterable))
               (count (cel-node-size iterable))
               (body-cost (+ (cel-estimate body) (if predicate (cel-estimate predicate) 0)))
               (loop-cost (ecase kind
                            ((:all :exists) (+ 3 body-cost))
                            (:exists_one (+ 3 body-cost))
                            (:filter (+ 12 body-cost))
                            ((:map :transform-list :sort-by) (+ 12 body-cost))
                            (:transform-map (+ 32 body-cost)))))
          (+ range 1 (* count loop-cost))))))))

(defun cel-estimated-cost (node)
  "Return the largest cost a checked program NODE can run up."
  (cel-estimate node))

;;; Evaluation

(defun cel-bytes-p (value)
  "Recognize CEL bytes, which are octet vectors unlike the general vectors of a JSON list."
  (typep value '(array (unsigned-byte 8) (*))))

(defun cel-list-p (value)
  "Recognize a CEL list, which JSON decoding represents as a non-string vector."
  (and (vectorp value) (not (stringp value)) (not (cel-bytes-p value))))

(defun cel-bool-p (value)
  "Recognize a CEL bool, which JSON decoding represents as T or NIL."
  (or (eq value t) (null value)))

(defun cel-int64 (value)
  "Return VALUE when it fits int64, or fail as CEL does on overflow."
  (unless (typep value '(signed-byte 64)) (cel-fail "integer overflow"))
  value)

(defun cel-uint64 (value)
  "Wrap VALUE as a uint when it fits, or fail as CEL does on overflow."
  (unless (typep value '(unsigned-byte 64)) (cel-fail "unsigned integer overflow"))
  (make-cel-uint :value value))

(defun cel-charge (cost)
  "Charge COST against the expression's budget, stopping it when that runs out."
  (when (minusp (decf *cel-remaining-steps* cost))
    (error 'cel-cost-exceeded :message "operation cancelled: actual cost limit exceeded")))

(defun cel-numeric-value (value)
  "Return the real number VALUE denotes, or NIL."
  (cond ((realp value) value)
        ((cel-uint-p value) (cel-uint-value value))))

;; tagged set and map lists compare and concatenate as upstream's
;; unstructuredSetList and unstructuredMapList do. Lists stay plain vectors; the kind is
;; noted beside them, weakly, when CRD values are converted for rules.
(defvar *cel-list-kinds* (make-hash-table :test #'eq :weakness :key :synchronized t)
  "From a list value to :SET, or (:MAP . keys) for a map list keyed by those fields.")

(defun cel-mark-list (items kind)
  "Note that ITEMS is a set list (KIND :SET) or a map list (KIND (:MAP . keys)), returning ITEMS."
  (when (plusp (length items)) (setf (gethash items *cel-list-kinds*) kind))
  items)

(defun cel-list-kind (items)
  "Return the list type noted for ITEMS, or NIL for an ordinary atomic list."
  (and (plusp (length items)) (gethash items *cel-list-kinds*)))

(defun cel-map-list-key (item keys)
  "Return ITEM's key values under KEYS, or :NONE when ITEM is not an object."
  (if (hash-table-p item)
      (mapcar (lambda (key) (gethash key item 'null)) keys)
      :none))

(defun cel-map-list-find (items keys key)
  "Return the element of ITEMS whose key fields equal KEY, and whether there was one."
  (unless (eq key :none)
    (loop for item across items
          when (let ((candidate (cel-map-list-key item keys)))
                 (and (not (eq candidate :none)) (every #'cel-equal candidate key)))
            do (return (values item t)))))

(defun cel-typed-list-equal (left right kind)
  "Compare RIGHT to LEFT, a set or map list of KIND, ignoring element order."
  (and (= (length left) (length right))
       (if (eq kind :set)
           (every (lambda (item) (find item left :test #'cel-equal)) right)
           (every (lambda (item)
                    (multiple-value-bind (match found) (cel-map-list-find left (rest kind) (cel-map-list-key item (rest kind)))
                      (and found (cel-equal match item))))
                  right))))

(defun cel-typed-list-concatenate (left right kind)
  "Concatenate RIGHT onto LEFT, a set or map list of KIND: sets skip present items, map lists replace by key."
  (cel-mark-list
   (if (eq kind :set)
       (concatenate 'vector left (remove-if (lambda (item) (find item left :test #'cel-equal)) right))
       (let ((result (copy-seq left)) (added nil) (keys (rest kind)))
         (loop for item across right
               for key = (cel-map-list-key item keys)
               for position = (unless (eq key :none)
                                (position-if (lambda (old)
                                               (let ((candidate (cel-map-list-key old keys)))
                                                 (and (not (eq candidate :none)) (every #'cel-equal candidate key))))
                                             result))
               do (if position (setf (aref result position) item) (push item added)))
         (concatenate 'vector result (nreverse added))))
   kind))

(defun cel-opaque-equal (left right)
  "Compare opaque library values by kind and representation."
  (and (eq (cel-opaque-kind left) (cel-opaque-kind right))
       (case (cel-opaque-kind left)
         (:quantity
          (zerop (decimal-quantity-compare (cel-opaque-value left)
                                           (cel-opaque-value right))))
         (t (equalp (cel-opaque-value left) (cel-opaque-value right))))))

(defun cel-equal (left right)
  "Apply CEL heterogeneous equality."
  (let ((a (cel-numeric-value left)) (b (cel-numeric-value right)))
    (cond ((and a b) (= a b))
          ((and (stringp left) (stringp right)) (string= left right))
          ((and (cel-bytes-p left) (cel-bytes-p right)) (equalp left right))
          ((and (cel-list-p left) (cel-list-p right))
           (let ((kind (cel-list-kind left)))
             (if kind
                 (cel-typed-list-equal left right kind)
                 (and (= (length left) (length right)) (every #'cel-equal left right)))))
          ((and (hash-table-p left) (hash-table-p right))
           (and (= (hash-table-count left) (hash-table-count right))
                (loop for key being the hash-keys of left using (hash-value value)
                      always (multiple-value-bind (other present) (gethash key right)
                               (and present (cel-equal value other))))))
          ((and (cel-bool-p left) (cel-bool-p right)) (eq left right))
          ((and (eq left 'null) (eq right 'null)) t)
          ((and (cel-timestamp-p left) (cel-timestamp-p right)) (= (cel-timestamp-nanos left) (cel-timestamp-nanos right)))
          ((and (cel-duration-p left) (cel-duration-p right)) (= (cel-duration-nanos left) (cel-duration-nanos right)))
          ((and (cel-optional-p left) (cel-optional-p right))
           (and (eq (cel-optional-present left) (cel-optional-present right))
                (or (not (cel-optional-present left)) (cel-equal (cel-optional-value left) (cel-optional-value right)))))
          ((and (cel-opaque-p left) (cel-opaque-p right)) (cel-opaque-equal left right))
          (t nil))))

(defun cel-compare-values (left right name)
  "Return -1, 0 or 1 for two values with an ordering, or fail the NAME overload."
  (let ((a (cel-numeric-value left)) (b (cel-numeric-value right)))
    (cond ((and a b) (cond ((< a b) -1) ((> a b) 1) (t 0)))
          ((and (stringp left) (stringp right))
           (cond ((string< left right) -1) ((string> left right) 1) (t 0)))
          ((and (cel-bytes-p left) (cel-bytes-p right))
           (let ((mismatch (mismatch left right)))
             (cond ((null mismatch) 0)
                   ((>= mismatch (length left)) -1)
                   ((>= mismatch (length right)) 1)
                   ((< (aref left mismatch) (aref right mismatch)) -1)
                   (t 1))))
          ((and (cel-bool-p left) (cel-bool-p right))
           (cond ((eq left right) 0) (left 1) (t -1)))
          ((and (cel-timestamp-p left) (cel-timestamp-p right))
           (signum (- (cel-timestamp-nanos left) (cel-timestamp-nanos right))))
          ((and (cel-duration-p left) (cel-duration-p right))
           (signum (- (cel-duration-nanos left) (cel-duration-nanos right))))
          (t (cel-fail "no such overload: ~A" name)))))

(defun cel-compare (name left right)
  "Evaluate an ordering operator, failing on values with no ordering overload."
  (let ((order (cel-compare-values left right name)))
    (cond ((equal name "_<_") (< order 0)) ((equal name "_<=_") (<= order 0))
          ((equal name "_>_") (> order 0)) (t (>= order 0)))))

(defun cel-arithmetic (name left right)
  "Evaluate an arithmetic operator with CEL's overflow and zero-division errors."
  (cond
    ((and (integerp left) (integerp right))
     (cel-int64
      (cond ((equal name "_+_") (+ left right)) ((equal name "_-_") (- left right))
            ((equal name "_*_") (* left right))
            ((zerop right) (cel-fail "division by zero"))
            ((equal name "_/_") (truncate left right))
            (t (rem left right)))))
    ((and (cel-uint-p left) (cel-uint-p right))
     (let ((a (cel-uint-value left)) (b (cel-uint-value right)))
       (cel-uint64
        (cond ((equal name "_+_") (+ a b)) ((equal name "_-_") (- a b))
              ((equal name "_*_") (* a b))
              ((zerop b) (cel-fail "division by zero"))
              ((equal name "_/_") (truncate a b))
              (t (rem a b))))))
    ((and (floatp left) (floatp right) (not (equal name "_%_")))
     (handler-case
         (cond ((equal name "_+_") (+ left right)) ((equal name "_-_") (- left right))
               ((equal name "_*_") (* left right)) (t (/ left right)))
       (arithmetic-error () (cel-fail "floating-point result is out of range"))))
    ((and (equal name "_+_") (stringp left) (stringp right)) (concatenate 'string left right))
    ((and (equal name "_+_") (cel-bytes-p left) (cel-bytes-p right))
     (concatenate '(vector (unsigned-byte 8)) left right))
    ((and (equal name "_+_") (cel-list-p left) (cel-list-p right))
     (let ((kind (cel-list-kind left)))
       (if kind (cel-typed-list-concatenate left right kind) (concatenate 'vector left right))))
    ((and (cel-timestamp-p left) (cel-duration-p right) (member name '("_+_" "_-_") :test #'equal))
     (cel-checked-timestamp
      (funcall (if (equal name "_+_") #'+ #'-) (cel-timestamp-nanos left) (cel-duration-nanos right))))
    ((and (equal name "_+_") (cel-duration-p left) (cel-timestamp-p right))
     (cel-checked-timestamp (+ (cel-duration-nanos left) (cel-timestamp-nanos right))))
    ((and (cel-timestamp-p left) (cel-timestamp-p right) (equal name "_-_"))
     (cel-checked-duration (- (cel-timestamp-nanos left) (cel-timestamp-nanos right))))
    ((and (cel-duration-p left) (cel-duration-p right) (member name '("_+_" "_-_") :test #'equal))
     (cel-checked-duration
      (funcall (if (equal name "_+_") #'+ #'-) (cel-duration-nanos left) (cel-duration-nanos right))))
    (t (cel-fail "no such overload: ~A" name))))

(defun cel-require-string (value name)
  "Return VALUE when it is a string, or fail the NAME overload."
  (unless (stringp value) (cel-fail "no such overload: ~A" name))
  value)

(defun cel-value-size (value)
  "Return the size cost tracking uses: length of a string, bytes, list or map, else one."
  (cond ((stringp value) (length value))
        ((cel-bytes-p value) (length value))
        ((cel-list-p value) (length value))
        ((hash-table-p value) (hash-table-count value))
        (t 1)))

(defun cel-charge-call (name target arguments)
  "Charge one evaluated call, as cel-go's runtime cost tracker does."
  (flet ((traversal (size) (ceiling (* size +cel-traversal-factor+))))
    (let ((subject (if target (first target) (first arguments))))
      (cel-charge
       (cond
         ((member name '("_==_" "_!=_" "_<_" "_<=_" "_>_" "_>=_") :test #'equal)
          (max 1 (traversal (min (cel-value-size (first arguments)) (cel-value-size (second arguments))))))
         ((equal name "_in_") (max 1 (cel-value-size (second arguments))))
         ((and (equal name "_+_") (or (stringp (first arguments)) (cel-bytes-p (first arguments))))
          (max 1 (traversal (+ (cel-value-size (first arguments)) (cel-value-size (second arguments))))))
         ((member name '("startsWith" "endsWith") :test #'equal)
          (max 1 (traversal (cel-value-size (first arguments)))))
         ((equal name "contains")
          (max 1 (* (traversal (cel-value-size subject)) (traversal (cel-value-size (first arguments))))))
         ((member name '("matches" "find" "findAll") :test #'equal)
          (max 1 (* (ceiling (* (1+ (cel-value-size subject)) +cel-traversal-factor+))
                    (ceiling (* (cel-value-size (if target (first arguments) (second arguments))) +cel-regex-factor+)))))
         ((member name '("isSorted" "sum" "max" "min" "indexOf" "lastIndexOf") :test #'equal)
          (max 1 (cel-value-size subject)))
         ((member name '("lowerAscii" "upperAscii" "substring" "trim" "url" "jsonpatch.escapeKey" "replace" "split"
                         "join" "cidr" "isIP" "isCIDR" "ip" "quantity" "isQuantity" "semver" "isSemver" "isURL")
                  :test #'equal)
          (max 1 (traversal (cel-value-size subject))))
         ((equal name "check") 350000)
         (t 1))))))

(defun cel-apply (name target arguments)
  "Apply an evaluated function to evaluated TARGET and ARGUMENTS."
  (cel-charge-call name target arguments)
  (let ((first-argument (first arguments)) (second-argument (second arguments)))
    (cond
      ((equal name "_==_") (cel-equal first-argument second-argument))
      ((equal name "_!=_") (not (cel-equal first-argument second-argument)))
      ((member name '("_<_" "_<=_" "_>_" "_>=_") :test #'equal)
       (cel-compare name first-argument second-argument))
      ((member name '("_+_" "_-_" "_*_" "_/_" "_%_") :test #'equal)
       (cel-arithmetic name first-argument second-argument))
      ((equal name "-_")
       (cond ((integerp first-argument) (cel-int64 (- first-argument)))
             ((floatp first-argument) (- first-argument))
             ((cel-duration-p first-argument) (cel-checked-duration (- (cel-duration-nanos first-argument))))
             (t (cel-fail "no such overload: -_"))))
      ((equal name "!_")
       (unless (cel-bool-p first-argument) (cel-fail "no such overload: !_"))
       (not first-argument))
      ((equal name "_in_")
       (cond ((cel-list-p second-argument)
              (and (find first-argument second-argument :test #'cel-equal) t))
             ((hash-table-p second-argument)
              (and (nth-value 1 (gethash (cel-map-key-string first-argument) second-argument)) t))
             (t (cel-fail "no such overload: _in_"))))
      ((equal name "dyn") first-argument)
      (t (cel-apply-library-call name target arguments)))))

(defun cel-capture (node bindings)
  "Evaluate NODE, returning its value and any error instead of unwinding."
  (handler-case (values (cel-evaluate node bindings) nil)
    (cel-cost-exceeded (condition) (error condition))
    (cel-evaluation-error (condition) (values nil condition))))

(defun cel-logical (absorbing left right bindings name)
  "Evaluate && or ||, where ABSORBING on either side wins over the other side's error."
  (multiple-value-bind (left-value left-error) (cel-capture left bindings)
    (when (and (null left-error) (not (cel-bool-p left-value))) (cel-fail "no such overload: ~A" name))
    (if (and (null left-error) (eq left-value absorbing))
        absorbing
        (multiple-value-bind (right-value right-error) (cel-capture right bindings)
          (when (and (null right-error) (not (cel-bool-p right-value))) (cel-fail "no such overload: ~A" name))
          (cond ((and (null right-error) (eq right-value absorbing)) absorbing)
                (left-error (error left-error))
                (right-error (error right-error))
                (t (not absorbing)))))))

(defun cel-iteration-entries (value two-variables)
  "List a comprehension's iterations as bindings of its one or two variables."
  (cond ((cel-list-p value)
         (if two-variables
             (loop for item across value for index from 0 collect (cons index item))
             (coerce value 'list)))
        ((hash-table-p value)
         (if two-variables
             (loop for key being the hash-keys of value using (hash-value item) collect (cons key item))
             (loop for key being the hash-keys of value collect key)))
        (t (cel-fail "expression of this type cannot be iterated"))))

(defun cel-comprehend (kind items variable body predicate second-variable bindings)
  "Evaluate a comprehension macro with its documented error absorption."
  (labels ((scope (item)
             (if second-variable
                 (acons variable (car item) (acons second-variable (cdr item) bindings))
                 (acons variable item bindings)))
           (truth (item)
             (cel-charge 3)
             (let ((value (cel-evaluate body (scope item))))
               (unless (cel-bool-p value) (cel-fail "comprehension predicate must be bool"))
               value))
           (kept (item)
             (or (null predicate)
                 (let ((keep (cel-evaluate predicate (scope item))))
                   (unless (cel-bool-p keep) (cel-fail "comprehension filter must be bool"))
                   keep))))
    (ecase kind
      ((:all :exists)
       (let ((absorbing (if (eq kind :all) nil t)) (pending nil))
         (dolist (item items)
           (handler-case
               (when (eq (truth item) absorbing)
                 (return-from cel-comprehend absorbing))
             (cel-cost-exceeded (condition) (error condition))
             (cel-evaluation-error (condition) (setf pending (or pending condition)))))
         (when pending (error pending))
         (not absorbing)))
      (:exists_one (= 1 (count-if #'truth items)))
      (:sort-by
       (let ((keyed (loop for item in items
                          do (cel-charge 3)
                          collect (cons (cel-evaluate body (scope item)) item))))
         (loop for (left right) on keyed while right
               do (cel-compare-values (car left) (car right) "sortBy"))
         (map 'vector #'cdr (stable-sort keyed (lambda (left right)
                                                 (minusp (cel-compare-values (car left) (car right) "sortBy")))))))
      (:filter (coerce (remove-if-not #'truth items) 'vector))
      (:map
       (coerce (loop for item in items
                     do (cel-charge 3)
                     when (kept item) collect (cel-evaluate body (scope item)))
               'vector))
      (:transform-list
       (coerce (loop for item in items
                     do (cel-charge 3)
                     when (kept item) collect (cel-evaluate body (scope item)))
               'vector))
      (:transform-map
       (let ((result (make-hash-table :test #'equal)))
         (dolist (item items result)
           (cel-charge 3)
           (when (kept item)
             (setf (gethash (cel-map-key-string (car item)) result) (cel-evaluate body (scope item))))))))))

(defun cel-field-value (operand field)
  "Read FIELD of a map or object, accepting its escaped CEL spelling; returns value and presence."
  (multiple-value-bind (value present) (gethash field operand)
    (if present
        (values value t)
        (if (search "__" field)
            (gethash (cel-unescape-field field) operand)
            (values nil nil)))))

(defun cel-map-key-string (key)
  "Spell a map key, keeping the JSON string keys of objects and printing other scalar keys."
  (cond ((stringp key) key)
        ((integerp key) (format nil "~D" key))
        ((cel-uint-p key) (format nil "~D" (cel-uint-value key)))
        ((eq key t) "true")
        ((null key) "false")
        (t (cel-fail "unsupported map key"))))

(defun cel-evaluate (node bindings)
  "Evaluate NODE, where BINDINGS is an alist of variables to their values."
  (unless (eq :lit (first node)) (cel-charge 1))
  (ecase (first node)
    (:lit (second node))
    (:ident
     (let ((binding (assoc (second node) bindings :test #'equal)))
       (unless binding (cel-fail "no such attribute: ~A" (second node)))
       (cdr binding)))
    (:select
     (let ((operand (cel-evaluate (second node) bindings)))
       (cond
         ((cel-optional-p operand) (cel-select-optional operand (third node)))
         ((and (cel-opaque-p operand) (eq :authorizer (cel-opaque-kind operand)) (equal "requestResource" (third node)))
          (cel-opaque :resource-check (append *cel-request-resource* (cel-opaque-value operand))))
         (t
          (unless (hash-table-p operand) (cel-fail "no such overload: selecting ~A" (third node)))
          (multiple-value-bind (value present) (cel-field-value operand (third node))
            (unless present (cel-fail "no such key: ~A" (third node)))
            value)))))
    (:opt-select
     (cel-select-optional (cel-evaluate (second node) bindings) (third node)))
    (:has
     (let ((operand (cel-evaluate (second node) bindings)))
       (cond
         ((cel-optional-p operand)
          (cel-optional-present (cel-select-optional operand (third node))))
         ((hash-table-p operand) (and (nth-value 1 (cel-field-value operand (third node))) t))
         (t (cel-fail "no such overload: has(~A)" (third node))))))
    (:index
     (let ((operand (cel-evaluate (second node) bindings)) (index (cel-evaluate (third node) bindings)))
       (when (cel-optional-p operand)
         (return-from cel-evaluate (cel-index-optional operand index)))
       (let ((position (cel-numeric-value index)))
         (cond ((and (cel-list-p operand) position (= position (truncate position)))
                (let ((position (truncate position)))
                  (unless (< -1 position (length operand)) (cel-fail "index out of bounds: ~D" position))
                  (aref operand position)))
               ((hash-table-p operand)
                (multiple-value-bind (value present) (gethash (cel-map-key-string index) operand)
                  (unless present (cel-fail "no such key: ~A" index))
                  value))
               (t (cel-fail "no such overload: _[_]"))))))
    (:opt-index
     (cel-index-optional (cel-evaluate (second node) bindings) (cel-evaluate (third node) bindings)))
    (:call
     (destructuring-bind (name target arguments) (rest node)
       (cel-apply name
                  (and target (list (cel-evaluate target bindings)))
                  (mapcar (lambda (argument) (cel-evaluate argument bindings)) arguments))))
    (:list
     (cel-charge 10)
     (let ((items nil))
       (dolist (item (second node))
         (if (eq :opt-element (first item))
             (let ((value (cel-evaluate (second item) bindings)))
               (unless (cel-optional-p value) (cel-fail "optional list element requires an optional value"))
               (when (cel-optional-present value) (push (cel-optional-value value) items)))
             (push (cel-evaluate item bindings) items)))
       (coerce (nreverse items) 'vector)))
    (:construct
     (cel-charge 40)
     (let ((object (make-hash-table :test #'equal)))
       (dolist (field (second node) object)
         (setf (gethash (car field) object) (cel-evaluate (cdr field) bindings)))))
    (:map
     (cel-charge 30)
     (let ((object (make-hash-table :test #'equal)))
       (dolist (pair (second node) object)
         (let* ((optional (eq :opt-element (first (car pair))))
                (key (cel-map-key-string (cel-evaluate (if optional (second (car pair)) (car pair)) bindings)))
                (value (cel-evaluate (cdr pair) bindings)))
           (when (nth-value 1 (gethash key object)) (cel-fail "repeated map key: ~A" key))
           (if optional
               (progn
                 (unless (cel-optional-p value) (cel-fail "optional map entry requires an optional value"))
                 (when (cel-optional-present value) (setf (gethash key object) (cel-optional-value value))))
               (setf (gethash key object) value))))))
    (:cond
     (let ((condition (cel-evaluate (second node) bindings)))
       (unless (cel-bool-p condition) (cel-fail "no such overload: _?_:_"))
       (cel-evaluate (if condition (third node) (fourth node)) bindings)))
    (:and (cel-logical nil (second node) (third node) bindings "_&&_"))
    (:or (cel-logical t (second node) (third node) bindings "_||_"))
    (:bind
     (destructuring-bind (variable init body) (rest node)
       (cel-evaluate body (acons variable (cel-evaluate init bindings) bindings))))
    (:opt-map
     (destructuring-bind (flat target variable body) (rest node)
       (let ((optional (cel-evaluate target bindings)))
         (unless (cel-optional-p optional) (cel-fail "no such overload: optMap"))
         (if (cel-optional-present optional)
             (let ((value (cel-evaluate body (acons variable (cel-optional-value optional) bindings))))
               (if flat value (make-cel-optional :value value :present t)))
             optional))))
    (:comprehension
     (destructuring-bind (kind iterable variable body predicate second-variable) (rest node)
       (cel-comprehend kind
                       (cel-iteration-entries (cel-evaluate iterable bindings) second-variable)
                       variable body predicate second-variable bindings)))))

(defun cel-select-optional (operand field)
  "Select FIELD from a possibly optional OPERAND, giving an optional."
  (let ((inner (if (cel-optional-p operand) (cel-optional-value operand) operand))
        (live (or (not (cel-optional-p operand)) (cel-optional-present operand))))
    (if (and live (hash-table-p inner))
        (multiple-value-bind (value present) (cel-field-value inner field)
          (make-cel-optional :value value :present (and present t)))
        (make-cel-optional))))

(defun cel-index-optional (operand index)
  "Index a possibly optional OPERAND, giving an optional that is empty when out of range."
  (let ((inner (if (cel-optional-p operand) (cel-optional-value operand) operand))
        (live (or (not (cel-optional-p operand)) (cel-optional-present operand))))
    (cond ((not live) (make-cel-optional))
          ((cel-list-p inner)
           (let ((position (cel-numeric-value index)))
             (if (and position (< -1 position (length inner)))
                 (make-cel-optional :value (aref inner (truncate position)) :present t)
                 (make-cel-optional))))
          ((hash-table-p inner)
           (multiple-value-bind (value present) (gethash (cel-map-key-string index) inner)
             (make-cel-optional :value value :present (and present t))))
          (t (make-cel-optional)))))

(defun cel-run-budgeted (program bindings)
  "Evaluate PROGRAM under its per-call limit and any shared budget, charging what it used to that budget."
  (let ((shared *cel-shared-budget*))
    (when (and shared (<= (car shared) 0))
      (error 'cel-budget-exhausted
             :message "validation failed due to running out of cost budget, no further validation rules will be run"))
    (let* ((limit (if shared (min (car shared) +cel-evaluation-budget+) +cel-evaluation-budget+))
           (*cel-remaining-steps* limit))
      (unwind-protect
           (handler-case (cel-evaluate program bindings)
             (cel-cost-exceeded (condition)
               (if (and shared (< (car shared) +cel-evaluation-budget+))
                   (error 'cel-budget-exhausted
                          :message "validation failed due to running out of cost budget, no further validation rules will be run")
                   (error condition))))
        (when shared (decf (car shared) (- limit (max 0 *cel-remaining-steps*))))))))

(defun evaluate-cel-value (program bindings)
  "Run a compiled PROGRAM under a fresh per-call budget and any shared one, returning its value of any type."
  (cel-run-budgeted program bindings))

(defun evaluate-cel-condition (program bindings)
  "Run a compiled PROGRAM under a fresh per-call budget and any shared one, signaling on any runtime error."
  (let ((value (cel-run-budgeted program bindings)))
    (unless (cel-bool-p value) (cel-fail "expression did not evaluate to bool"))
    value))
