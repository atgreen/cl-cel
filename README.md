# cl-cel

`cl-cel` is a bounded Common Expression Language compiler and evaluator for
Common Lisp. It compiles expressions once, checks declared variables and
function overloads, and evaluates them against caller-owned bindings with a
deterministic cost limit.

The built-in library includes conversions, strings, regular expressions,
lists, sets, optionals, timestamps, durations, named time zones, quantities,
URLs, IP addresses, CIDRs, semantic versions, and portable string formats.

## Installation

Install `cl-re2` and the dependencies locked in `ocicl.csv`, then make both
ASDF systems visible before loading `cl-cel`. During development with sibling
checkouts, a deterministic invocation is:

```sh
CL_SOURCE_REGISTRY="$PWD/../cl-re2//:$PWD//" \
  sbcl --noinform --non-interactive \
  --eval '(require "asdf")' \
  --eval '(asdf:test-system "cl-cel")'
```

`cl-re2` is a normal public system dependency; it is not copied into this
repository or fetched implicitly by project code.

## Usage

```lisp
(asdf:load-system :cl-cel)

(cl-cel:with-cel-environment (:variables '("address"))
  (let ((condition
          (cl-cel:compile-cel-condition
           "address in ['127.0.0.1', '::1']")))
    (cl-cel:evaluate-cel-condition
     condition
     '(("address" . "127.0.0.1")))))
```

See `examples/basic.lisp` for a complete example using only the public API.

## Design

- Parsing, static checking, and evaluation are separate phases.
- `with-cel-environment` defines the variables and overload tables visible at
  compile time; evaluated values remain caller-owned.
- Evaluation has a configurable operation budget and signals
  `cel-cost-exceeded` when exhausted.
- Regular expressions use `cl-re2` for predictable matching behavior.
- Named time zones are read from standard TZif files and cached safely.

## Testing

```sh
CL_SOURCE_REGISTRY=~/git/cl-re2//:~/git/cl-cel// \
  sbcl --noinform --non-interactive \
       --eval '(require :asdf)' \
       --eval '(asdf:test-system :cl-cel)'
```

## Author

Anthony Green <green@moxielogic.com>

## License

MIT. See `LICENSE`.
