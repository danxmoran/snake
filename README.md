# Snake

Toy compiler and runtime from the Compilers class at Northeastern, targeting x86. Supports:

* Primitives:
    * Ints
    * Bools
* Heap-allocated structures:
    * Tuples (homogenous and heterogenous)
    * First-class lambda functions (with free-variable capture)
* Simple unary operators:
    * `print` to display values
    * `add1` and `sub1` on ints
    * `!` (not) on bools
    * `isnum`, `isbool`, and `istuple`
* Simple binary operators:
    * `==` on all types (reference equality on tuples and lambdas)
    * `+`, `-`, `*`, `<`, `>`, `<=`, and `=>` on ints
    * `&&` and `||` on bools
* Tuple getters and setters:
    * Expression-as-key for homogenous tuples
    * Constant-as-key for heterogenous tuples
* Conditional branching with `if`-`else`
* Local variable bindings with `let` (lexical scope)
* Simple typechecking, with Hindley-Milner type inference and support for explicit annotations
* Tail-call elimination
* Recursive and mutually-recursive lambda definitions
* Semispace gargage collection using Cheney's algorithm
* Simple optimizations:
    * Constant folding
    * Common subexpression elimination
    * Dead assignment elimination

See [`test.ml`](test.ml) for examples, along with examples of error-flagging.

## Setting up

First get required tools. On OSX:

```bash
$ brew install nasm ocaml opam
$ opam init
$ opam install batteries extlib ounit
```

Then build and run the regression suite, to be sure everything works:

```bash
$ make test && ./test
```

NOTE: A number of tests will be auto-skipped on OS X. They depend on Valgrind,
which still doesn't seem to work properly on Macs. Everything should work on
Ubuntu (provided valgrind is installed).

## Running

```bash
# Write a program:
$ cat <<EOF > input/my-program.snake
let fact = (lambda n:
    let rec tail_fact = (lambda m, acc:
      if (m == 0): acc
      else: tail_fact(m - 1, m * acc)) in
    tail_fact(n, 1)) in
  fact(10)
EOF
# Compile the program:
$ make output/my-program.run
# Run the program:
$ ./output/my-program.run
```
