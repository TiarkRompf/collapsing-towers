# Collapsing Towers of Interpreters

This is the artifact package for the corresponding POPL 2018 paper ([PDF](http://lampwww.epfl.ch/~amin/pub/collapsing-towers.pdf)).

## Abstract

Given a tower of interpreters, i.e., a sequence of multiple interpreters interpreting one another as input programs, we aim to collapse this tower into a compiler that removes all interpretive overhead and runs in a single pass. In the real world, a use case might be Python code executed by an x86 runtime, on a CPU emulated in a JavaScript VM, running on an ARM CPU. Collapsing such a tower can not only exponentially improve runtime performance, but also enable the use of base-language tools for interpreted programs, e.g., for analysis and verification. In this paper, we lay the foundations in an idealized but realistic setting.

We present a multi-level lambda calculus that features _staging constructs_ and _stage polymorphism_: based on runtime parameters, an evaluator either executes source code (thereby acting as an interpreter) or generates code (thereby acting as a compiler). We identify stage polymorphism, a programming model from the domain of high-performance program generators, as the key mechanism to make such interpreters compose in a collapsible way.

We present Pink, a meta-circular Lisp-like evaluator on top of this calculus, and demonstrate that we can collapse arbitrarily many levels of self-interpretation, including levels with semantic modifications. We discuss several examples: compiling regular expressions through an interpreter to base code, building program transformers from modified interpreters, and others. We develop these ideas further to include reflection and reification, culminating in Purple, a reflective language inspired by Brown, Blond, and Black, which realizes a conceptually infinite tower, where every aspect of the semantics can change dynamically. Addressing an open challenge, we show how user programs can be compiled and recompiled under user-modified semantics.

## Challenge

We are concerned with the following challenge: given a sequence of programming
languages `L_0,...,L_n` and interpreters for `L_i+1` written in `L_i`, derive
a compiler from `L_n` to `L_0`. This compiler should be one-pass, and it should be
optimal in the sense that the translation removes all interpretive overhead of the
intermediate languages.

## Overview

We first summarize the contents of the artifact package and provide instructions
how to run the test cases and examples. Afterwards, we detail the relation between
the paper and the code in this package.

# Contents

## Multi-level core language λ↑↓ in PLT Redex

### Code
* __[`core.rkt`](core.rkt)__ defines the multi-level core language λ↑↓ as a PLT Redex model, using a small-step operational semantics.
* __[`core-exs.rkt`](core-exs.rkt)__ defines examples and test cases to exercise the semantics.

### Run
Run `core-exs.rkt` in [DrRacket](https://racket-lang.org/).

## Pink in Scala

### Code
* __[`base.scala`](base.scala)__ defines the multi-level core language λ↑↓ as a definitional interpreter in Scala.
* __[`lisp.scala`](lisp.scala)__ defines a LISP-like front end.
* __[`pink.scala`](pink.scala)__ defines meta-circular stage-parametric interpreters for Pink.
* __[`matcher.scala`](matcher.scala)__ defines a regular expression matcher on top of LISP-like front end & Pink.
* __[`bench.scala`](bench.scala)__ defines a microbenchmark for comparing evaluation and compilation in Pink.

### Run
Run `sbt run` using Scala's [SBT](http://www.scala-sbt.org/).

Modify [`test-main.scala`](test-main.scala) to run more or fewer tests and benchmarks.

## Pink in Scheme
available at [namin/pink](https://github.com/namin/pink), here referred to as `pink-scheme`.

## Purple
available at [namin/lms-black](https://github.com/namin/lms-black), here referred to as `purple`.

# Relation to the Paper ([PDF](http://lampwww.epfl.ch/~amin/pub/collapsing-towers.pdf))

In the following, we detail how sections, figures, and claims from the paper are reflected in the artifact package.

## 3 Multi-Level Core Language λ↑↓
* __Fig. 1__ corresponds to PLT Redex development in [`core.rkt`](core.rkt).
* __Fig. 2__ is a subset of the Scala development in [`base.scala`](base.scala). The alternative Scheme development is at [`pink-scheme/base.scm`](https://github.com/namin/pink/blob/master/base.scm).
* __Fig. 3__ and other such examples are in the PLT Redex examples in [`core-exs.rkt`](core-exs.rkt).
### 3.1 A Lisp-Like Front-End
* This section uses Scheme syntax for illustration. The more extensive matcher is developed in [`matcher.scala`](matcher.scala).
### 3.2 Stage Polymorphism
* Again the specific example used here in Scheme syntax is for illustration, but the technique of abstracting over the stage with via η-expansion is used extensively, for example in [`pink.scala`](pink.scala).
## 4 Building and Collapsing Towers
* Variants of __Fig. 4__ are in [`pink.scala`](pink.scala) and [`pink-scheme/pink.scm`](https://github.com/namin/pink/blob/master/pink.scm).
* Examples of collapsing towers are in [`pink.scala`](pink.scala) and [`pink-scheme/pink-tests.scm`](https://github.com/namin/pink/blob/master/pink-tests.scm).
* __Fig. 5__ is developed in [`matcher.scala`](matcher.scala) and [`pink-scheme/matcher.scm`](https://github.com/namin/pink/blob/master/matcher.scm).
* __Fig. 6__ is extracted from outputs of examples in [`pink.scala`](pink.scala). Search for "confirming Figure 6", which occurs three times for the left, middle and right columns of the figure.
### 4.1 Correctness and Optimality
* The `testCorrectnessOptimality()` method in [`pink.scala`](pink.scala) directly follows the examples in this section.
### 4.2 Deriving Translators from Heterogeneous Towers
#### 4.2.1 Instrumenting Execution
* The `testInstrumentation()` method in [`pink.scala`](pink.scala) demonstrates the example of this section.
* The further tests deriving translators in [`matcher.scala`](matcher.scala) demonstrates how translators and translator generators can be derived.
#### 4.2.2 CPS Transform
* The object `Pink_CPS` in [`pink.scala`](pink.scala) shows a range of CPS-related transformations.
## 5 Towards Reflective Towers
### 5.1 Execute-at-Metalevel
#### 5.1.2 Modifying the Tower Structure
* The `testEM()` method in the object `Pink` in [`pink.scala`](pink.scala) demonstrates the example of this section.
#### 5.1.3 Language Extensions in User Code
* The `testEM()` method in the object `Pink_CPS` in [`pink.scala`](pink.scala) demonstrates the example of this section.
### 5.2 Compiling under Persistent Semantic Modifications
* The object `Pink_clambda`  in [`pink.scala`](pink.scala) shows how to implement and exercise `clambda` in Pink.
## 6 Purple: Reflection à la Black
* The example shown as a starting point here is in [`purple/src/test/.../em.scala`](https://github.com/namin/lms-black/blob/master/src/test/scala/lms/black/em.scala).
* The Purple development [source](https://github.com/namin/lms-black/tree/master/src/main/scala/lms/black) consists of the stage-polymorphic base interpreter functions ([`eval.scala`](https://github.com/namin/lms-black/blob/master/src/main/scala/lms/black/eval.scala)), the LMS instantiation([`stage.scala`](https://github.com/namin/lms-black/blob/master/src/main/scala/lms/black/stage.scala)), and various utilities including a REPL. The REPL is automatically imported with `sbt console` from the top-level [`purple`](https://github.com/namin/lms-black) directory and can be invoked with `ev`, e.g. `ev("(+ 1 1)")`.
## 7 Purple / Black Examples
* The Purple examples are collected as [tests](https://github.com/namin/lms-black/tree/master/src/test/scala/lms/black) in [the Purple development](https://github.com/namin/lms-black).
## 8 from λ↑↓ to LMS
### 8.1 Stage Polymorphism with Type Classes
* The `trait Ops[R[_]]` is defined in [`purple/src/main/.../eval.scala`](https://github.com/namin/lms-black/blob/master/src/main/scala/lms/black/eval.scala). The identity instantiation is defined as `implicit object OpsNoRep extends Ops[NoRep]` in the same file.
* The LMS instantiation is defined as `implicit object OpsRep extends Ops[Rep]` in [`purple/src/main/.../stage.scala`](https://github.com/namin/lms-black/blob/master/src/main/scala/lms/black/stage.scala).
## 9 A Sketch of Purple's Implementation
* Most of the code from this section is in [`purple/src/main/.../eval.scala`](https://github.com/namin/lms-black/blob/master/src/main/scala/lms/black/eval.scala).
## 10 Benchmarks
* The benchmarks for Pink are collected in [`bench.scala`](bench.scala) and ran as part of `sbt run`. The benchmarks for Purple are collected in [`purple/src/test/.../bench.scala`](https://github.com/namin/lms-black/blob/master/src/test/scala/lms/black/bench.scala) and ran with `sbt test:run` from the the top-level [`purple`](https://github.com/namin/lms-black) directory. The benchmark for the original Black is in [`black/examples/bench.blk`](https://github.com/namin/black/blob/bench/examples/bench.blk) -- the number of iterations is only 10'000 instead of 100'000 and it is scaled appropriately when reporting the results. The Black microbenchmark is run in Chez Scheme from the top-level Black directory by `(load "init.scm") (load "examples/bench.blk")`. The Black microbenchmark requires adding the primitive `real-time` function from Chez Scheme to Black, which is done in a [branch `bench`](https://github.com/readevalprintlove/black/compare/master...namin:bench?expand=1).
