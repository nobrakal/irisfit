# Will it Fit?

This Coq project includes:

* LambdaFit, a deeply-embedded imperative and concurrent
  lambda-calculus equipped with tracing garbage collection.
* IrisFit, an [Iris](https://iris-project.org/)-based Separation Logic
  for proving heap-space bounds of LambdaFit programs.

## Setup & build

This project needs [opam](https://opam.ocaml.org/doc/Install.html) to install dependencies.
You can run `./setup.sh` to create a local opam switch with correct
dependencies, and build the project.
Please allow at least 30 minutes for the installation and build to
run.

To manually build the project, run `make` or `dune build`.

## Architecture

The architecture is as follows:

* `lib/` for signed multisets and possibly null fractions.
* `spacelang/` for (almost not modified) files from
  [SpaceLang](https://gitlab.inria.fr/fpottier/diamonds/), taken with
  the authorization of the authors.
* `language/` for the syntax & "oblivious" semantics of the
  language.
* `final/` for the "main" semantics and associated results.
* `program_logic/` for program logic.
* `sequential/` for the emulation of the sequential mode presented
in [A High-Level Separation Logic for Heap Space under Garbage Collection](https://doi.org/10.5281/zenodo.7129302).
* `examples/` for various examples.

## Links with Publications

We present a correspondence between this formalization and related
papers.

* For the TOPLAS paper "Will it Fit? Verifying Heap Space Bounds of
  Concurrent Programs under Garbage Collection",
  see `README_toplas.md`.
* For the PhD thesis of Alexandre Moine, "Formal Verification of Heap
  Space Bounds under Garbage Collection",
  see `README_thesis.md`.

## ProofGeneral

NB: There is a hack to work with ProofGeneral.
We have a dumb `src/_CoqProject` which make visible the files
produced by dune.

See issue: https://github.com/ProofGeneral/PG/issues/477
