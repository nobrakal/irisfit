## What is this about?

This directory contains files emulating the sequential mode (from
POPL'23) paper, based on the concurrent logic.

We illustrate how such an emulation can be used by deriving the
low-level interface of closures from a proof in the sequential mode.

* `wp_sequential.v` contains the main definitions.
* `interface.v` contains the interface between the sequential mode and
  the concurrent mode.
* `wp_closure.v` contains the proof of the low-level interface of closures _in the sequential
  mode_
* `wp_closure_conc.v` contains the proof of the low-level interface of
  closures _in the concurrent mode_ from the sequential proof.
