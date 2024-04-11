# IrisFit

An Iris instance for establishing heap space bounds of concurrent
programs in the presence of garbage collection.

## Setup & build

This project needs [opam](https://opam.ocaml.org/doc/Install.html) to install dependencies.
You can run `./setup.sh` to create a local opam switch with correct
dependencies, and build the project.
Please allow at least 30 minutes for the installation and build to
run.

After the setup is done,
you can manually build the project with `make` or `dune build`.

## Architecture

The architecture is as follows:

* `lib/` for signed multisets and possibly null fractions.
* `spacelang/` for (almost not modified) files from
  [SpaceLang](https://gitlab.inria.fr/fpottier/diamonds/), taken with
  the authorization of the authors.
* `language/` for the syntax of LambdaFit and the "oblivious" semantics of the
  language.
* `final/` for the "default" semantics of LambdaFit and associated results.
* `program_logic/` for program logic.
* `sequential/` for the sequential mode presented
  in [A High-Level Separation Logic for Heap Space under Garbage
  Collection](https://dl.acm.org/doi/10.1145/3571218), which we emulate
  in IrisFit.
* `examples/` for various examples.

## Link with the Paper

All the development is made with Weakest Preconditions (WP) rather
than triples.
Code pointers are expressed with notation µ λ and application of terms
u and v as (u v).
Closure creation uses the syntax `mk_clo` and closure call the syntax
`call_clo`.
Code pointers must contain no locations. The syntax does not actually
enforce this constraint, so a side-condition locs(t) = ∅ appears from
time to time.
Moreover, while the paper assumes a global constant `S` describing the
maximum size of the heap, we explicitly parameterize here predicates
and lemmas with a variable (ms:nat).

### Figures

* Figure 3 (LambdaFit: syntax):
file `language/syntax.v`
* Figure 4 (The head reduction relation):
file `language/head_semantics.v`
We define a relation `head_step` that covers every case, except for
`fork`
We then define a relation `head_step_conc`, which is either `fork`, or
a `head_step`
* Figure 5 (The step relation):
file `language/semantics.v`
The `step` relation is named `atomic_step`
* Figure 6 (The garbage collection relation):
file `final/gc.v`
* Figure 7 (The action relation):
file `final/final_semantics.v`
* Figure 8 (Enabled actions (and auxiliary predicates)):
file `final/final_semantics.v`
The predicate `AllOut` is defined in file
`program_logic/wp_adequacy.v`
* Figure 9 (The main reduction relation):
file `final/final_semantics.v`
* Figure 10 (Structural reasoning rules):
directory `program_logic/`
  + Consequence: file `wp_updates.v`, lemma `wp_consequence`
  + Frame: file `wp.v`, lemma `wp_frame`
* Figure 11 (Reasoning rules of the “sizeof ” assertion):
file `program_logic/mapsto.v`
  + SizeOfPointsTo: `mapsto_extract_size_paper`
  + SizeOfConfront: `sizeof_confront`
  + SizeOfPersist: `sizeof_persist`
* Figure 12 (Reasoning rules for space credits):
file `program_logic/interp_base.v`
  + ZeroSC: `diamonds_zero`
  + SplitJoinSC: `diamond_split_iff`
* Figure 13 (Reasoning rules for the pointed-by-heap assertion):
file `program_logic/ph.v`
  + JoinPBHeap: `mapsfrom_join`
  + SplitPBHeap: `mapsfrom_split`
  + CovPBHeap: `mapsfrom_weak_paper`
* Figure 14 (Reasoning rules for the pointed-by-thread assertion):
directory `program_logic/`
  + FracPBThread: in file `pbt.v`, lemma `frac_pbt`
  + CovPBThread: in file `pbt.v`, lemma `pbt_approx`
  + TrimPBThread: in file `wp_clean`, lemma `supd_clean`
* Figure 15 (Reasoning rules for “inside” and “outside” assertions):
directory `program_logic/`
  + InsideNotOutside: in file `wp_protected.v`, lemma
    `inside_not_outside`
  + AddTemporary: in file `wp_clean.v`, lemma `tupd_clean_debt`
  + RemTemporary: in file `wp_clean.v`, lemma `debt_transfer`
  + TrimInside: in file `wp_protected.v`, lemma `inside_clean`
* Figure 16 (Reasoning rules for deallocation witnesses):
file `program_logic/more_interp.v`
  + CleanPBHeap: `mapsfrom_cleanup0`
  + DeadPBHeap: `confront_mapsfrom_dag`
  + DeadPBThread: `confront_pbt_dag`
  + NoDanglingRootOut: `no_dangling_pointer`
  + NoDanglingRootIn: `no_dangling_pointer_inside`
  + DeadPersist: `persistent_dagger`
* FreeOne: in file `program_logic/wp_free.v`, lemma `interp_free`
* Figure 17 (Syntax-directed reasoning rules, without protected-section-specific rules and without Bind):
directory `program_logic/`
  + IfTrue, IfFalse: in file `wp.v`, lemma `wp_if`
  + LetVal: in file `wp.v`, lemma `wp_let_val`
  + Prim: in file `wp_call_prim.v`, lemma `wp_call_prim`
  + CallPtr : in file `wp_call.v`, lemma `wp_call`
  + Poll: in file `wp_poll.v`, lemma `wp_poll`
  + Alloc: in file `wp_alloc.v`, lemma `wp_alloc`
  + Load: in file `wp_load.v`, lemma `wp_load`
  + Store: in file `wp_store.v`, lemma `wp_store`
  + CASSuccess: in file `wp_cas.v`, lemma `wp_cas_suc`
  + CASFailure: in file `wp_cas.v`, lemma `wp_cas_fail`
  + Fork: in file `wp_fork.v` lemma `wp_fork`
  + Val: in file `wp.v`, lemma `wp_val`
* Figure 18 (Reasoning rules: protected-section-specific rules):
directory `program_logic/`
  + Enter: in file `wp_protected.v`, lemma `wp_enter`
  + Exit: in file `wp_protected.v`, lemma `wp_exit`
  + LoadInside: in file `wp_load.v`, lemma `wp_load_inside`
  + StoreDead: in file `wp_store.v`, lemma `wp_store_dead`
  + CASSuccessDead: in file `wp_cas.v`, lemma `wp_cas_suc_dead`
* Figure 19 (Reasoning rules: the Bind rule):
file `program_logic/wp.v`
  + Bind: `wp_bind`
* Figure 20 (Reasoning rules: additional mode-specific rules):
file `program_logic/wp.v`
  + SwitchMode: `wp_noclean`
  + BindNoTrim: `wp_bind_noclean`
* Figure 21 (Reasoning rules: logical deallocation):
file `program_logic/wp_free.v`
  + CloudEmpty: `ocloud_empty`
  + CloudAdd: `ocloud_add`
  + CloudFree: `supd_free_ocloud`
* Figure 22 (Predicates used in the statement of the safety theorem):
directory `final/`
  + NotStuckVal, NotStuckStep: `final_semantics.v`
  + Safe: `final_semantics.v`
  + Always: `temporal_logic.v`
* Figure 23 (Predicates used in the statement of the liveness theorem):
file `final/temporal_logic.v`
* Figure 24 (The oblivious reduction relation and associated predicates):
  + InterleaveOblivious: file `final/final_semantics.v`, lemma `step_oblivious_alt`
  + NotStuckObliviousVal,NotStuckObliviousStep: file `program_logic/wp_adequacy.v`, definition `not_stuck`
* Figure 25 (Closures: macros for closure construction and invocation):
file `language/closure.v`
* Figure 26 (Closures: low-level API):
file `program_logic/wp_closure.v`
  + MkClo: `wp_mk_clo`
  + CallClo: `wp_call_clo`
  + CloFree: `closure_free`
  + CloPersist: `Closure_persistent`
* Figure 27 (Definition of the predicate Closure):
file `program_logic/wp_closure.v`
* Figure 28 (Closures: high-level API):
file `program_logic/wp_spec.v`
  + MkSpec: `wp_mk_spec`
  + CallSpec: `wp_call_spec`
  + SpecWeak: `spec_weak`
  + SpecFree: `spec_free`
  + SpecPersist: `Spec_persistent`
* Figure 29 (Definition of the predicate Spec):
file `program_logic/wp_spec.v`
* Figure 30 (Key reasoning rules for triples with souvenir):
file `program_logic/wp_spec.v`
  + BindWithSouvenir: lemma `wpc_bind`
  + AddSouvenir: lemma `wpc_context_singleton.v`
  + ForgetSouvenir: lemma `wpc_weak`
* Figure 31 (Definition of triples with souvenir):
file `wpc.v`
* Definition of atomic triples:
file `program_logic/wpc_logatom.v`
* Figure 32 (Code and specification of fetch-and-add):
file `examples/toolbox/faa.v`
* Figure 33 (Code and specification of a concurrent monotonic counter):
file `examples/counter/counter.v`
* Figure 34 (Code and specification of an async/finish library):
file `examples/toolbox/async_finish.v`
* Figure 35 (Specification of Treiber’s Stack):
file `examples/lockfree/treiber.v`

## Lemmas and Theorems

| Result          | File                          | Name                         |
|-----------------|-------------------------------|------------------------------|
| Lemma 4.1       | `final/final_theorems.v`      | `EveryAllocFits_all_enabled` |
| Lemma 4.2       | `final/final_theorems.v`      | `step_main_preserves_size`   |
| Theorem 7.1     | `final/final_theorems.v`      | `wp_safety`                  |
| Theorem 7.2 (1) | `final/final_theorems.v`      | `wp_safety_addpp`            |
| Theorem 7.2 (2) | `final/final_theorems.v`      | `wp_liveness_addpp`          |
| Theorem 7.3     | `program_logic/wp_adequacy.v` | `wp_adequacy_core`           |

## ProofGeneral

NB: There is a hack to work with ProofGeneral.
We have a dumb `src/_CoqProject` which make visible the files
produced by dune.

See issue: https://github.com/ProofGeneral/PG/issues/477
