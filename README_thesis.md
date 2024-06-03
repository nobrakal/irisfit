## Correspondence with the the PhD thesis of Alexandre Moine, "Formal Verification of Heap Space Bounds under Garbage Collection"

All the development is made with Weakest Preconditions (WP) rather
than triples.
Code pointers are expressed with notation µ λ and application of terms
u and v as (u v).
Closure creation uses the syntax `mk_clo` and closure call the syntax
`call_clo`.
Code pointers must contain no locations. The syntax does not actually
forbid it, so a side-condition locs(t) = ∅ appears from time to time.
Moreover, while the paper assume a global constant `S` describing
the maximum size of the heap, we explicitly parameterize here
predicates and lemmas with a variable (ms:nat).
Last, the whole program logic is parameterized by a size function `sz:nat -> nat`,
named `size` in the thesis, associating to the number of fields of a block the number
of memory words it needs to be represented.
For our case studies, we use `sz = fun x -> x`.

### Figures

* Figure 3: file `language/syntax.v`
* Figure 4: file `language/head_semantics.v`.
We define a relation `head_step` that covers every case, except for
`fork`.
We then define a relation `head_step_conc`, which is either `fork`, or
a `head_step`.
* Figure 5: file `language/semantics.v`.
The `step` relation is named `atomic_step`.
* Figure 6: file `final/gc.v`.
* Figure 7: file `final/final_semantics.v`.
* Figure 8: file `final/final_semantics.v`.
The predicate `AllOut` is defined in file
`program_logic/wp_adequacy.v`.
* Figure 9: file `final/final_semantics.v`.
* Figure 10: in directory `program_logic/`
  + Consequence: file `wp_updates.v`, lemma `wp_consequence`.
  + Frame: file `wp.v`, lemma `wp_frame`.
* Figure 11: in file `program_logic/mapsto.v`
  + SizeOfPointsTo: `mapsto_extract_size_paper`
  + SizeOfConfront: `sizeof_confront`
* Figure 12: in file `program_logic/interp_base.v`
  + ZeroSC: `diamonds_zero`
  + SplitJoinSC: `diamond_split_iff`
* Figure 13: in file `program_logic/ph.v`
  + JoinPBHeap: `mapsfrom_join`
  + SplitPBHeap: `mapsfrom_split`
  + CovPBHeap: `mapsfrom_weak_paper`
* Figure 14: in directory `program_logic/`
  + FracPBThread: in file `pbt.v`, lemma `frac_pbt`
  + CovPBThread: in file `pbt.v`, lemma `pbt_approx`
  + TrimPBThread: in file `wp_clean`, lemma `supd_clean`
* Figure 15: in directory `program_logic/`
  + InsideNotOutside: in file `wp_protected.v`, lemma
    `inside_not_outside`
  + AddTemporary: in file `wp_clean.v`, lemma `tupd_clean_debt`
  + RemTemporary: in file `wp_clean.v`, lemma `debt_transfer`
  + TrimInside: in file `wp_protected.v`, lemma `inside_clean`
* Figure 16: in file `program_logic/more_interp.v`
  + TrimPBHeap: `mapsfrom_cleanup0`
  + DeadPBHeap: `confront_mapsfrom_dag`
  + DeadPBThread: `confront_pbt_dag`
  + NoDanglingRootOut: `no_dangling_pointer`
  + NoDanglingRootIn: `no_dangling_pointer_inside`
* FreeOne: in file `program_logic/wp_free.v`, lemma `interp_free`
* Figure 17: in directory `program_logic/`
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
* Figure 18: in directory `program_logic/`
  + Enter: in file `wp_protected.v`, lemma `wp_enter`
  + Exit: in file `wp_protected.v`, lemma `wp_exit`
  + LoadInside: in file `wp_load.v`, lemma `wp_load_inside`
  + StoreDead: in file `wp_store.v`, lemma `wp_store_dead`
  + CASSuccessDead: in file `wp_cas.v`, lemma `wp_cas_suc_dead`
* Figure 19: in file `program_logic/wp.v`
  + Bind: `wp_bind`
* Figure 20: in file `program_logic/wp.v`
  + SwitchMode: `wp_noclean`
  + BindNoTrim: `wp_bind_noclean`
* Figure 21: in file `program_logic/wp_free.v`
  + CloudEmpty: `ocloud_empty`
  + CloudAdd: `ocloud_add`
  + CloudFree: `supd_free_ocloud`
* Figure 22: in directory `final/`
  + NotStuckVal, NotStuckStep: `final_semantics.v`
  + GloballyNotStuck: `strong_safety.v`
  + Safe: `final_semantics.v`
  + Always: `temporal_logic.v`
  + PollAndAllocAreOut: `strong_safety.v`, definition `paao`
  + GCCanMakeEveryAllocFits: `strong_safety.v`, definition `gccmeaf`
  + StronglySafe: `strong_safety.v`
* Figure 23: file `final/temporal_logic.v`
* Figure 24:
  + InterleaveOblivious: file `final/final_semantics.v`, lemma `step_oblivious_alt`
  + NotStuckObliviousVal, NotStuckObliviousStep: file `program_logic/wp_adequacy.v`, definition `not_stuck`
* Figure 25: file `final/temporal_logic.v`
  + CrashOrHoldsNow, CrashOrHoldsAfter: definition `AfterAtMostWeak`
  + CrashOrEventually: definition `EventuallyWeak`
* Figure 26:
  + reducible: file `language/reducible.v`
  + wp: file `program_logic/wp.v`
* Figure 27: in folder `program_logic/`
  + store: file `mapsto.v`, definition `store_interp`
  + pbh: file `ph.v`, definition `ph_interp`
  + pbt: definition inlined within `interp`
  + protected: definition inlined within `interp`
  + spacecredits: definition inlined within `interp`
  + interp: file `interp_base.v`.
  The Coq definition of the assertion is less structured than the one presented in Figure 27.
  The mode is implemented with a boolean.
* Figure 28: in directory `program_logic/`
  + points-to: file `mapsto.v`
  + pointed-by-heap: file `ph.v`
  + pointed-by-thread: file `interp_base.v`
  + dagger: file `pbt.v`
  + space credits: file `interp_base.v`, definition `diamond`
  + sizeof: file `mapsto.v`
  + outside and inside: file `program_logic/interp_base.v`
* Figure 20: in directory `program_logic/`
  + Preserve: file `wp_adequacy.v`, lemma `wptp_steps`
  + Progress: file `wp_adequacy.v`, lemma `wp_not_stuck`
  + LiveSpace: file `wp_adequacy.v`, lemma `interp_reasonable`
  + InterpInit: files `interp_init.v` and `wp_adequacy.v`, combination of `interp_init` and `interp_bump`.
* Figure 30: file `language/closure.v`
* Figure 31: file `program_logic/wp_closure.v`
  + MkClo: `wp_mk_clo`
  + CallClo: `wp_call_clo`
  + ClofFree: `closure_free`
* Figure 32: file `program_logic/wp_closure.v`
* Figure 33: file `program_logic/wp_spec.v`
  + MkSpec: `wp_mk_spec`
  + CallSpec: `wp_call_spec`
  + SpecWeak: `spec_weak`
  + SpecFree: `spec_free`
* Figure 34: file `program_logic/wp_spec.v`
* Figure 35: file `program_logic/wpc.v`
  + BindWithSouvenir: lemma `wpc_bind`
  + AddSouvenir: lemma `wpc_context_singleton.v`
  + ForgetSouvenir: lemma `wpc_weak`
* Figure 36: file `wpc.v`
* Figure 37: file `examples/sequential/list_rev.v`
* Figure 38: file `examples/sequential/list.v`
* Figure 39: file `examples/sequential/cps/cps_append.v`
* Figure 40: in directory `examples/sequential/stack/`
  + Specifications: `stack.v`
  + List-based implementation: `stack_list.v`
  + Array-based implementation: `stack_chunk.v`
  + Functor: `stack_of_stacks.v`
  + Treiber-based implementation: `stack_treiber.v`
* Figure 41: file `examples/sequential/cyclist.v`
* Figure 42: file `examples/sequential/cyclist.v`
* Definition of atomic triples: `program_logic/wpc_logatom.v`
* Figure 43: file `examples/toolbox/faa.v`
* Figure 44: file `examples/counter/counter.v`
* Figure 45: file `examples/counter/counter.v`
* Figure 46: file `examples/toolbox/async_finish.v`
* Figure 47: file `examples/lockfree/treiber.v`
* Figure 48: file `examples/lockfree/treiber.v`
* Figure 49: in directory `examples/lockfree/michael_scott/`
  + Code: `ms_code.v`
  + QueueCreate: file `ms_create.v`
  + QueueEnqueue: file `ms_enqueue.v`
  + QueueDequeue: file `ms_dequeue.v`
  + QueueFree: file `ms_free.v`


## Lemmas

| Lemma | File                          | Name                                |
|-------|-------------------------------|-------------------------------------|
| 1     | `final/final_theorems.v`      | `EveryAllocFits_all_enabled`        |
| 2     | `final/final_theorems.v`      | `step_main_preserves_size`          |
| 3     | `final/strong_safety.v`       | `strongly_safe_globally_not_stuck'` |
| 4     | `final/temporal_logic.v`      | `always_mono`                       |
| 5     | `final/final_semantics.v`     | `main_to_oblivious`                 |
| 6     | `final/strong_safety.v`       | `not_stuck_oblivious_to_main`       |
| 7     | `final/gc.v`                  | `gc_non_size_increasing`            |
| 8     | `program_logic/linked.v`      | `live_heap_size`, by definition.    |
| 9     | `final/gc.v`                  | `gc_collect_2`                      |
| 10    | `final/strong_safety_addpp.v` | `addpp_preserves_safety`            |
| 11    | `final/final_theorems.v`      | `strongifiy_liveness`               |
| 12    | `final/liveness_addpp.v`      | `weak_liveness_addpp`               |

## Theorems

| Theorem | File                          | Name                |
|---------|-------------------------------|---------------------|
| 1       | `final/strong_safety.v`       | `wp_strong_safety`  |
| 2.1     | `final/final_theorems.v`      | `wp_safety_addpp`   |
| 2.2     | `final/final_theorems.v`      | `wp_liveness_addpp` |
| 3 and 5 | `program_logic/wp_adequacy.v` | `wp_adequacy_core`  |

Theorem 4 can be found at [iris doc](https://plv.mpi-sws.org/coqdoc/iris/iris.base_logic.lib.fancy_updates.html#step_fupdN_soundness_gen), [permalink](https://archive.softwareheritage.org/swh:1:cnt:d521738fea793efa8097e7d27fe4111134de005c;origin=https://gitlab.mpi-sws.org/iris/iris;visit=swh:1:snp:a3b01e150fc67626d9c4082c0b205863017382c6;anchor=swh:1:rev:5ae024071a99434487cc0f517f3b19597081c01b;path=/iris/base_logic/lib/fancy_updates.v;lines=275)

## Definitions

| Definition | File                          | Name             | Note                                                |
|------------|-------------------------------|------------------|-----------------------------------------------------|
| 1          | `final/anf.v`                 | `weak_anf`       | Only ANF at call sites                              |
| 2          | `final/addpp.v`               | `addpp`          |                                                     |
| 3          | `program_logic/linked.v`      | `live_heap_size` |                                                     |
| 4          | N/A                           | N/A              | Always inlined                                      |
| 5          | `spacelang/predecessors.v`    | `freed`          |                                                     |
| 6          | `language/successors.v`       | `closed`         |                                                     |
| 7          | `program_logic/linked.v`      | `linked`         | With an additional constraint on domains            |
| 8          | `program_logic/interp_base.v` | `debt`           | With an additional constraint on domains            |
| 9          | `spacelang/predecessors.v`    | `invariant`      |                                                     |
| 10         | `program_logic/tied.v`        | `tied`           | Without the constraint on consistent                |
| 11         | `program_logic/roots_inv.v`   | `roots_inv`      | With additional constraints on domains              |
| 12         | `lib/fracset.v`               | `fracset`        | Specialization of a more general `nfrac` definition |
| 13         | `program_logic/interp_base.v` | `interpGS`       | As a typeclass                                      |
