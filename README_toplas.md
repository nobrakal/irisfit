## Correspondence with the Paper: Will it Fit? Verifying Heap Space Bounds of Concurrent Programs under Garbage Collection with Separation Logic

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
  + Safe: `final_semantics.v`
  + Always: `temporal_logic.v`
* Figure 23: file `final/temporal_logic.v`
* Figure 24:
  + InterleaveOblivious: file `final/final_semantics.v`, lemma `step_oblivious_alt`
  + NotStuckObliviousVal,NotStuckObliviousStep: file `program_logic/wp_adequacy.v`, definition `not_stuck`
* Figure 25: file `language/closure.v`
* Figure 26: file `program_logic/wp_closure.v`
  + MkClo: `wp_mk_clo`
  + CallClo: `wp_call_clo`
  + ClofFree: `closure_free`
* Figure 27: file `program_logic/wp_closure.v`
* Figure 28: file `program_logic/wp_spec.v`
  + MkSpec: `wp_mk_spec`
  + CallSpec: `wp_call_spec`
  + SpecWeak: `spec_weak`
  + SpecFree: `spec_free`
* Figure 29: file `program_logic/wp_spec.v`
* Figure 30: file `program_logic/wpc.v`
  + BindWithSouvenir: lemma `wpc_bind`
  + AddSouvenir: lemma `wpc_context_singleton.v`
  + ForgetSouvenir: lemma `wpc_weak`
* Figure 31: file `wpc.v`
* Definition of atomic triples: `program_logic/wpc_logatom.v`
* Figure 32: file `examples/toolbox/faa.v`
* Figure 33: file `examples/counter/counter.v`
* Figure 34: file `examples/toolbox/async_finish.v`
* Figure 35: file `examples/lockfree/treiber.v`

## Lemmas and Theorems

| Result          | File                          | Name                         |
|-----------------|-------------------------------|------------------------------|
| Lemma 4.1       | `final/final_theorems.v`      | `EveryAllocFits_all_enabled` |
| Lemma 4.2       | `final/final_theorems.v`      | `step_main_preserves_size`   |
| Theorem 7.1     | `final/final_theorems.v`      | `wp_safety`                  |
| Theorem 7.2 (1) | `final/final_theorems.v`      | `wp_safety_addpp`            |
| Theorem 7.2 (2) | `final/final_theorems.v`      | `wp_liveness_addpp`          |
| Theorem 7.3     | `program_logic/wp_adequacy.v` | `wp_adequacy_core`           |
