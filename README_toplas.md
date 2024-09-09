## Correspondence with the Paper: Will it Fit? Verifying Heap Space Bounds of Concurrent Programs under Garbage Collection with Separation Logic

The development is made with Weakest Preconditions (WP) rather
than triples.
Code pointers are expressed with notation µ λ and application of terms
u and v as (u v).
Closure creation uses the syntax `mk_clo` and closure call the syntax
`call_clo`.
Code pointers must contain no locations. The syntax does not actually
forbid it, so a side-condition locs(t) = ∅ appears from time to time.

### Figures

* Figure 4: file `language/syntax.v`
* Figure 5: file `language/head_semantics.v`\
We define a relation `head_step` that covers every case, except for
`fork`.
We then define a relation `head_step_conc`, which is either `fork`, or
a `head_step`.
* Figure 6: file `language/semantics.v`
The `step` relation is named `atomic_step`
* Figure 7: file `final/gc.v`
* Figure 8: file `final/final_semantics.v`
* Figure 9: file `language/semantics.v`
* Figure 10: file `final/final_semantics.v`
The predicate `AllOut` is defined in file
`program_logic/wp_adequacy.v`.
* Figure 11: file `final/final_semantics.v`
* Figure 12: file `final/semantics_with_growing_store.v`
* Figure 13: directory `program_logic/`
  + Consequence: file `wp_updates.v`: `wp_consequence`
  + Frame: file `wp.v`: `wp_frame`
* Figure 14: file `program_logic/mapsto.v`
  + SizeOfPointsTo: `mapsto_extract_size_paper`
  + SizeOfConfront: `sizeof_confront`
* Figure 15: file `program_logic/interp_base.v`
  + ZeroSC: `diamonds_zero`
  + SplitJoinSC: `diamond_split_iff`
* Figure 16: file `program_logic/ph.v`
  + JoinPBHeap: `mapsfrom_join`
  + SplitPBHeap: `mapsfrom_split`
  + CovPBHeap: `mapsfrom_weak_paper`
* Figure 17: directory `program_logic/`
  + FracPBThread: file `pbt.v`: `frac_pbt`
  + CovPBThread: file `pbt.v`: `pbt_approx`
  + TrimPBThread: file `wp_clean`: `supd_clean`
* Figure 18: directory `program_logic/`
  + InsideNotOutside: file `wp_protected.v`:
    `inside_not_outside`
  + AddTemporary: file `wp_clean.v`: `tupd_clean_debt`
  + RemTemporary: file `wp_clean.v`: `debt_transfer`
  + TrimInside: file `wp_protected.v`: `inside_clean`
* Figure 19: file `program_logic/more_interp.v`
  + TrimPBHeap: `mapsfrom_cleanup0`
  + DeadPBHeap: `confront_mapsfrom_dag`
  + DeadPBThread: `confront_pbt_dag`
  + NoDanglingRootOut: `no_dangling_pointer`
  + NoDanglingRootIn: `no_dangling_pointer_inside`
* FreeOne: file `program_logic/wp_free.v`: `interp_free`
* Figure 20: directory `program_logic/`
  + IfTrue, IfFalse: file `wp.v`: `wp_if`
  + LetVal: file `wp.v`: `wp_let_val`
  + Prim: file `wp_call_prim.v`: `wp_call_prim`
  + CallPtr : file `wp_call.v`: `wp_call`
  + Poll: file `wp_poll.v`: `wp_poll`
  + Alloc: file `wp_alloc.v`: `wp_alloc`
  + Load: file `wp_load.v`: `wp_load`
  + Store: file `wp_store.v`: `wp_store`
  + CASSuccess: file `wp_cas.v`: `wp_cas_suc`
  + CASFailure: file `wp_cas.v`: `wp_cas_fail`
  + Fork: file `wp_fork.v`: `wp_fork`
  + Val: file `wp.v`: `wp_val`
* Figure 21: directory `program_logic/`
  + Enter: file `wp_protected.v`: `wp_enter`
  + Exit: file `wp_protected.v`: `wp_exit`
  + LoadInside: file `wp_load.v`: `wp_load_inside`
  + StoreDead: file `wp_store.v`: `wp_store_dead`
  + CASSuccessDead: file `wp_cas.v`: `wp_cas_suc_dead`
* Figure 22: file `program_logic/wp.v`
  + Bind: `wp_bind`
* Figure 23: file `program_logic/wp.v`
  + SwitchMode: `wp_noclean`
  + BindNoTrim: `wp_bind_noclean`
* Figure 24: file `program_logic/wp_free.v`
  + CloudEmpty: `ocloud_empty`
  + CloudAdd: `ocloud_add`
  + CloudFree: `supd_free_ocloud`
* Section 7 and Figure 25: file `examples/toolbox/smallex.v`
* Figure 26: file `final/final_semantics.v`
* Figure 27: file `final/temporal_logic.v`
* Figure 28: all these definitions are inlined.
* Figure 29: file `program_logic/wp_adequacy.v`
  + NotStuckObliviousVal, NotStuckObliviousStep: definition `not_stuck`
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
  + BindWithSouvenir: `wpc_bind`
  + AddSouvenir: `wpc_context_singleton.v`
  + ForgetSouvenir: `wpc_weak`
  + EmptySouvenir: `wpc_wp_empty`
* Figure 36: file `wpc.v`
* Definition of atomic triples: `program_logic/wpc_logatom.v`
* Figure 37: file `examples/toolbox/faa.v`
* Figure 38: file `examples/counter/counter.v`
* Figure 39: file `examples/toolbox/async_finish.v`
* Figure 40: file `examples/lockfree/treiber.v`

## Lemmas and Theorems

| Result          | File                                   | Name                          |
|-----------------|----------------------------------------|-------------------------------|
| Lemma 4.1       | `final/final_theorems.v`               | `EveryAllocFits_all_enabled`  |
| Lemma 4.2       | `final/final_theorems.v`               | `step_default_preserves_size` |
| Lemma 4.3       | `final/semantics_with_growing_store.v` | `rtc_growing_to_default`      |
| Lemma 4.4       | `final/semantics_with_growing_store.v` | `rtc_default_to_growing`      |
| Lemma 4.5       | `final/semantics_with_growing_store.v` | `rtc_growing_grows`           |
| Theorem 8.1     | `final/final_theorems.v`               | `wp_safety`                   |
| Theorem 8.2 (1) | `final/final_theorems.v`               | `wp_safety_addpp`             |
| Theorem 8.2 (2) | `final/final_theorems.v`               | `wp_liveness_addpp`           |
| Theorem 8.3 (1) | `final/semantics_with_growing_store.v` | `wp_safety_addpp_growing`     |
| Theorem 8.3 (2) | `final/semantics_with_growing_store.v` | `wp_liveness_addpp_growing`   |
| Theorem 8.3 (3) | `final/semantics_with_growing_store.v` | `wp_bound_is_preserved`       |
| Theorem 8.4     | `program_logic/wp_adequacy.v`          | `wp_adequacy_core`            |
