From irisfit.program_logic Require Import interp_base.

(* Here, we specify the [sz] parameter of [interpGS] to be [fun x => x],
   the identity function.
   Hence, we verify our examples in the special case where a block with [n] fields
   is represented in memory by [n] memory words.
 *)
Notation interpGS0 Σ := (interpGS (fun x => x) Σ).
