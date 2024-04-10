From stdpp Require Export binders base.
From irisfit.language Require Export language.

(* From https://plv.mpi-sws.org/coqdoc/iris/iris.bi.weakestpre.html *)
Declare Scope tm_scope.
Delimit Scope tm_scope with T.
Bind Scope tm_scope with tm.

Declare Scope val_scope.
Delimit Scope val_scope with V.
Bind Scope val_scope with val.

(* ------------------------------------------------------------------------ *)

(* This allows opening the value scope after [BBlock]. *)

Notation BBlock vs :=
  (BBlock (vs%V)).

(* ------------------------------------------------------------------------ *)

(* Notations for values. *)

(* These notations can produce ASTs of type [val] and [tm], and are active
   in the scopes [%V] and [%T]. *)

(* [()] denotes the unit value. *)

Notation "()" :=
  (val_unit)
: val_scope.

(* [#l] denotes the memory location [l], viewed as a value. *)

Notation "# l" :=
  (val_loc l%V%stdpp)
  (at level 8, format "# l")
: val_scope.

(*

(* [e1 == e2] is location equality. *)

(* TODO: are [%V], [%E], [: tm_scope] useful and correct, since
[val] is not [value] and [expr] is not [instr]? *)

Notation "dst <- src1 == src2" :=
  (ILocEq dst%V src1%V src2%V)%E
  (at level 70, format "dst <- src1 == src2")
: tm_scope.

*)

(* [^ n] denotes the integer [n], as a value, and an expr. *)

Notation "^ n" :=
  (val_int n%Z)
  (at level 8, format "^ n")
  : val_scope.

(* [λ: xs, i] denotes the function whose formal parameters are [_::xs]
   and whose body is [i]. The formal parameters must be expressed as a
   tuple, delimited with double square brackets. *)

Notation "λ: xs , t" :=
  (val_code BAnon%binder xs%binder t%T)
  (at level 200, xs at level 1, t at level 200,
   format "'[' 'λ:'  xs ,  '/  ' t ']'")
    : val_scope.

Notation "μ: x , xs , t" :=
  (val_code x%binder xs%binder t%T)
  (at level 200, xs at level 1, t at level 200,
  format "'[' 'μ:'  x ,  xs ,  '/  ' t ']'").

(* This allows using tuple notation to construct a list of the formal
   parameters. *)

Notation "[[]]" :=
  (nil)
: binder_scope.

Notation "[[ x ]]" :=
  (cons (BNamed x) nil)
: binder_scope.

Notation "[[ x1 , x2 , .. , xn ]]" :=
  (cons (BNamed x1) (cons (BNamed x2) (.. (cons (BNamed xn) nil) .. )))
: binder_scope.

(* ------------------------------------------------------------------------ *)

(* Sequencing. *)

Notation "'let:' x := t1 'in' t2" := (tm_let x%binder t1%T t2%T)
  (at level 200, x at level 1, t1, t2 at level 200,
   format "'[' 'let:'  x  :=  '[' t1 ']'  'in'  '/' t2 ']'") : tm_scope.

Notation "t1 ;; t2" :=
  (tm_let BAnon t1%T t2%T)
  (at level 100, t2 at level 200,
   format "'[' '[hv' '['  t1  ']' ;; ']'  '/' t2 ']'")
: tm_scope.

(* ------------------------------------------------------------------------ *)

(* If. *)

Notation "'if:'  i1  'then'  i2  'else'  i3" :=  (tm_if i1%T i2%T i3%T)
  (at level 200, i1, i2, i3 at level 200) : tm_scope.

(* ------------------------------------------------------------------------ *)

(* Function calls. *)

Coercion tm_call : tm >-> Funclass.

(* This allows using tuple notation to construct a list of the actual
   parameters. *)

Notation "[[]]" :=
  (nil)
    : tm_scope.

Notation "[[ t ]]" :=
  (cons (t : tm)%V nil)
    : tm_scope.

Notation "[[ t1 , t2 , .. , tn ]]" :=
  (cons (t1 : tm)%V (cons (t2 : tm)%V (.. (cons (tn : tm)%V nil) .. )))
    : tm_scope.

(* ------------------------------------------------------------------------ *)

Notation "'alloc' n" :=
  (tm_alloc (n%Z%V))
    (at level 10) : tm_scope.

Notation "'fork' t" :=
  (tm_fork (t%T))
    (at level 10) : tm_scope.

Notation "'CAS' t1 t2 t3 t4" :=
  (tm_cas (t1%V) (t2%Z%V) (t3%Z%V) (t4%Z%V))
    (at level 10) : tm_scope.

Notation "src .[ ofs ]" :=
  (tm_load src%V ofs%Z%V)
    (at level 10, format "src .[ ofs ]") : tm_scope.

Notation "dst .[ ofs ] <- src" :=
  (tm_store dst%V ofs%Z%V src%V)
    (at level 10, format "dst .[ ofs ]  <-  src") : tm_scope.

(* ------------------------------------------------------------------------ *)
(* Op *)

Notation "x '+ y" :=
  (tm_call_prim (prim_int_op IntAdd) (x:tm)%T (y:tm)%T)
    (at level 10 ) : tm_scope.

Notation "x '- y" :=
  (tm_call_prim (prim_int_op IntSub) (x:tm)%T (y:tm)%T)
    (at level 10 ) : tm_scope.

Notation "x '* y" :=
  (tm_call_prim (prim_int_op IntMul) (x:tm)%T (y:tm)%T)
    (at level 10 ) : tm_scope.

Notation "x '/ y" :=
  (tm_call_prim (prim_int_op IntDiv) (x:tm)%T (y:tm)%T)
    (at level 10 ) : tm_scope.

Notation "x '== y" :=
  (tm_call_prim (prim_eq) (x:tm)%T (y:tm)%T)
    (at level 10 ) : tm_scope.

Notation "x '/= y" :=
  (tm_call_prim (prim_neq) (x:tm)%T (y:tm)%T)
    (at level 10 ) : tm_scope.

Notation "x '&& y" :=
  (tm_call_prim (prim_bool_op BoolAnd) (x:tm)%T (y:tm)%T)
    (at level 10 ) : tm_scope.

Notation "x '|| y" :=
  (tm_call_prim (prim_bool_op BoolOr) (x:tm)%T (y:tm)%T)
    (at level 10 ) : tm_scope.
