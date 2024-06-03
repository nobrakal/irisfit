From irisfit Require Import language notation.
From irisfit.examples Require Import pair.

Definition osent : Z := 0.
Definition otail : Z := 1.

Definition create : val :=
  λ: [[]],
    let: "sent" := alloc 2 in
    pair [["sent", "sent"]].

Definition enqueue : val :=
  μ: "self", [["q", "x"]],
    let: "node" := alloc 2 in
    "node".[0] <- "x";;
    tm_enter ;;
    let: "tail" := "q".[otail] in
    let: "next" := "tail".[1]  in
    if: ("next" '== val_unit)
    then (* The tail is nil, we can try to insert *)
      if: tm_cas "tail" 1%Z val_unit "node"
      then (tm_cas "q" otail "tail" "node" ;; tm_exit)
      else (tm_exit;; "self" [["q","x"]])
    else (* tail didn't point to the last node *)
      (* Try to move the tail-pointer forward, then retry *)
      tm_cas "q" otail "tail" "next" ;; tm_exit;; ("self" [["q","x"]]).

Definition dequeue : val :=
  μ: "self", [["q"]],
    tm_enter;;
    let: "head" := "q".[osent] in
    let: "tail" := "q".[otail] in
    let: "next" := "head".[1] in
    if: ("head" '== "tail")
    then (* Either the queue is empty or the tail is outdated *)
        (if: ("next" '== val_unit)
         then tm_exit ;; "self" [["q"]]
         else (* outdated tail *)
           (tm_cas "q" 1%Z "tail" "next";; tm_exit ;; "self" [["q"]]))
    else (* The queue is non empty. *)
      (if: tm_cas "q" osent "head" "next" then
         let: "v" := "next".[0] in
         (* "KILL" the sentinel (if next is not the sentinel anymore, this has no effect) *)
         "next".[0] <- val_unit;;
         (tm_exit ;; "v")
       else tm_exit ;; "self" [["q"]]).
