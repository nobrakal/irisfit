From stdpp Require Import decidable binders namespaces.
From irisfit.language Require Import notation closure.
From irisfit.examples Require Import utils diaframe proofmode faa ref ignore.

Definition mk_counter : val :=
  λ: [[]],
    let: "r" := ref [[ ^0 ]] in
    let: "incr" := mk_clo BAnon [[]] (ignore [(faa [["r",0,1]])]) in
    let: "get"  := mk_clo BAnon [[]] ("r".[0]) in
    let: "b" := alloc ^2 in
    "b".[0] <- "incr";;
    "b".[1] <- "get";;
    "b".
