#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

export OPAMYES=true

if ! command -v opam >/dev/null ; then
  echo "You are missing opam, the OCaml package manager."
  echo "See"
  echo "  https://opam.ocaml.org/doc/Install.html"
  exit 1
fi

echo "Updating our local copy of the opam package database."
echo "This can take a few minutes..."
opam update

if [ -d _opam ] ; then
  echo "There is already a local opam switch in the current directory."
  echo "If it is OK to remove it, please type:"
  echo "  opam switch remove ."
  echo "then run ./setup.sh again."
  exit 1
fi

echo "Creating a local opam switch in the current directory."
echo "This will take a while (perhaps over 10 minutes)..."

opam switch create \
     --repositories=default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git \
     --deps-only \
     .

eval $(opam env)

make -j 2
