(** * System LM for propositional minimal logic encoded as an LL theory

This file encodes the inference rules of the system LM (propositional
minimal logic). The cut-coherence and well-formedness properties are
proved and then, using [OLCutElimination] we prove the cut-elimination
theorem for this system .
 *)

Require Export FLL.OL.OLCutElimTheoremPOS.
Require Import Coq.Init.Nat.
Require Import FLL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.
(** ** Syntax *)
(* No constants *)
Inductive Constants := .
(* conjunction, disjunction and implication *)
Inductive Connectives := AND | OR | IMPL  .
(* no quantifiers *)
Inductive Quantifiers := .
(* No unary connectives  *) 
Inductive UConnectives := .

Instance SimpleOLSig : OLSyntax:=
  {|
    OLType := nat;
    constants := Constants ;
    uconnectives := UConnectives;
    connectives := Connectives ;
    quantifiers := Quantifiers
  |}.

(** ** Inference rules *)

(** *** Constants *)
Definition rulesCTE (c:constants) : ContantEnc:=
  match c with
  end.

(** *** Binary connectives *)
Definition rulesBC (c :connectives) :=
  match c with
  | AND => PARTENSOR
  | OR =>  WITHPLUS
  | IMPL => TENSORPAR
  end.
Check rulesBC.

Instance SimpleOORUles : OORules :=
  {|
    rulesCte := rulesCTE ;
    rulesBin := rulesBC
  |}.

(** The cut-elimination theorem instantiated for LJ *)
Check CutElimination.

