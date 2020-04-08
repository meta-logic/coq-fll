(** * System LK for propositional classical logic encoded as an LL theory

This file encodes the inference rules of the system LK (propositional
classical logic). The cut-coherence and well-formedness properties are
proved and then, using [OLCutElimination] we prove the cut-elimination
theorem for this system .
 *)

Require Export FLL.OL.OLCutElimTheoremPOSNEG.
Require Import Coq.Init.Nat.
Require Import FLL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


(** ** Syntax *)
(* units: true and false *)
Inductive Constants := TT | FF  .
(* conjunction, disjunction and implication *)
Inductive Connectives := AND | OR | IMPL  .
(* no quantifiers *)
Inductive Quantifiers := .
(* Although negation is not needed we keep it for illustrative purposes *) 
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
Definition rulesCTE (c:constants) :=
  match c with
  | TT => ZEROTOP
  | FF => TOPZERO
  end.

(** *** Binary connectives *)
Definition rulesBC (c :connectives) :=
  match c with
  | AND => PARTENSOR
  | OR =>  TENSORPAR
  | IMPL => TENSORPAREXCH
  end.


Instance SimpleOORUles : OORules :=
  {|
    rulesCte := rulesCTE ;
    rulesBin := rulesBC
  |}.

(** The cut-elimination theorem instantiated for LK *)
Check CutElimination.
