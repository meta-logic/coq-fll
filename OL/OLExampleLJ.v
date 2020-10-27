(** * System LJ for propositional intuitionistic logic encoded as an LL theory

This file encodes the inference rules of the system LJ (propositional
intuitionistic logic). Using [OLCutElimination] we prove the cut-elimination
theorem for this system .
 *)

Require Export FLL.OL.OLCutElimTheoremPOS.
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
Inductive Quantifiers := ALL .
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
Definition rulesCTE (c:constants) :=
  match c with
  | TT => ZEROTOP
  | FF => TOPZERO
  end.


(** *** Binary connectives *)
Definition rulesBC (c :connectives) :=
  match c with
  | AND => PARTENSOR
  | OR =>  WITHPLUS
  | IMPL => TENSORPAR
  end.

(** *** Quantifiers *)
Definition rulesQD (q :quantifiers) :=
  match q with
  | ALL => ALLSOME
  end
.


Instance SimpleOORUles : OORules :=
  {|
    rulesCte := rulesCTE ;
    rulesBin := rulesBC;
    rulesQ := rulesQD
  |}.

(** The cut-elimination theorem instantiated for LJ *)
Check CutElimination.

