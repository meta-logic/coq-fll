(** * System LJ for propositional intuitionistic logic encoded as an LL theory

This file encodes the inference rules of the system LJ . The cut-coherence and well-formedness properties are
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
(* units: true and false *)
Inductive Constants := TT | FF  .
(* conjunction, disjunction and implication *)
Inductive Connectives := AND | OR | IMPL  .
(* no quantifiers *)
Inductive Quantifiers := ALL .
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

(** The cut-elimination theorem instantiated for LK *)
Check CutElimination.

(** Soundness and Completeness *)

Inductive LJSeq : list uexp -> uexp -> Prop :=
| LJinit : forall L F, In F L -> LJSeq L F
| LJAndL : forall L F G R, LJSeq (F :: G :: L) R -> LJSeq ( (t_bin AND F G) :: L) R
.

Definition LEncode L := map (fun x => d| x|) L.
Definition REncode F := u| F|.

Theorem Soundeness: forall L F, LJSeq L F ->
                                seq buildTheory (LEncode L) [ REncode F] (> []).
  Proof with solveF;solveLL'.
    intros.
    induction H.

    (* init *)
    admit.

    simpl.
    decide3' (makeRuleBin AND Left F G)...
    constructor.
    admit.
    tensor' (@nil oo) [REncode R]...
    admit.
Admitted.
