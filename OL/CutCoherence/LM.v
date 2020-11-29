(** * System LM for minimal logic encoded as an LL theory

This file encodes the inference rules of the system LM (minimal logic). 

 *)

Require Export FLL.OL.CutCoherence.OLCuti.
Require Import Coq.Init.Nat.
Require Import FLL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

(** ** Syntax *)
(** No constants *)
Inductive Constants := .
(**  conjunction, disjunction and implication *)
Inductive Connectives := AND | IMP  .
(** universal quantifier *)
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

(**  Constants *)
Definition rulesCTE (c:constants) : ContantEnc:=
  match c with
  end.

(**  Binary connectives *)
Definition rulesBC (c :connectives) :=
  match c with
  | AND => PLUSWITH
  | IMP => TENSORPAR
  end.

(*** Quantifiers *)
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


(** An inductive definition for LM. This will be used to prove that
the LL encoding is sound and complete *)

Inductive LMSeq : list uexp -> uexp -> Prop :=
| LMinit : forall L F,  LMSeq (F:: L) F
| LMAndL1 : forall L F G R, LMSeq (F :: L) R -> LMSeq ( (t_bin AND F G) :: L) R
| LMAndL2 : forall L F G R, LMSeq (G :: L) R -> LMSeq ( (t_bin AND F G) :: L) R
| LMAndR : forall L F G , LMSeq L F -> LMSeq L G -> LMSeq L (t_bin AND F G)
| LMImpL : forall L A B G , LMSeq L A -> LMSeq (B:: L) G -> LMSeq (t_bin IMP A B ::L) G
| LMImpR : forall L A B  , LMSeq (A:: L) B ->  LMSeq L (t_bin IMP A B)
| LMAllL : forall L t FX G, uniform FX -> proper t -> LMSeq( FX t :: L) G -> LMSeq (t_quant ALL FX :: L) G
| LMAllR : forall L FX , uniform FX -> (forall x, proper x -> LMSeq L (FX x)) -> LMSeq L (t_quant ALL FX)
| (* contraction is needed *)
LMContr : forall L F G, (LMSeq (F :: F:: L)) G -> (LMSeq (F :: L)) G
| (* Explicit exchange *)
LMEx : forall L L' G, Permutation L L' -> LMSeq L G -> LMSeq L' G 
. 
Hint Constructors LMSeq : core .
Hint Constructors LMSeq : core .
Hint Constructors OLTheory buildTheory : core.
Hint Constructors  isOLFormula : core. 
Hint Unfold IsPositiveLAtomFormulaL : core. 
Hint Constructors IsPositiveRAtomFormula : core .


Global Instance LML_morph : 
  Proper ((@Permutation uexp) ==> eq ==> iff) (LMSeq).
Proof.
  unfold Proper; unfold respectful. 
  intros.
  split;intros;subst.
  eapply LMEx;eauto.
  apply Permutation_sym in H.
  eapply LMEx;eauto.
Qed.

Ltac solveOLTheory :=
  try
    match goal with
    | [|- OLTheory _] =>
      first [ apply ooth_init ; auto ; SolveIS
            | do 2 constructor;auto ; SolveIS ]
    end.


(** Soundness *)
Theorem Soundeness: forall L F, LMSeq L F ->
                                isOLFormulaL L ->
                                isOLFormula F ->
                                seq OLTheory (LEncode L) (REncode [F]) (> []).
Proof with solveF;solveLL;solveOLTheory;SolveIS;solveOLTheory. 
  intros.
  induction H. 
  + (* init *)
    decide3 (RINIT F)...
    tensor (REncode [F]) (@nil oo)...
  + (* ANDL1 *)
    decide3 (makeRuleBin AND Left F G)...      
    tensor (@nil oo) (REncode [R])...
    oplus1.
    LLPerm ( d| t_bin AND F G | :: d| F |  :: LEncode L).
    apply weakening.
    apply IHLMSeq... 
  +  (* ANDL2 *)
    decide3 (makeRuleBin AND Left F G)...
    tensor (@nil oo) (REncode [R])...
    oplus2.
    LLPerm ( d| t_bin AND F G | :: d| G |  :: LEncode L).
    apply weakening.
    apply IHLMSeq... 
  + (* And R *)
    decide3 (makeRuleBin AND Right F G)...
    tensor (REncode [t_bin AND F G]) (@nil oo).
    apply  IHLMSeq1...
    apply  IHLMSeq2...
  + (* implication left *)
    decide3 (makeRuleBin IMP Left A B)...
    tensor (@nil oo) (REncode [G])...
    tensor (@nil oo) (REncode [G])...
    apply weakening.
    apply IHLMSeq1...
    apply weakening.
    LLPerm (d| B | :: LEncode L ) .
    apply IHLMSeq2... 
  + (* implication right *)
    decide3 (makeRuleBin IMP Right A B)... 
    tensor (REncode [t_bin IMP A B]) (@nil oo).
    
    LLPerm (d| A | :: LEncode L ) .
    apply IHLMSeq... 
  + (* forall left *)
    decide3 (makeRuleQ ALL Left FX)...
    tensor (@nil oo) (REncode [G])...
    existential t...
    apply weakening.
    LLPerm(d| FX t |:: LEncode L )...
    apply IHLMSeq... 
  + (* forall right *)
    decide3 (makeRuleQ ALL Right FX)...
    tensor (REncode [t_quant ALL FX]) (@nil oo)...
    apply H3...
  + (* contraction *)
    eapply contractionSet with (L0:=LEncode [F]);[firstorder|]...
    apply IHLMSeq...
  + (* exchange *)
    eapply Permutation_map in  H as H'.
    unfold LEncode; rewrite <- H'...
    apply IHLMSeq...
    rewrite H...
Qed.

Ltac toLM H :=
  match (type of H) with
  | In (u| _ |)(LEncode _ ++ REncode _) =>
    apply upRight in H; apply OLInPermutation in H;CleanContext
  | In (d| _ |)(LEncode _) =>
    apply OLInPermutationL in H;CleanContext;
    eapply LMEx; [apply Permutation_sym;eauto | ]
  | seqN _ _ (u| ?F | :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := LEncode L ++ REncode (F :: R)) in H ;[| simpl; perm]
  | seqN _ _ (u| ?F | :: ?T :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := T :: LEncode L ++ REncode (F :: R)) in H ;[| simpl; perm]
  | seqN _ _ (d| ?F | :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := LEncode (F :: L) ++ REncode R) in H ;[| simpl; perm]
  | seqN _ _ (d| ?F | :: ?T :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := T :: LEncode (F::L) ++ REncode R) in H ;[| simpl; perm]
  end.

(** Completeness *)
Theorem Completeness: forall n L F , 
    isOLFormulaL L ->
    isOLFormula F ->
    seqN OLTheory n (LEncode L)  (REncode [F]) (> []) ->
    LMSeq L F .
Proof with solveF;solveLL;SolveIS;CleanContext.
  induction n using strongind;intros.
  inversion H1.

  inversion H2;subst.
  simpl in H5.
  apply RemoveUnique in H5...
  apply InIsPositiveL in H5;contradiction.
  inversion H4...
  + (* from the theory *)
    inversion H3...
    ++ (* Constants *)
      destruct C.
    ++ (* Constants *)
      destruct C.
    ++ (* binary connective right *)
      apply FocusingRightRule in H6...
      (* by cases on C *)
      destruct C;simpl in H8...
      { (* case AND *)
        apply AppPLUSWITHRight in H8...
        apply LMAndR; apply (H x0)...
      }
    { (* impl *)
        apply AppTENSORPARRight in H8...
        apply LMImpR.
        apply (H x0)...
      }
    ++  (* binary connective left *)
      apply FocusingLeftRule in H6...
      (* by cases on C *)
      destruct C;simpl in H8...
      { (* case AND *)
        apply AppPLUSWITHLeft in H8...
        destruct H8.
        + toLM H7.
          apply LMContr. 
          apply LMAndL1; rewrite <- H7.
          eapply (H x0)...
        + toLM H7.
          apply LMContr. 
          apply LMAndL2; rewrite <- H7.
          eapply (H x0)...
      }
      { (* impl *)
        apply AppTENSORPARLeft in H8...
        toLM H7.
        apply LMContr.
        apply LMImpL; rewrite <- H6; eapply (H x0)...
      }
    ++ (* Quantifier right *)
      apply FocusingRightQ in H6...
      (* by cases on C*)
      destruct C;simpl in H9...
      { (* case ALL *)
        apply AppALLSOMERight in H9...
        apply LMAllR;intros...
        specialize (H8 x H6).
        eapply (H x0)...
      }
    ++ (* Quantifier left *)
      apply FocusingLeftQ in H6...
      (* by cases on C*)
      destruct C;simpl in H9...
      { (* case ALL *)
        apply AppALLSOMELeft in H9...
        toLM H8.
        apply LMContr.
        apply LMAllL with (t:= x1)...
        rewrite <- H6; eapply (H x0)...
      }
    
  + (* init *)
    apply Init_inversion1 in H6...
    toLM H6.
    apply LMinit.
Qed.

Theorem Adequacy:  forall L F , 
    isOLFormulaL L ->
    isOLFormula F ->
    (
      seq OLTheory  (LEncode L) (REncode [F]) (> []) <->
      LMSeq L F ).
Proof with solveF;solveLL.
  intros.
  split;intros.
  + apply seqtoSeqN in H1;CleanContext.
    apply  Completeness in H1...
  +  apply Soundeness in H1...
Qed.

(** The cut-elimination theorem instantiated for LM *)
Check Adequacy .
Check CutElimination.
