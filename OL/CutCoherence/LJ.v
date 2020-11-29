(** * System LJ for first-order intuitionistic logic encoded as an LL theory *)

(** The rule for conjunction in this system is

<<
Gamma , Fi |-- G
----------------------
Gamma , F1/\ F2 |-- G
>>

and hence encoded with the formula [PLUSWITH] (that uses [OPLUS] to choose one of the formulas Fi *)

Require Export FLL.OL.CutCoherence.OLCuti.
Require Import FLL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


(** ** Syntax *)
(** units: true and false *)
Inductive Constants := TT | FF  .
(** conjunction, disjunction and implication *)
Inductive Connectives := AND | OR | IMP  .
(** universal and existential quantifiers *)
Inductive Quantifiers := ALL|SOME .
(* No unary connectives *)
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
(** The following definitions chooses the  LL connectives to encode the LJ rules *)
(** Constants *)
Definition rulesCTE (c:constants) :=
  match c with
  | TT => ZEROTOP
  | FF => TOPZERO
  end.

(** Binary connectives *)
Definition rulesBC (c :connectives) :=
  match c with
  | AND => PLUSWITH
  | OR =>  WITHPLUS
  | IMP => TENSORPAR
  end.

(** Quantifiers *)
Definition rulesQD (q :quantifiers) :=
  match q with
  | ALL => ALLSOME
  | SOME => SOMEALL
  end
.

Instance SimpleOORUles : OORules :=
  {|
    rulesCte := rulesCTE ;
    rulesBin := rulesBC;
    rulesQ := rulesQD
  |}.


(** An inductive definition for LJ. This will be used to prove that
the LL encoding is sound and complete *)

Inductive LJSeq : list uexp -> uexp -> Prop :=
| LJTRUE : forall L, LJSeq L (t_cons TT)
| LJFALSE : forall L G, LJSeq (t_cons FF :: L) G
| LJinit : forall L F,  LJSeq (F:: L) F
| LJAndL1 : forall L F G R, LJSeq (F :: L) R -> LJSeq ( (t_bin AND F G) :: L) R
| LJAndL2 : forall L F G R, LJSeq (G :: L) R -> LJSeq ( (t_bin AND F G) :: L) R
| LJAndR : forall L F G , LJSeq L F -> LJSeq L G -> LJSeq L (t_bin AND F G)
| LJOrL : forall L F G R,  LJSeq (F :: L) R ->  LJSeq (G :: L) R -> LJSeq ( (t_bin OR F G) :: L) R
| LJOrR1 : forall L F G , LJSeq L F -> LJSeq L (t_bin OR F G)
| LJOrR2 : forall L F G , LJSeq L G -> LJSeq L (t_bin OR F G)
| LJImpL : forall L A B G , LJSeq L A -> LJSeq (B:: L) G -> LJSeq (t_bin IMP A B ::L) G
| LJImpR : forall L A B  , LJSeq (A:: L) B ->  LJSeq L (t_bin IMP A B)
| LJAllL : forall L t FX G, uniform FX -> proper t -> LJSeq( FX t :: L) G -> LJSeq (t_quant ALL FX :: L) G
| LJAllR : forall L FX , uniform FX -> (forall x, proper x -> LJSeq L (FX x)) -> LJSeq L (t_quant ALL FX)
| LJEXL : forall L FX G, uniform FX -> (forall x, proper x -> LJSeq (FX x:: L) G) -> LJSeq (t_quant SOME FX :: L) G
| LJEXR : forall L FX t, uniform FX -> proper t -> LJSeq L (FX t)-> LJSeq L (t_quant SOME FX)
| (* contraction is needed *)
LJContr : forall L F G, (LJSeq (F :: F:: L)) G -> (LJSeq (F :: L)) G
| (* Explicit exchange *)
LJEx : forall L L' G, Permutation L L' -> LJSeq L G -> LJSeq L' G 
. 
Hint Constructors LJSeq : core .
Hint Constructors LJSeq : core .
Hint Constructors OLTheory buildTheory : core.
Hint Constructors  isOLFormula : core. 
Hint Unfold IsPositiveLAtomFormulaL : core. 
Hint Constructors IsPositiveRAtomFormula : core .


Global Instance LJL_morph : 
  Proper ((@Permutation uexp) ==> eq ==> iff) (LJSeq).
Proof.
  unfold Proper; unfold respectful. 
  intros.
  split;intros;subst.
  eapply LJEx;eauto.
  apply Permutation_sym in H.
  eapply LJEx;eauto.
Qed.

Ltac solveOLTheory :=
  try
    match goal with
    | [|- OLTheory _] =>
      first [ apply ooth_init ; auto ; SolveIS
            | do 2 constructor;auto ; SolveIS ]
    end.


(** Soundness theorem *)
Theorem Soundeness: forall L F, LJSeq L F ->
                                isOLFormulaL L ->
                                isOLFormula F ->
                                seq OLTheory (LEncode L) (REncode [F]) (> []).
Proof with solveF;solveLL;solveOLTheory;SolveIS;solveOLTheory. 
  intros.
  induction H. 
  + (* True on the right *)
    decide3 (makeRuleConstant TT Right)...
    tensor (REncode [t_cons TT]) (@nil oo).
  + (* false on the left *)
    decide3 (makeRuleConstant FF Left)...
    tensor (@nil oo) (REncode [G])...
  + (* init *)
    decide3 (RINIT F)...
    tensor (REncode [F]) (@nil oo)...
  + (* ANDL1 *)
    decide3 (makeRuleBin AND Left F G)...      
    tensor (@nil oo) (REncode [R])...
    oplus1.
    LLPerm ( d| t_bin AND F G | :: d| F |  :: LEncode L).
    apply weakening.
    apply IHLJSeq... 
  +  (* ANDL2 *)
    decide3 (makeRuleBin AND Left F G)...
    tensor (@nil oo) (REncode [R])...
    oplus2.
    LLPerm ( d| t_bin AND F G | :: d| G |  :: LEncode L).
    apply weakening.
    apply IHLJSeq... 
  + (* And R *)
    decide3 (makeRuleBin AND Right F G)...
    tensor (REncode [t_bin AND F G]) (@nil oo).
    apply  IHLJSeq1...
    apply  IHLJSeq2...
  + (* Or L *)
    decide3 (makeRuleBin OR Left F G)...
    tensor (@nil oo)  (REncode [R])...
    
    apply weakening. LLPerm(d| F | :: LEncode L).
    apply IHLJSeq1... 
    
    apply weakening. LLPerm(d| G | :: LEncode L).
    apply IHLJSeq2...
  +  (* OrR1 *)
    decide3 (makeRuleBin OR Right F G)...
    tensor (REncode [t_bin OR F G]) (@nil oo). 
    oplus1.
    apply IHLJSeq...
  +  (* OrR2 *)
    decide3 (makeRuleBin OR Right F G)...
    tensor (REncode [t_bin OR F G]) (@nil oo).
    oplus2.
    apply IHLJSeq...
  + (* implication left *)
    decide3 (makeRuleBin IMP Left A B)...
    tensor (@nil oo) (REncode [G])...
    tensor (@nil oo) (REncode [G])...
    apply weakening.
    apply IHLJSeq1...
    apply weakening.
    LLPerm (d| B | :: LEncode L ) .
    apply IHLJSeq2... 
  + (* implication right *)
    decide3 (makeRuleBin IMP Right A B)... 
    tensor (REncode [t_bin IMP A B]) (@nil oo).
    
    LLPerm (d| A | :: LEncode L ) .
    apply IHLJSeq... 
  + (* forall left *)
    decide3 (makeRuleQ ALL Left FX)...
    tensor (@nil oo) (REncode [G])...
    existential t...
    apply weakening.
    LLPerm(d| FX t |:: LEncode L )...
    apply IHLJSeq... 
  + (* forall right *)
    decide3 (makeRuleQ ALL Right FX)...
    tensor (REncode [t_quant ALL FX]) (@nil oo)...
    apply H3...
  + (* existst left *)
    decide3 (makeRuleQ SOME Left FX)... 
    tensor (@nil oo) (REncode [G])...
    apply weakening...
    LLPerm(d| FX x |:: LEncode L )...
    apply H3...
  + (* exists right *)
    decide3 (makeRuleQ SOME Right FX)...
    tensor  (REncode [t_quant SOME FX]) (@nil oo)... 
    existential t...
    apply IHLJSeq...
  + (* contraction *)
    eapply contractionSet with (L0:=LEncode [F]);[firstorder|]...
    apply IHLJSeq...
  + (* exchange *)
    eapply Permutation_map in  H as H'.
    unfold LEncode; rewrite <- H'...
    apply IHLJSeq...
    rewrite H...
Qed.

Ltac toLJ H :=
  match (type of H) with
  | In (u| _ |)(LEncode _ ++ REncode _) =>
    apply upRight in H; apply OLInPermutation in H;CleanContext
  | In (d| _ |)(LEncode _) =>
    apply OLInPermutationL in H;CleanContext;
    eapply LJEx; [apply Permutation_sym;eauto | ]
  | seqN _ _ (u| ?F | :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := LEncode L ++ REncode (F :: R)) in H ;[| simpl; perm]
  | seqN _ _ (u| ?F | :: ?T :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := T :: LEncode L ++ REncode (F :: R)) in H ;[| simpl; perm]
  | seqN _ _ (d| ?F | :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := LEncode (F :: L) ++ REncode R) in H ;[| simpl; perm]
  | seqN _ _ (d| ?F | :: ?T :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := T :: LEncode (F::L) ++ REncode R) in H ;[| simpl; perm]
  end.

(** Completeness theorem *)
Theorem Completeness: forall n L F , 
    isOLFormulaL L ->
    isOLFormula F ->
    seqN OLTheory n (LEncode L)  (REncode [F]) (> []) ->
    LJSeq L F .
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
    ++ (* Constant right *)
      apply FocusingRightCte in H6...
      (* by cases on C *)
      destruct C;simpl in H8...
    ++  (* constant left *)
      apply FocusingLeftCte in H6...
      (* by cases on C *)
      destruct C;simpl in H8...
      toLJ H7.
      apply LJFALSE.
    ++ (* binary connective right *)
      apply FocusingRightRule in H6...
      (* by cases on C *)
      destruct C;simpl in H8...
      { (* case AND *)
        apply AppPLUSWITHRight in H8...
        apply LJAndR; apply (H x0)...
      }
      { (*  OR *)
        apply AppWITHPLUSRight in H8...
        destruct H8.
        apply LJOrR1.
        apply (H x0)...
        apply LJOrR2.
        apply (H x0)...
      }
      { (* impl *)
        apply AppTENSORPARRight in H8...
        apply LJImpR.
        apply (H x0)...
      }
    ++  (* binary connective left *)
      apply FocusingLeftRule in H6...
      (* by cases on C *)
      destruct C;simpl in H8...
      { (* case AND *)
        apply AppPLUSWITHLeft in H8...
        destruct H8.
        + toLJ H7.
          apply LJContr. 
          apply LJAndL1; rewrite <- H7.
          eapply (H x0)...
        + toLJ H7.
          apply LJContr. 
          apply LJAndL2; rewrite <- H7.
          eapply (H x0)...
      }
      { (*  OR *)
        apply AppWITHPLUSLeft in H8...
        toLJ H7.
        apply LJContr.
        apply LJOrL; rewrite <- H6; eapply (H x0)...
      }
      { (* impl *)
        apply AppTENSORPARLeft in H8...
        toLJ H7.
        apply LJContr.
        apply LJImpL; rewrite <- H6; eapply (H x0)...
      }
    ++ (* Quantifier right *)
      apply FocusingRightQ in H6...
      (* by cases on C*)
      destruct C;simpl in H9...
      { (* case ALL *)
        apply AppALLSOMERight in H9...
        apply LJAllR;intros...
        specialize (H8 x H6).
        eapply (H x0)...
      }
      { (* case SOME *)
        apply AppSOMEALLRight in H9...
        apply LJEXR with (t:=x1)...
        eapply (H x0)...
      }          
    ++ (* Quantifier left *)
      apply FocusingLeftQ in H6...
      (* by cases on C*)
      destruct C;simpl in H9...
      { (* case ALL *)
        apply AppALLSOMELeft in H9...
        toLJ H8.
        apply LJContr.
        apply LJAllL with (t:= x1)...
        rewrite <- H6; eapply (H x0)...
      }
      { (* case SOME *)
        apply AppSOMEALLLeft in H9...
        toLJ H8.
        apply LJContr.
        rewrite <- H6.
        apply LJEXL;intros...
        specialize (H9 _ H8).
        eapply (H x0)...
      }
  + (* init *)
    apply Init_inversion1 in H6...
    toLJ H6.
    apply LJinit.
Qed.

Theorem Adequacy:  forall L F , 
    isOLFormulaL L ->
    isOLFormula F ->
    (
      seq OLTheory  (LEncode L) (REncode [F]) (> []) <->
      LJSeq L F ).
Proof with solveF;solveLL.
  intros.
  split;intros.
  + apply seqtoSeqN in H1;CleanContext.
    apply  Completeness in H1...
  +  apply Soundeness in H1...
Qed.
(** The cut-elimination theorem instantiated for LJ *)
Check Adequacy .
Check CutElimination.
