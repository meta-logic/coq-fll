(** * System LJ for propositional intuitionistic logic encoded as an LL theory *)

(** The rule for conjunction in this system is

Gamma , F1, F2 |-- G
----------------------
Gamma , F1/\ F2 |-- G

and hence encoded with the formula PARTENSOR (that uses PAR to store
the two atoms into the classical context *)

Require Export FLL.OL.OLCuti.
Require Import Coq.Init.Nat.
Require Import FLL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


(** ** Syntax *)
(* units: true and false *)
Inductive Constants := TT | FF  .
(* conjunction, disjunction and implication *)
Inductive Connectives := AND | OR | IMP  .
(* no quantifiers *)
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
  | IMP => TENSORPAR
  end.

(** *** Quantifiers *)
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


(** Soundness and Completeness *)

Inductive LJSeq : list uexp -> uexp -> Prop :=
| LJTRUE : forall L, LJSeq L (t_cons TT)
| LJFALSE : forall L G, LJSeq (t_cons FF :: L) G
| LJinit : forall L F,  LJSeq (F:: L) F
| LJAndL : forall L F G R, LJSeq (F :: G :: L) R -> LJSeq ( (t_bin AND F G) :: L) R
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

Definition LEncode L := map (fun x => d| x|) L.
Definition REncode F := u| F|.


Hint Constructors OLTheory buildTheory : core.
Hint Constructors isOLFormula : core. 


Lemma isOLLencode : forall L, isOLFormulaL L -> IsPositiveLAtomFormulaL (LEncode L).
Proof with subst;auto.
  intros.
  induction L. simpl...
  inversion H...
  assert (IsPositiveLAtomFormula (d| a |)).
  constructor...  
  apply ForallCons...
  apply IHL...
Qed.

Lemma PermutationLEncode : forall L a x x1,
    Permutation (LEncode L) (d| a | :: x) -> Permutation (a :: x1) L -> Permutation x (LEncode x1).
Proof with subst;auto.
  intros.      
  assert(Permutation (d| a | :: x) (LEncode ((a :: x1)))).
  {  symmetry.
     symmetry in H.
     apply Permutation_map_inv in H.
     do 2 destruct H.
     rewrite H.
     apply Permutation_map.
     eapply (perm_trans H0 H1). }
  simpl in H1.
  eapply (Permutation_cons_inv H1).
Qed.

Lemma InLEncode : forall L a,
    In (d| a |) (LEncode L) -> In a L.
Proof with subst;auto.
  intros.      
  apply in_map_iff in H.
  do 2 destruct H.
  inversion H...
Qed.

Lemma isOLFormulaIn : forall F L, 
    isOLFormulaL L -> In F L -> isOLFormula F. 
Proof.
  intros.
  unfold isOLFormulaL in H.
  generalize (Forall_forall isOLFormula L );intro.
  destruct H1.
  apply H1 with (x:= F) in H ;auto.
Qed.

Generalizable All Variables.
Global Instance isOLFormulaL_morph : 
  Proper ((@Permutation uexp) ==> Basics.impl) (Forall isOLFormula).
Proof.
  unfold Proper; unfold respectful; unfold Basics.impl.
  intros.
  eapply Forall_Permute;eauto.
Qed.  

Ltac solveIsOLForm :=
  repeat
    match goal with
    | [ H: isOLFormula (t_quant _ ?FX) |- isOLFormula (?FX ?x) ] => 
      inversion H;subst; clear H
    | [ H: isOLConstant (t_quant _ ?FX) |- isOLFormula (?FX ?x) ] => 
      inversion H;subst;auto       
    | [ H: isOLFormula (t_bin _ ?A1 ?A2) |- isOLFormula ?A2 ] => 
      inversion H;subst; clear H
    | [ H: isOLConstant (t_bin _ ?A1 ?A2) |- isOLFormula ?A2 ] => 
      inversion H;subst;auto  
    | [ H: isOLFormula (t_bin _ ?A1 ?A2) |- isOLFormula ?A1 ] => 
      inversion H;subst; clear H
    | [ H: isOLConstant (t_bin _ ?A1 ?A2) |- isOLFormula ?A1 ] => 
      inversion H;subst;auto 
    | [ H1: isOLFormulaL ?L, H2: isOLFormula (t_bin _ ?A1 ?A2) |- isOLFormulaL (?A1 :: ?L) ] =>
      inversion H2;subst; clear H2                 
    | [ H1: isOLFormulaL ?L, H2: isOLConstant (t_bin _ ?A1 ?A2) |- isOLFormulaL (?A1 :: ?L) ] =>
      inversion H2;subst;auto;apply ForallCons;auto  
    | [ H1: isOLFormulaL ?L, H2: isOLFormula (t_bin _ ?A1 ?A2) |- isOLFormulaL (?A2 :: ?L) ] =>
      inversion H2;subst; clear H2                 
    | [ H1: isOLFormulaL ?L, H2: isOLConstant (t_bin _ ?A1 ?A2) |- isOLFormulaL (?A2 :: ?L) ] =>
      inversion H2;subst;auto;apply ForallCons;auto           
    end;auto.

Ltac solveIsOLFormL :=
  try solveIsOLForm;
  repeat
    match goal with
    | [ H1: isOLFormulaL (?F :: ?M'), H2: isOLFormulaL ?M |- isOLFormulaL (?M ++ [?F]) ] => 
      assert(Hp: Permutation (M ++ [F]) (F :: M) ) by perm;
      rewrite Hp;inversion H1;subst;apply ForallCons;auto     
    | [ H1: isOLFormulaL (?F :: ?M') |- isOLFormula ?F ] => 
      inversion H1;subst;auto  
    | [ H1: isOLFormulaL (?F :: ?M) |- isOLFormulaL (?F'::?M) ] => 
      inversion H1;subst;apply ForallCons;auto  
    | [ H1: _ |- isOLFormulaL (?F::?M) ] => 
      try solve [repeat apply ForallCons;auto]          
    | [ H1: isOLFormulaL (?F :: ?M) |- isOLFormulaL ?M ] => 
      inversion H1;subst;auto 
    | [ H1: isOLFormulaL ?M, H2: Permutation ?M ?M' |- _ ] => 
      rewrite H2 in H1;clear H2
    | [ H1: isOLFormulaL ?M, H2: Permutation ?M' ?M |- _ ] => 
      rewrite <- H2 in H1;clear H2         
    | [ H1: isOLFormulaL (?M++?N) |- isFormulaL ?M ] => 
      eapply ForallAppInv1;eauto  
    | [ H1: isOLFormulaL (?M++?N) |- isFormulaL ?N ] => 
      eapply ForallAppInv2;eauto                      
    | [ H1: In ?F ?B |- isFormula ?F ] => 
      apply isOLFormulaIn in H1;auto  
    end; try solveIsOLForm.


Ltac InForall1 :=
  match goal with
  | [ H: In ?F (LEncode ?L) |- _ ] => 
    assert(Ht:In (t_cons FF) L);
    apply in_map_iff in H;
    destruct H as [l H'];
    destruct H' as [H'' H'''];
    inversion H'';subst;auto;
    apply InPermutation in Ht;
    destruct Ht as [t Ht'];symmetry in Ht'
  end.

Ltac InForall2 :=
  match goal with
  | [ H: In ?F (LEncode ?L) |- _ ] => 
    assert(Hp:exists L', Permutation (LEncode L) (F :: L')) by
        refine(InPermutation _ _ H); destruct Hp;apply InLEncode in H;
    apply InPermutation in H;destruct H;symmetry in H
  end.


Ltac solveOLTheory :=
  try
    match goal with
    | [ H: isOLFormulaL (_  _ ?F::?L)|- OLTheory _ ] => 
      do 2 constructor;inversion H;subst;auto 
    | [ H: _|- OLTheory _ ] => 
      do 2 constructor;auto 
    end.

Ltac simplOLFormulas :=
  solveOLTheory;
  try
    match goal with
    | [ H: _ |- isOLFormulaL (?F :: ?L)  ] => apply ForallCons;auto        
                                                                 
    | [ H: lbind 0 ?FX = lbind 0 ?FX'  |- _ ] => 
      apply lbindEq in H;auto;rewrite H in *
    | [ Hx: proper ?x,
            H: forall t, proper t -> isOLFormula (?FX t)  |- _ ] => 
      specialize(H x Hx) as Hf;auto

    | [ H: isOLFormula (t_quant _ ?FX) |- _ ] => 
      inversion H as [ |id H' | | | ];subst;
      [inversion H'|]       
    | [ H: isOLFormula (t_bin _ ?A1 ?A2) |- _ ] => 
      inversion H as [ |id H' | | | ];subst;
      [inversion H'|]
    | [ H: isOLFormulaL (t_cons ?C::?L) |- _ ] => 
      inversion H;subst; auto              
    | [ H: isOLFormulaL (t_quant _ ?FX::?L) |- _ ] => 
      inversion H;subst; auto        
    | [ H: isOLFormulaL (t_bin _ ?A1 ?A2::?L) |- _ ] => 
      inversion H;subst; auto
    | [ H: Permutation ?L ?L', H0 : isOLFormulaL ?L' |- _ ] => 
      assert(isOLFormulaL L);[apply (PermuteMap H0);symmetry;auto|];
      assert(Permutation (LEncode L) (LEncode L'));[apply Permutation_map; auto|]
    end;auto.


Theorem Soundeness: forall L F, LJSeq L F ->
                                isOLFormulaL L ->
                                isOLFormula F ->
                                seq OLTheory (LEncode L) [ REncode F] (> []).
Proof with solveF;solveLL;simplOLFormulas.
  intros.
  induction H. 
  + (* True on the right *)
    decide3 (makeRuleConstant TT Right)...
    tensor [REncode (t_cons TT)] (@nil oo).
  + (* false on the left *)
    decide3 (makeRuleConstant FF Left)...
    tensor (@nil oo) [REncode G]...
  + (* init *)
    decide3 (RINIT F)...
    tensor [REncode F] (@nil oo)...
  + (* ANDL1 *)
    decide3 (makeRuleBin AND Left F G)...      
    tensor (@nil oo) [REncode R]...
    LLPerm ( d| t_bin AND F G | :: d| F |  :: d| G| :: LEncode L).
    apply weakening.
    apply IHLJSeq... 
  + (* And R *)
    decide3 (makeRuleBin AND Right F G)...
    tensor [REncode (t_bin AND F G)] (@nil oo).
    tensor (@nil oo) (@nil oo).
  + (* Or L *)
    decide3 (makeRuleBin OR Left F G)...
    tensor (@nil oo)  [REncode R]...
    
    apply weakening. LLPerm(d| F | :: LEncode L).
    apply IHLJSeq1... 
    
    apply weakening. LLPerm(d| G | :: LEncode L).
    apply IHLJSeq2...
  +  (* OrR1 *)
    decide3 (makeRuleBin OR Right F G)...
    tensor [REncode (t_bin OR F G)] (@nil oo). 
    
    oplus1.
  +  (* OrR2 *)
    decide3 (makeRuleBin OR Right F G)...
    tensor [REncode (t_bin OR F G)] (@nil oo).
    
    oplus2.
  + (* implication left *)
    decide3 (makeRuleBin IMP Left A B)...
    tensor (@nil oo) [REncode G]...
    tensor (@nil oo) [REncode G]. 
    
    apply weakening.
    apply IHLJSeq1... 
    
    apply weakening.
    LLPerm (d| B | :: LEncode L ) .
    apply IHLJSeq2... 
  + (* implication right *)
    decide3 (makeRuleBin IMP Right A B)... 
    tensor [ REncode (t_bin IMP A B)] (@nil oo).
    
    LLPerm (d| A | :: LEncode L ) .
    apply IHLJSeq... 
  + (* forall left *)
    decide3 (makeRuleQ ALL Left FX)...
    tensor (@nil oo) [REncode G]...
    
    existential t...
    apply weakening.
    LLPerm(d| FX t |:: LEncode L )...
    
    apply IHLJSeq... 
  + (* forall right *)
    decide3 (makeRuleQ ALL Right FX)...
    tensor ([REncode (t_quant ALL FX)]) (@nil oo)...

    apply H3...
  + (* existst left *)
    decide3 (makeRuleQ SOME Left FX)... 
    tensor (@nil oo) [REncode G]...
    
    apply weakening...
    LLPerm(d| FX x |:: LEncode L )...
    apply H3...
  + (* exists right *)
    decide3 (makeRuleQ SOME Right FX)...
    tensor  [REncode (t_quant SOME FX)] (@nil oo)... 
    existential t...
  + (* contraction *)
    eapply contractionSet with (L0:=LEncode [F]);[firstorder|]...
    apply IHLJSeq...
    inversion H0...
  + (* exchange *)
    simplOLFormulas.
    eapply (exchangeCC H4)...
Qed.

Theorem Completeness: forall n L F , 
    isOLFormulaL L ->
    isOLFormula F ->
    seqN OLTheory n (LEncode L) [ REncode F] (> []) ->
    LJSeq L F .
Proof with solveF;solveLL.
  induction n using strongind;intros.
  inversion H1.

  inversion H2...
  unfold REncode in H4... (* cannot focus on atoms *)
  apply in_map_iff in H5. (* H5 is inconsistent since F0 must be an atom *)
  destruct H5... (* H5 is inconsistent since F0 must be an atom *)

  inversion H4...
  + (* from the theory *)
    inversion H3...
    ++ (* Constant right *)
      apply FocusingRightCte in H6;[|apply (isOLLencode H0)].
      CleanContext.
      (* by cases on C *)
      destruct C;simpl in H8...
      inversion H8... (* there is no proof o zero *)
    ++  (* constant left *)
      apply FocusingLeftCte in H6;[|apply (isOLLencode H0)].
      CleanContext.
      (* by cases on C *)
      destruct C;simpl in H8...
      inversion H8... (* there is no proof o zero *)
      
      InForall1. (* FF must be in L *)
      apply (LJEx Ht').
      apply LJFALSE.
    ++ (* binary connective right *)
      apply FocusingRightRule in H6;[|apply (isOLLencode H0)].
      CleanContext.
      (* by cases on C *)
      destruct C;simpl in H8...
      { (* case AND *)
        apply AppPARTENSORRight in H8.
        CleanContext.
        apply LJAndR.
        apply (H x0);solveIsOLFormL.
        apply (H x0);solveIsOLFormL. 
      }
      { (*  OR *)
        apply AppWITHPLUSRight in H8.
        CleanContext.
        destruct H8.
        apply LJOrR1.
        apply (H x0);solveIsOLFormL. 
        apply LJOrR2.
        apply (H x0);solveIsOLFormL. 
      }
      { (* impl *)
        apply AppTENSORPARRight in H8.
        CleanContext.
        apply LJImpR.
        apply (H x0);solveIsOLFormL... 
      }
    ++  (* binary connective left *)
      apply FocusingLeftRule in H6;[|apply (isOLLencode H0)].
      CleanContext.
      (* by cases on C *)
      destruct C;simpl in H8...
      { (* case AND *)
        apply AppPARTENSORLeft in H8.
        CleanContext.

        apply InLEncode in H6.
        apply InPermutation in H6.
        destruct H6.
        assert(Hp : Permutation (LEncode L) (d| t_bin AND F1 G | :: LEncode x)).
          
        eapply Permutation_map in H5.
        simpl in H5. exact H5.
        symmetry in H5.
          
        assert(HF: isOLFormulaL (t_bin AND F1 G :: x)). 
        rewrite H5;auto.
          
        apply (LJEx H5).
        apply LJContr. 
        apply LJAndL.

        eapply (H x0)...
        apply ForallCons...
        inversion HF.
        solveIsOLFormL.
        apply ForallCons...
        inversion HF.
        solveIsOLFormL.
        rewrite  <- Hp...
      }
      { (*  OR *)
        apply AppWITHPLUSLeft in H8.
        CleanContext.
        InForall2.
        assert(HF: isOLFormulaL (t_bin OR F1 G :: x1)).
        symmetry in H6.
        rewrite H6 in H0;auto.
        
        inversion HF...
        
        apply (LJEx H6).
        apply LJContr.
        apply LJOrL.
        + eapply PermutationLEncode in H6;[|exact H5].
          eapply (H x0)...
          solveIsOLFormL.
          rewrite <- H6.
          rewrite <- H5...
        + eapply PermutationLEncode in H6;[|exact H5].
          
          eapply (H x0)...
          solveIsOLFormL.
          rewrite <- H6.
          rewrite <- H5...
      }
      { (* impl *)
        apply AppTENSORPARLeft in H8.
        CleanContext.
        
        InForall2.
        
        assert(HF: isOLFormulaL (t_bin IMP F1 G :: x1)).
        symmetry in H6.
        rewrite H6 in H0;auto. 
        inversion HF...

        apply (LJEx H6).
        apply LJContr.
        apply LJImpL.
        + eapply PermutationLEncode in H6;[|exact H5].
          
          eapply (H x0)...
          solveIsOLFormL.
          rewrite <- H6.
          rewrite <- H5...
        + eapply PermutationLEncode in H6;[|exact H5].
          
          eapply (H x0)...
          solveIsOLFormL.
          rewrite <- H6.
          rewrite <- H5...
      }
    ++ (* Quantifier right *)
      apply FocusingRightQ in H6;[|apply (isOLLencode H0)].
      CleanContext.
      (* by cases on C*)
      destruct C;simpl in H9...
      { (* case ALL *)
        inversion H9...
        inversion H13...
        apply LJAllR;intros...
        specialize(H16 x H5).
        
        inversion H16...
        apply H in H19...
        
        solveIsOLFormL.
        apply lbindEq in H11...
        rewrite <- H11...
      }
      { (* case SOME *)
        inversion H9...
        inversion H14...
        inversion H13...
        apply LJEXR with (t:=t)...
        apply H in H18...
        (* This part should be automatic *)
        solveIsOLFormL.
        apply lbindEq in H11...
        rewrite <- H11...
      }          
    ++ (* Quantifier left *)
      apply FocusingLeftQ in H6;[|apply (isOLLencode H0)]. 
      CleanContext.
      (* by cases on C*)
      destruct C;simpl in H9...
      { (* case ALL *)
        apply AppALLSOMELeft in H9.
        CleanContext.
        
        inversion H8...
        inversion H5...
        
        InForall2.
        
        assert(HF: isOLFormulaL (t_quant ALL FX :: x2)).
        symmetry in H6.
        rewrite H6 in H0;auto. 
        inversion HF...
        
        apply (LJEx H6).
        apply LJContr.
        eapply LJAllL with (t:=x1)...
        
        eapply PermutationLEncode in H6;[|exact H5].
        
        eapply (H x0)...
        apply ForallCons...
        specialize(H13 x1 H9).
        apply lbindEq in H11...
        
        rewrite H11 in H13...
        
        rewrite <- H6.
        rewrite <- H5...
      }
      { (* case SOME *)
        apply AppSOMEALLLeft in H9.
        CleanContext.
        
        inversion H8...
        inversion H5...
        InForall2.
        
        assert(HF: isOLFormulaL (t_quant SOME FX :: x1)).
        symmetry in H6.
        rewrite H6 in H0;auto. 
        inversion HF...
        
        apply (LJEx H6).
        apply LJContr.
        eapply LJEXL...
        intros.
        
        eapply PermutationLEncode in H6;[|exact H5].
        
        eapply (H x0)...
        apply ForallCons...
        specialize(H12 x2 H13).
        apply lbindEq in H10...
        
        rewrite H10 in H12...
        
        rewrite <- H6.
        rewrite <- H5...
      }
  + (* init *)
    apply Init_inversion1 in H6;[|apply (isOLLencode H0)]...
    
    InForall2. (* OO in L *)
    apply (LJEx H7).
    apply LJinit.
Qed.

Theorem Adequacy:  forall L F , 
    isOLFormulaL L ->
    isOLFormula F ->
    (
      seq OLTheory  (LEncode L) [ REncode F] (> []) <->
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
