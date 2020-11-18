(** * System LK for propositional classical logic encoded as an LL theory

This file encodes the inference rules of the system LK (propositional
classical logic). The cut-coherence and well-formedness properties are
proved and then, using [OLCutElimination] we prove the cut-elimination
theorem for this system .
 *)

Require Export FLL.OL.OLCutc.
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
  | IMP => TENSORPAREXCH
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


Inductive LKSeq : list uexp -> list uexp -> Prop :=
| LKTRUE : forall L L', LKSeq L ((t_cons TT)::L')
| LKFALSE : forall L L', LKSeq (t_cons FF :: L) L' 
| LKinit : forall L L' F,  LKSeq (F:: L) (F::L')
| LKAndL : forall L F G L', LKSeq (F :: G :: L) L' -> LKSeq ( (t_bin AND F G) :: L) L'
| LKAndR : forall L F G L' , LKSeq L (F::L') -> LKSeq L (G::L') -> LKSeq L (t_bin AND F G :: L')
| LKOrL : forall L F G L',  LKSeq (F :: L) L' ->  LKSeq (G :: L) L' -> LKSeq ( (t_bin OR F G) :: L) L'
| LKOrR1 : forall L F G L' , LKSeq L (F::G::L') -> LKSeq L (t_bin OR F G :: L')
| LKImpL : forall L A B L' , LKSeq L (A::L') -> LKSeq (B:: L) L' -> LKSeq (t_bin IMP A B ::L) L'
| LKImpR : forall L A B L' , LKSeq (A:: L) (B::L') ->  LKSeq L (t_bin IMP A B :: L')
| LKAllL : forall L t FX L', uniform FX -> proper t -> LKSeq( FX t :: L) L' -> LKSeq (t_quant ALL FX :: L) L'
| LKAllR : forall L FX L' , uniform FX -> (forall x, proper x -> LKSeq L ((FX x)::L')) -> LKSeq L (t_quant ALL FX :: L')
| LKEXL : forall L FX L', uniform FX -> (forall x, proper x -> LKSeq (FX x:: L) L') -> LKSeq (t_quant SOME FX :: L) L'
| LKEXR : forall L FX t L', uniform FX -> proper t -> LKSeq L ((FX t)::L')-> LKSeq L (t_quant SOME FX::L')
(* Explicit exchange *)
| LKExL : forall L L' Delta, Permutation L L' -> LKSeq L Delta -> LKSeq L' Delta
| LKExR : forall L L' Delta, Permutation L L' -> LKSeq Delta L -> LKSeq Delta L'
.

Hint Constructors LKSeq : core .

Definition LEncode L := map (fun x => d| x|) L.
Definition REncode L := map (fun x => u| x|) L.


Hint Constructors OLTheory buildTheory : core.
Hint Constructors  isOLFormula : core. 


Lemma isOLLencode : forall L, isOLFormulaL L -> IsPositiveLAtomFormulaL (LEncode L).
Proof with subst;auto.
  intros.
  induction L. simpl...
  constructor.
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


Theorem Soundeness: forall L L', LKSeq L L' ->
                                isOLFormulaL L ->
                                isOLFormulaL L' ->
                                seq OLTheory (LEncode L ++  REncode L') [] (> []).
Proof with solveF;solveLL;simplOLFormulas.
  intros.
  induction H. 
  + (* True on the right *)
    decide3 (makeRuleConstant TT Right)...
    apply in_or_app...
  + (* false on the left *)
    decide3 (makeRuleConstant FF Left)...
  + (* init *)
    decide3 (RINIT F).
    apply ooth_init... inversion H0...
    tensor (@nil oo) (@nil oo)...
    right...
    apply in_or_app...
  + (* ANDL1 *)
    decide3 (makeRuleBin AND Left F G)...      
    LLPerm (d| t_bin AND F G | :: d| F | ::  d| G | :: (LEncode L ++ REncode L')).
    apply weakening.
    apply IHLKSeq...
    inversion H4...
    inversion H4...
  + (* And R *)
    decide3 (makeRuleBin AND Right F G)...
    apply in_or_app...
    LLPerm (u| t_bin AND F G | :: (LEncode L ++ ( u| F | :: REncode L') )) .
    apply weakening...
    apply IHLKSeq1...
    LLPerm (u| t_bin AND F G | :: (LEncode L ++ ( u| G | :: REncode L') )) .
    apply weakening...
    apply IHLKSeq2...
    
  + (* Or L *)
    decide3 (makeRuleBin OR Left F G)...
    apply weakening. LLPerm( ( d| F | :: LEncode L) ++ REncode L').
    apply IHLKSeq1...  inversion H5...
    
    apply weakening. LLPerm( ( d| G | :: LEncode L) ++ REncode L').
    apply IHLKSeq2... inversion H6...
  +  (* OrR *)
    decide3 (makeRuleBin OR Right F G)...
    apply in_or_app...
    LLPerm ( u| t_bin OR F G | :: (LEncode L  ++  (u| F | :: u| G | ::  REncode L') )) .
    apply weakening.
    apply IHLKSeq...
    inversion H4...
    inversion H4...
  
  + (* implication left *)
    decide3 (makeRuleBin IMP Left A B)...
    apply weakening.
    LLPerm  ((LEncode L ++ (u| A | :: REncode L'))).
    apply IHLKSeq1... inversion H5...
    apply weakening.
    LLPerm ( (d| B | :: LEncode L) ++ REncode L').
    apply IHLKSeq2... inversion H5...
    
  + (* implication right *)
    decide3 (makeRuleBin IMP Right A B)... 
    apply in_or_app...
    LLPerm  ( u| t_bin IMP A B | :: ( d| A | :: LEncode L) ++ ( u| B | :: REncode L') ).
    apply weakening.
    apply IHLKSeq...
    inversion H4...
    inversion H4...
  + (* forall left *)
    decide3 (makeRuleQ ALL Left FX)...
    existential t...
    apply weakening.
    LLPerm (( d| FX t | :: LEncode L) ++ REncode L' ).
    apply IHLKSeq...
    apply lbindEq in H9;auto.
    rewrite <-H9...
  + (* forall right *)
    decide3 (makeRuleQ ALL Right FX)...
    apply in_or_app...
    LLPerm (u| t_quant ALL FX | :: (LEncode L ++ (u| FX x | ::REncode L') )).
    apply weakening...
    apply H3...
    apply lbindEq in H9;auto.
    rewrite <- H9...
  + (* existst left *)
    decide3 (makeRuleQ SOME Left FX)... 
    apply weakening...
    
    LLPerm (( d| FX x | :: LEncode L) ++ REncode L') .
    apply H3...
    apply lbindEq in H9;auto.
    rewrite <- H9...
  + (* exists right *)
    decide3 (makeRuleQ SOME Right FX)...
    apply in_or_app...
    existential t...
    LLPerm  (u| t_quant SOME FX | :: (LEncode L ++ u| FX t | :: REncode L') ).
    apply weakening...
    apply IHLKSeq...
    apply lbindEq in H9...
    rewrite <- H9...
  + (* exchange *)
    simplOLFormulas.
    rewrite <- H4...
  + assert(isOLFormulaL L);[apply (PermuteMap H1);symmetry;auto|];
      assert(Permutation (REncode L) (REncode L'));[apply Permutation_map; auto|].
    rewrite <- H4...
Qed.

Theorem NoDinR : forall F L, In (d| F|) (REncode L) -> False .
  intros.
  induction L;auto.
  simpl in H.
  destruct H;auto.
  inversion H.
Qed.

Theorem NoUinL : forall F L, In (u| F|) (LEncode L) -> False .
  intros.
  induction L;auto.
  simpl in H.
  destruct H;auto.
  inversion H.
Qed.
  
Theorem downLeft : forall L L' F,
    In (d| F |) (LEncode L ++ REncode L') ->
    In (d| F |) (LEncode L).
  intros.
  apply in_app_or in H.
  destruct H;auto.
  apply NoDinR in H.
  contradiction.
Qed.

Theorem upRight : forall L L' F,
    In (u| F |) (LEncode L ++ REncode L') ->
    In (u| F |) (REncode L').
  intros.
  apply in_app_or in H.
  destruct H;auto.
  apply NoUinL in H.
  contradiction.
Qed.

Theorem OLInPermutation: forall L F,
    In (u| F |) (REncode L) ->
    exists L', Permutation L (F:: L').
  induction L;intros.
  inversion H.
  simpl in H.
  inversion H.
  inversion H0;subst.
  eexists;eauto.
  apply IHL in H0.
  CleanContext.
  exists (a:: x).
  rewrite H0;perm.
Qed.
  
Theorem Completeness: forall n L L' , 
    isOLFormulaL L ->
    isOLFormulaL L' ->
    seqN OLTheory n (LEncode L ++  REncode L') [] (> []) ->
    LKSeq L L' .
Proof with solveF;solveLL.
  induction n using strongind;intros.
  inversion H1.

  inversion H2...
  inversion H5...
  unfold REncode in H5... unfold LEncode in H5...
  admit.
  inversion H4...
  + (* from the theory *)
    inversion H3...
    ++ (* Constant right *)
      apply FocusingRightCte in H6;[| admit].
      CleanContext.
      (* by cases on C *)
      destruct C;simpl in H8...
      admit.
      inversion H8... (* there is no proof o zero *)
    ++  (* constant left *)
      apply FocusingLeftCte in H6.
      CleanContext.
      destruct C;simpl in H8...
      inversion H8...
      apply downLeft in H6.
      InForall1.
      apply (LKExL Ht')...
      admit.
    ++ (* binary connective right *)
      apply FocusingRightRule in H6;[|admit].
      CleanContext.
      apply upRight in H6.
      (* by cases on C *)
      destruct C;simpl in H8...
      { (* case AND *)
        apply AppPARTENSORRight in H8.
        CleanContext.
        apply OLInPermutation in H6;CleanContext. apply Permutation_sym in H5.
        apply (LKExR H5)...
        apply LKAndR.
        apply (H x0);solveIsOLFormL.
        admit. simpl. LLExact H8.
        apply (H x0);solveIsOLFormL. 
      }
      { (*  OR *)
        apply AppWITHPLUSRight in H8.
        CleanContext.
        destruct H8.
        apply LKOrR1.
        apply (H x0);solveIsOLFormL. 
        apply LKOrR2.
        apply (H x0);solveIsOLFormL. 
      }
      { (* impl *)
        apply AppTENSORPARRight in H8.
        CleanContext.
        apply LKImpR.
        apply (H x0);solveIsOLFormL... 
      }
    ++  (* binary connective left *)
      apply FocusingLeftRule in H6;[|apply (isOLLencode H0)].
      CleanContext.
      (* by cases on C *)
      destruct C;simpl in H8...
      { (* case AND *)
        apply AppPLUSWITHLeft in H8.
        CleanContext.
        destruct H8.
        + apply InLEncode in H6.
          apply InPermutation in H6.
          destruct H6.
          assert(Hp : Permutation (LEncode L) (d| t_bin AND F1 G | :: LEncode x)).
          
          eapply Permutation_map in H6.
          simpl in H6. exact H6.
          symmetry in H6.
          
          assert(HF: isOLFormulaL (t_bin AND F1 G :: x)). 
          rewrite H6;auto.
          
          apply (LKEx H6).
          apply LKContr. 
          apply LKAndL1.

          eapply (H x0)...
          apply ForallCons...
          inversion HF.
          solveIsOLFormL.

          rewrite  <- Hp...
        + InForall2.
          assert(HF: isOLFormulaL (t_bin AND F1 G :: x1)). 
          symmetry in H6.
          rewrite H6 in H0;auto. 
          
          apply (LKEx H6).
          apply LKContr.
          apply LKAndL2.
          
          eapply PermutationLEncode in H6;[|exact H8].
          
          eapply (H x0)...
          
          inversion HF...
          solveIsOLFormL.

          rewrite  <- H6.
          rewrite <- H8...
      }
      { (*  OR *)
        apply AppWITHPLUSLeft in H8.
        CleanContext.
        InForall2.
        assert(HF: isOLFormulaL (t_bin OR F1 G :: x1)).
        symmetry in H6.
        rewrite H6 in H0;auto.
        
        inversion HF...
        
        apply (LKEx H6).
        apply LKContr.
        apply LKOrL.
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

        apply (LKEx H6).
        apply LKContr.
        apply LKImpL.
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
        apply LKAllR;intros...
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
        apply LKEXR with (t:=t)...
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
        
        apply (LKEx H6).
        apply LKContr.
        eapply LKAllL with (t:=x1)...
        
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
        
        apply (LKEx H6).
        apply LKContr.
        eapply LKEXL...
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
    apply (LKEx H7).
    apply LKinit.
Qed.

Theorem Adequacy:  forall L F , 
    isOLFormulaL L ->
    isOLFormula F ->
    (
      seq OLTheory  (LEncode L) [ REncode F] (> []) <->
      LKSeq L F ).
Proof with solveF;solveLL.
  intros.
  split;intros.
  + apply seqtoSeqN in H1;CleanContext.
    apply  Completeness in H1...
  +  apply Soundeness in H1...
Qed.
(** The cut-elimination theorem instantiated for LK *)
Check Adequacy .
Check CutElimination.

