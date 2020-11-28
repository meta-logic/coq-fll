(** * System MALL for propositional multiplicative and additive linear logic

This file encodes the inference rules of the system MALL (two sided)
of propositional multiplicative additive linear logic.
 *)

Require Export FLL.OL.OLCutElimTheorem.
Require Import Coq.Init.Nat.
Require Import FLL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

 
(** ** Syntax *)
(* No units *)
Inductive Constants := .
(* conjunction, disjunction and implication *)
Inductive Connectives := TENSOR | PAR | WITH | OPLUS .
(* no quantifiers *)
Inductive Quantifiers := .
(* no unary connectives *) 
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
  match c return ruleCte with
  end.

(** *** Unary connectives *)
Definition rulesUC  (c:uconnectives) :=
  match c return ruleUnary with
  end.

(** *** Binary connectives *)
Definition rulesBC (c :connectives) :=
  match c with
  | TENSOR => {| rb_rightBody := fun F G => (atom (up F)) ** (atom (up G) );
                 rb_leftBody  := fun F G => (atom (down F) ) $ (atom (down G)) |}
  | PAR => {| rb_rightBody := fun F G => (atom (up F)) $ (atom (up G) );
              rb_leftBody  := fun F G => (atom (down F) ) ** (atom (down G)) |}
  | WITH => {| rb_rightBody := fun F G => (atom (up F)) & (atom (up G) );
                 rb_leftBody  := fun F G => (atom (down F) ) op (atom (down G)) |}
  | OPLUS => {| rb_rightBody := fun F G => (atom (up F)) op (atom (up G) );
             rb_leftBody  := fun F G => (atom (down F) ) & (atom (down G)) |}
  end.

(** *** Quantifiers *)
Definition rulesQC (c :quantifiers) :=
  match c return ruleQ with
  end.


Instance SimpleOORUles : OORules :=
  {|
    rulesCte := rulesCTE ;
    rulesUnary := rulesUC ;
    rulesBin := rulesBC;
    rulesQ := rulesQC
  |}.

(** ** Well-formedness conditions *)



(** *** Constants *)
Lemma wellFormedConstant_p : wellFormedCte.
Proof with WFSolver.
  unfold wellFormedCte;intros.
  destruct lab.
Qed.


(** *** Unary connectives *)

Lemma wellFormedUnary_p : wellFormedUnary.
Proof with WFSolver.
  unfold wellFormedUnary;intros.
  destruct lab.
Qed.


(** *** Binary connectives *)
Lemma wellFormedBinary_p : wellFormedBinary.
Proof with WFSolver.
  unfold wellFormedBinary;intros.
  destruct lab;destruct s.
  + (* Conjunction left *)
  exists BOneP...
  apply ANDL_Par.
  + (* Conjunction right *)
  exists BTwoPM...
  apply ANDR_Tensor.
  + (* Disjunction left *)
    exists BTwoPM...
    intros n HSeq HIs...
    FLLInversionAll...
    ++ (* linear case *)
    exists M0.
       exists N0.
       exists [atom (down Fo1)].
       exists [atom (down Go1)].
       exists (@nil oo). exists (@nil oo).
       eexists. exists 4...
       left...
       rewrite H1...
       tensor M0 N0...
       decide3 (makeLRuleBin PAR Fo1 Go1)...
       tensor [ (atom (down (t_bin PAR Fo1 Go1)))] (Delta1 ++ Delta2).
       tensor .
    ++ (* classical case *)
      exists M0.
       exists N0.
       exists [atom (down Fo1)].
       exists [atom (down Go1)].
       exists (@nil oo). exists (@nil oo).
       eexists. exists 4...
       right...
       rewrite H1...
       tensor M0 N0...
       decide3 (makeLRuleBin PAR Fo1 Go1)...
       tensor (@nil oo) (Delta1 ++ Delta2)...
       tensor Delta1 Delta2.
       
  + (* Disjunction right *)
    exists BOneP...
    intros n HSeq HIs...
    FLLInversionAll.

    exists   ([atom (up Fo1)] ++ [atom (up Go1)]). exists (@nil oo).
    eexists. exists 5...
    rewrite H1.
    left.
    exists N...
    decide3  (perp (up (t_bin PAR Fo1 Go1)) ** (atom (up Fo1) $ atom (up Go1))).
    tensor [ (atom (up (t_bin PAR Fo1 Go1)))] Delta1.
    solveLL...

    exists   ([atom (up Fo1)] ++ [atom (up Go1)]). exists (@nil oo).
    eexists. exists 5...
    rewrite H1.
    right...
    decide3  (perp (up (t_bin PAR Fo1 Go1)) ** (atom (up Fo1) $ atom (up Go1))).
    tensor (@nil oo) Delta1.
    solveLL...

  + (* With Left *)
    exists BOneP...
    intros n HSeq HIs...
    FLLInversionAll.

    exists  [atom (down Fo1)]. exists (@nil oo).
    eexists. exists 4...
    rewrite H1.
    left.
    exists N...
    apply tri_plus1'...
    decide3  (perp (down (t_bin WITH Fo1 Go1)) ** (atom (down Fo1) op atom (down Go1))).
    tensor [ (atom (down (t_bin WITH Fo1 Go1)))] Delta1.

    exists  [atom (down Fo1)]. exists (@nil oo).
    eexists. exists 4...
    rewrite H1.
    right...
    apply tri_plus1'...
    decide3  (perp (down (t_bin WITH Fo1 Go1)) ** (atom (down Fo1) op atom (down Go1))).
    tensor (@nil oo) Delta1.

    exists  [atom (down Go1)]. exists (@nil oo).
    eexists. exists 4...
    rewrite H1.
    left.
    exists N...
    apply tri_plus2'...
    decide3  (perp (down (t_bin WITH Fo1 Go1)) ** (atom (down Fo1) op atom (down Go1))).
    tensor [ (atom (down (t_bin WITH Fo1 Go1)))] Delta1.

    exists  [atom (down Go1)]. exists (@nil oo).
    eexists. exists 4...
    rewrite H1.
    right...
    apply tri_plus2'...
    decide3  (perp (down (t_bin WITH Fo1 Go1)) ** (atom (down Fo1) op atom (down Go1))).
    tensor (@nil oo) Delta1.
  + (* with right *)
    exists BTwoPA...
    intros n HSeq HIs...
    FLLInversionAll...
    ++ exists N.
       exists [atom (up Fo1)]. 
       exists [atom (up Go1)].
       exists (@nil oo). exists (@nil oo).
       eexists. exists 4...
       rewrite H1.
       left...
       decide3 (makeRRuleBin WITH Fo1 Go1)...
       tensor [(atom (up (t_bin WITH Fo1 Go1)))] Delta12.

    ++ exists N.
       exists [atom (up Fo1)].
       exists [atom (up Go1)].
       exists (@nil oo). exists (@nil oo).
       eexists. exists 4...
       rewrite H1.
       right...
       decide3 (makeRRuleBin WITH Fo1 Go1)...
       tensor (@nil oo) Delta12...
  + (* Oplus Left *)
    exists BTwoPA...
    apply ORL_With.
    
  + (* Oplus Right *)
    exists BOneP...
    apply ORR_Plus.
Qed.



(** *** Quantifiers *)
Lemma wellFormedQuantifier_p : wellFormedQuantifier.
Proof with solveF.
  unfold wellFormedQuantifier. intros.
  destruct lab.
Qed.

Lemma wellFormedTheory_p : wellFormedTheory.
  split.
  apply wellFormedConstant_p.
  split.
  apply wellFormedUnary_p.
  split; [apply wellFormedBinary_p | apply wellFormedQuantifier_p].
Qed.

(** ** Cut-coherency properties *)

(** *** Binary Connectives *)
Lemma CutCoherenceTENSOR: CutCoherenceBin (rulesBC TENSOR).
Proof with solveF.
  unfold CutCoherenceBin;intros.
  simpl.
  solveLL.
  decide3 ((atom (up F) ) ** (atom (down F) )). econstructor;eauto using le_max_l.
  tensor [perp (up F) ] [perp (up G); perp (down F) ** perp (down G)];solveLL.
  decide3 ((atom (up G) ) ** (atom (down G) )). econstructor;eauto using le_max_r.
  tensor [perp (up G) ] [ perp (down F) ** perp (down G); atom (down F)];solveLL.
  
  decide1 ((perp (down F) ) ** perp (down G) ).
  tensor [atom (down F) ] [atom (down G) ].
Qed.

Lemma CutCoherencePAR: CutCoherenceBin (rulesBC PAR).
Proof with solveF.
  unfold CutCoherenceBin;intros.
  simpl.
  solveLL.
  decide3 ((atom (up F) ) ** (atom (down F) )). econstructor;eauto using le_max_l.
  tensor  [perp (up F) ** perp (up G); perp (down G)] [perp (down F) ]  ;solveLL.
  decide3 ((atom (up G) ) ** (atom (down G) )). econstructor;eauto using le_max_r.
  tensor  [perp (up F) ** perp (up G); atom (up F)][perp (down G)]   ;solveLL.
  decide1 (perp (up F) ** perp (up G)) .
  tensor [atom (up F) ][ atom (up G)].
Qed.

Lemma CutCoherenceWITH: CutCoherenceBin (rulesBC WITH).
Proof with solveF.
  unfold CutCoherenceBin;intros.
  simpl.
  solveLL.
  
  decide3 ((atom (up F) ) ** (atom (down F) )). econstructor;eauto using le_max_l.
  tensor[perp (up F) op perp (up G)] [perp (down F)]  ;solveLL.
  decide1 (perp (up F) op perp (up G)).

  decide3 ((atom (up G) ) ** (atom (down G) )). econstructor;eauto using le_max_r.
  tensor[perp (up F) op perp (up G)] [perp (down G)]  ;solveLL.
  decide1 (perp (up F) op perp (up G)).
Qed.


Lemma CutCoherenceOPLUS: CutCoherenceBin (rulesBC OPLUS).
Proof with solveF.
  unfold CutCoherenceBin;intros.
  simpl.
  solveLL.
  
  decide3 ((atom (up F) ) ** (atom (down F) )). econstructor;eauto using le_max_l.
  tensor [perp (up F)]  [perp (down F) op perp (down G)]  ;solveLL.
  decide1 (perp (down F) op perp (down G)).

  decide3 ((atom (up G) ) ** (atom (down G) )). econstructor;eauto using le_max_r.
  tensor [perp (up G)]  [perp (down F) op perp (down G)]  ;solveLL.
  decide1 (perp (down F) op perp (down G)).
Qed.


Lemma CutCoherence_p : CutCoherence .
  split;intros; try destruct lab.
  split;intros; try destruct lab.
  split;intros; try destruct lab;
    auto using CutCoherenceOPLUS, CutCoherenceWITH, CutCoherenceTENSOR, CutCoherencePAR.
Qed.

(** The theory is well formed: cut-coherence holds and all the rules
are bipoles *)
Lemma wellTheory_p : wellTheory.
  split;auto using CutCoherence_p,  wellFormedTheory_p.
Qed.

Hint Unfold  OLTheoryIsFormula ConstantsFormulas UConnectivesFormulas ConnectivesFormulas QuantifiersFormulas : core .
Hint Unfold  OLTheoryIsFormulaD ConstantsFormulasD UConnectivesFormulasD ConnectivesFormulasD QuantifiersFormulasD :core.

Theorem  OLTheoryIsFormula_p :  OLTheoryIsFormula.
Proof with SolveIsFormulas.
  split;autounfold...
  intro;destruct lab...
Qed.

Theorem  OLTheoryIsFormulaD_p :  OLTheoryIsFormulaD.
Proof with SolveIsFormulas.
  split;autounfold...
  intro;destruct lab...
Qed.

(** ** Adequacy 

Now we prove that the encoding is sound and complete. For that, we
define the provability relation of MALL as an inductive definition *)

Notation "F *** G" := (t_bin TENSOR F G) (at level 10) .
Notation "F $$$ G" := (t_bin PAR F G) (at level 10) .
Notation "F 'ooo' G" := (t_bin OPLUS F G) (at level 10) .
Notation "F &* G" := (t_bin WITH F G) (at level 10) .



Inductive MALLSeq : list uexp -> list uexp -> Prop :=
| MALLInit : forall F , MALLSeq [F] [F]
| MALLTensorR : forall L1 L2 L1' L2' F G, MALLSeq L1 (F :: L2) -> MALLSeq L1' (G :: L2') -> MALLSeq  (L1 ++ L1') (F *** G :: (L2 ++ L2'))
| MALLTensorL : forall L1 L2 F G, MALLSeq (F :: G :: L1) L2 -> MALLSeq (F *** G :: L1) L2
| MALLParR : forall L1 L2 F G, MALLSeq L1 (F :: G :: L2) -> MALLSeq L1 (F $$$ G :: L2)
| MALLParL :forall L1 L2 L1' L2' F G, MALLSeq (F :: L1) L2 -> MALLSeq (G :: L1') L2' -> MALLSeq (F $$$ G :: L1 ++ L1') (L2 ++ L2')
| MALLOpRE1 : forall L1 L2 F G, MALLSeq L1 (F :: L2) -> MALLSeq L1 (F ooo G :: L2)
| MALLOpRE2 : forall L1 L2 F G, MALLSeq L1 (G :: L2) -> MALLSeq L1 (F ooo G :: L2)
| MALLOpL : forall L1 L2 F G, MALLSeq (F :: L1) L2 -> MALLSeq (G :: L1) L2 -> MALLSeq (F ooo G :: L1) L2
| MALLWithR : forall L1 L2 F G, MALLSeq L1 (F :: L2) -> MALLSeq L1 (G :: L2) -> MALLSeq L1 (F &* G :: L2)
| MALLWithL1 : forall L1 L2 F G, MALLSeq (F :: L1) L2 ->  MALLSeq (F &* G :: L1) L2
| MALLWithL2 : forall L1 L2 F G, MALLSeq (G :: L1) L2 ->  MALLSeq (F &* G :: L1) L2
| MALLExR : forall  L1 L2 L2', Permutation L2 L2' -> MALLSeq L1 L2' -> MALLSeq L1 L2
| MALLExL : forall  L1 L2 L1', Permutation L1 L1' -> MALLSeq L1' L2 -> MALLSeq L1 L2
.

Global Instance MALLL_morph : 
  Proper ((@Permutation uexp) ==> (@Permutation uexp) ==> iff) (MALLSeq).
Proof.
  unfold Proper; unfold respectful. 
  intros.
  split;intros;subst.
  eapply MALLExR with (L2':=x0);auto. apply Permutation_sym;auto.
  eapply MALLExL with (L1':=x);auto. apply Permutation_sym;auto.
  eapply MALLExR with (L2':=y0);auto.
  eapply MALLExL with (L1':=y);auto. 
Qed.

Ltac solveOLTheory :=
  try
    match goal with
    | [|- OLTheory _] =>
      first [ apply ooth_init ; auto ; SolveIS
            | do 2 constructor;auto ; SolveIS ]
    end.


Hint Unfold LEncode REncode : core .
Theorem Soundeness: forall L1 L2, MALLSeq L1 L2 ->
                                isOLFormulaL L1 ->
                                isOLFormulaL L2 ->
                                seq OLTheory []  ( (LEncode L1) ++  (REncode L2)) (> []).
Proof with solveF;solveLL;solveOLTheory;SolveIS;solveOLTheory. 
  intros.
  induction H. 
  + (* init *)
    decide3 (RINIT F)...
    tensor (REncode [F]) (LEncode [F]).
  + (* TensorR *)
    decide3 (makeRRuleBin TENSOR  F G)...      
    tensor [u| F *** G |] ( LEncode (L1 ++ L1') ++  REncode (L2 ++ L2')).
    
    assert (Permutation (LEncode (L1 ++ L1') ++ REncode (L2 ++ L2')) ((LEncode L1 ++ REncode L2 ) ++ (LEncode L1' ++ REncode L2' ))).
    autounfold; repeat rewrite map_app...
    rewrite H3.
    tensor (LEncode L1 ++ REncode L2)(LEncode L1' ++ REncode L2').
    sLLPerm ((LEncode L1 ++ (REncode (F ::L2)))).
    apply IHMALLSeq1...
    apply ForallAppInv1 in H0...
    apply ForallAppInv1 in H7...
    sLLPerm ((LEncode L1' ++ (REncode (G ::L2')))).
    apply IHMALLSeq2...
    apply ForallAppInv2 in H0...
    apply ForallAppInv2 in H7...
  + (* TensorL *)
    decide3 (makeLRuleBin TENSOR  F G)...
    tensor  [d| F *** G |]  (LEncode L1 ++ REncode L2).
    sLLPerm ( LEncode( F :: G :: L1) ++ REncode L2).
    apply IHMALLSeq...
  + (* Par Right *)
    decide3 (makeRRuleBin PAR  F G)...
    tensor  [u| F $$$ G |] (LEncode L1 ++ REncode L2).
    sLLPerm ( (LEncode L1) ++ REncode (F :: G :: L2)).
    apply IHMALLSeq...
  + (* Par Left *)
    decide3 (makeLRuleBin PAR  F G)...
    tensor [d| F $$$ G|]  (LEncode (L1 ++ L1') ++ REncode (L2 ++ L2')).
    assert (Permutation (LEncode (L1 ++ L1') ++ REncode (L2 ++ L2')) ((LEncode L1 ++ REncode L2 ) ++ (LEncode L1' ++ REncode L2' ))).
    autounfold; repeat rewrite map_app...
    rewrite H3.
    tensor (LEncode L1 ++ REncode L2)(LEncode L1' ++ REncode L2').
    sLLPerm (LEncode (F::L1) ++ REncode L2).
    apply  IHMALLSeq1...
    apply ForallAppInv1 in H7...
    apply ForallAppInv1 in H1...
    sLLPerm (LEncode (G::L1') ++ REncode L2').
    apply  IHMALLSeq2...
    apply ForallAppInv2 in H7...
    apply ForallAppInv2 in H1...
  + (* Oplus1 *)
    decide3 (makeRRuleBin OPLUS  F G)...
    tensor [u| F ooo G |] (LEncode L1 ++ REncode L2).
    oplus1.
    sLLPerm ( (LEncode L1) ++ (REncode (F :: L2))).
    apply IHMALLSeq...
  + (* Oplus2 *)
    decide3 (makeRRuleBin OPLUS  F G)...
    tensor [u| F ooo G |] (LEncode L1 ++ REncode L2).
    oplus2.
    sLLPerm ( (LEncode L1) ++ (REncode (G :: L2))).
    apply IHMALLSeq...
  + (* Oplus Left *)
    decide3 (makeLRuleBin OPLUS  F G)...
    tensor [d| F ooo G |] (LEncode L1 ++ REncode L2).
    sLLPerm ( LEncode ( F:: L1) ++ REncode L2).
    apply IHMALLSeq1...
    sLLPerm ( LEncode ( G:: L1) ++ REncode L2).
    apply IHMALLSeq2...
  + (* With R *)
    decide3 (makeRRuleBin WITH  F G)...
    tensor [u| F &* G |] (LEncode L1 ++ REncode L2).
    sLLPerm ( LEncode L1  ++ REncode (F::L2)).
    apply IHMALLSeq1...
    sLLPerm ( LEncode L1  ++ REncode (G::L2)).
    apply IHMALLSeq2...
  + (*WithL 1 *)
    decide3 (makeLRuleBin WITH  F G)...
    tensor [d| F &* G |] (LEncode L1 ++ REncode L2).
    oplus1.
    sLLPerm ( LEncode (F ::L1)  ++  REncode L2).
    apply IHMALLSeq...
  + (*WithL 2 *)
    decide3 (makeLRuleBin WITH  F G)...
    tensor [d| F &* G |] (LEncode L1 ++ REncode L2).
    oplus2.
    sLLPerm ( LEncode (G ::L1)  ++  REncode L2).
    apply IHMALLSeq...
  + (* Exchange *)
    eapply Permutation_map in  H as H'.
    unfold REncode; rewrite H'...
    apply IHMALLSeq...
    rewrite <- H...
  + (* Exchange *)
    eapply Permutation_map in  H as H'.
    unfold LEncode; rewrite H'...
    apply IHMALLSeq...
    rewrite <- H...
Qed.

Ltac toMALL H :=
  match (type of H) with
  | In (u| _ |)(LEncode _ ++ REncode _) =>
    apply upRight in H; apply OLInPermutation in H;CleanContext;
    eapply MALLExR; [apply Permutation_sym; eauto|]
  | In (d| _ |)(LEncode _ ++ REncode _) =>
    apply downLeft in H; apply OLInPermutationL in H;CleanContext;
    eapply MALLExL; [apply Permutation_sym;eauto | ]
  | seqN _ _ (u| ?F | :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := LEncode L ++ REncode (F :: R)) in H ;[| simpl; perm]
  | seqN _ _ (u| ?F | :: ?T :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := T :: LEncode L ++ REncode (F :: R)) in H ;[| simpl; perm]
  | seqN _ _ (d| ?F | :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := LEncode (F :: L) ++ REncode R) in H ;[| simpl; perm]
  | seqN _ _ (d| ?F | :: ?T :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := T :: LEncode (F::L) ++ REncode R) in H ;[| simpl; perm]
  end.


(* Theorem Permutation_app_map:forall {T:Type} (A B: list T),
    Permutation A B ->
    exists A1 A2 B1 B2,
      Permutation A  (A1 ++ A2) /\
      Permutation B  (B1 ++ B2) /\
      Permutation A1 B1 /\
      Permutation A2 B2.
      
Proof.
  Search Permutation.
  induction A;simpl;intros.
  apply Permutation_nil in H;subst.
  do 4 exists [].
              firstorder.
              destruct B.
              apply Permutation_nil' in H;inversion H.
              apply PProp_perm_select in H.
              destruct H;CleanContext.
              { apply IHA in H0;CleanContext.
                rewrite H.
                rewrite H0.

   *)
  

Theorem ListPartition: forall {A:Type} (L: list A),
    exists L1 L2, Permutation L (L1 ++ L2).
  induction L;intros.
  exists [].
  exists [];perm.
  CleanContext.
  exists (a::x).
  exists x0.
  simpl.
  constructor.
  rewrite H;auto.
Qed.
  


Theorem Completeness: forall n L1 L2,
    seqN OLTheory n []  ( (LEncode L1) ++  (REncode L2)) (> []) ->
    MALLSeq L1 L2.
Proof with solveF;solveLL;solveOLTheory;SolveIS;solveOLTheory.
  induction n using strongind;intros L1 L2 Hseq  ; inversion Hseq;subst...
  apply Remove_In in H2...
  apply InIsPositive in H2 ;contradiction. 
  
  inversion H1...
  + (* from the theory *)
    inversion H0;subst;destruct C.
    ++ (* tensor right *)
      FLLInversionAll;CleanContext.
      apply Permutation_sym in H7;simpl in H7.
      apply PermutationInCons in H7 as H7'.
      apply upRight in H7'.
      apply OLInPermutation in H7';CleanContext.
      rewrite H2 in H7;rewrite H2.
      simpl in H7.
      rewrite <- perm_takeit_2 in H7.
      apply Permutation_cons_inv in H7.
      rewrite H6 in H7.
      generalize( ListPartition x);intro;CleanContext.
      generalize( ListPartition L1);intro;CleanContext.
      rewrite H3 in H7;rewrite H3.
      rewrite H5 in H7; rewrite H5.
      apply MALLTensorR.
Abort.
      


  
(** The cut-elimination theorem instantiated for LK *)
Check OLCutElimination wellTheory_p OLTheoryIsFormula_p OLTheoryIsFormulaD_p.
