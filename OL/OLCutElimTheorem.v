(** * LL as a Meta-logical framework.  *)

(** In this file we show how the cut-elimination procedure for FLL can
be used to prove cut-elimination for object logics that are
cut-coherent in the sense of Miller & Pimentel. Roughly, a system is
cut-coherent if the encoding of the right and left rules of each
connective are dual. *)

Require Export FLL.Misc.Hybrid.
Require Export FLL.OL.OLDefinitions.
Require Import Coq.Init.Nat.
Require Import FLL.SL.CutElimination.
Import FLL.Misc.Permutations.
Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
Hint Resolve proper_APP uniform_proper : hybrid.
Hint Unfold proper: hybrid.
Hint Rewrite ext_eq_eta : hybrid.
Hint Resolve uniform_id uniform_con uniform_app : hybrid.
Hint Resolve proper_VAR : hybrid.
Hint Resolve lbindEq exprInhabited : hybrid.
Hint Constructors uniform_oo : hybrid.
Hint Constructors seq seqN : core .
Hint Constructors uniform_oo : core.

Hint Constructors isFormula : core.
Hint Constructors isOLFormula : core.

Hint Constructors IsPositiveAtomFormula : core .

Hint Unfold IsPositiveAtomFormulaL : core. 
Hint Unfold makeLRuleConstant makeRRuleConstant makeLRuleUnary makeRRuleUnary makeLRuleBin makeRRuleBin makeLRuleQ makeRRuleQ : core.

Hint Unfold BiPoleCte BiPoleUnary BiPoleBinary BiPoleQuantifier : core .
Hint Unfold RINIT RCUT : core.
Hint Constructors theoryInitCut theoryCut : core.
Hint Constructors CutRuleN : core.
Hint Unfold CutCoherenceBin CutCoherenceQ  CutCoherence (*wellFormedConstant*) wellFormedUnary wellFormedBinary wellFormedQuantifier wellTheory  : core .
Hint Constructors  OLTheoryCut OLTheory : core.


(** ** Cut Elimination Procedure *)
Section CutElimination .
  Context `{OLR: OORules}.

  Ltac SolveSeqPerm := 
    repeat
      match goal with
        [ H : Permutation ?x ?z ,
              Hs : seqN OLTheory ?A ?B (?x ++ ?y) ?C |- _ ] =>
        assert(seqN OLTheory A B (z ++ y) C) by (refine (exchangeLCN _ Hs); rewrite H; perm);clear Hs 
      | [ H : Permutation ?x ?z ,
              Hs : seqN OLTheory ?A ?B (?y ++ ?x) ?C |- _ ] =>
        assert(seqN OLTheory A B (y ++ z) C) by (refine (exchangeLCN _ Hs); rewrite H; perm);clear Hs         
      end.
  
  
  (** Given a hypothesis of the form 
      [Permutation (F + :: N) (G + :: M)], if [F] and [G] are different 
        (E.g., different
        predicate symbols, or same predicate symbols under different
        object formulas [F] and [G]), such a difference is verified
        and a new premise is added: 
        [Permutation N (G + :: M') for some [M'] *)
  Ltac UpDownMismatch :=
    match goal with
      [ H : Permutation  ( ( atom (?pred1 ?F )) :: _ ) (( atom (?pred2 ?G )) :: _) |- _ ] =>
      try
        match pred2 with
        | pred1 =>
          match goal with
          | [ HA : isOLAtom F |- _] => inversion HA
          | [ HA : isOLAtom G |- _] => inversion HA
          end
        end;
      let H' := fresh "HDIFF" in
      let H'' := fresh "HDIFF" in
      let H''' := fresh "HDIFF" in
      let M := fresh "L" in
      assert (H' : (atom (pred1 F )) <> (atom (pred2 G )))
        by ( intro H'';subst;inversion H'');
      generalize (PermutationNeqIn H H');intro H''';clear H';
      destruct H''' as [M H'''];rewrite H''' in  H;
      apply Perm_swap_inv in H;
      subst
    end;SolveSeqPerm.


  (** As a general hypothesis, we assume that the Object logic
          is cut-coherent *)
  Hypothesis LTWell : wellTheory.
  (** We also assume that the rules of the OL are formulas satisfying the isFormula Property *)
  Definition ConstantsFormulas := forall (lab:constants),
      isFormula ((rulesCte lab).(rc_leftBody)) /\ isFormula ((rulesCte lab).(rc_rightBody)).
  Definition UConnectivesFormulas := forall (lab:uconnectives),
      forall F, isFormula ((rulesUnary lab).(ru_leftBody)  F) /\ isFormula ((rulesUnary lab).(ru_rightBody)  F).
  Definition ConnectivesFormulas := forall (lab:connectives),
      forall F G, isFormula ((rulesBin lab).(rb_leftBody)  F G) /\ isFormula ((rulesBin lab).(rb_rightBody)  F G).
  Definition QuantifiersFormulas := forall (lab:quantifiers),
      forall FX, isFormula ((rulesQ lab).(rq_leftBody) FX) /\ isFormula ((rulesQ lab).(rq_rightBody) FX).
  Definition OLTheoryIsFormula :=ConstantsFormulas /\ UConnectivesFormulas /\ ConnectivesFormulas /\QuantifiersFormulas.

  (** We also assume that the rules of the OL are formulas satisfying the isFormula Property *)
  Definition ConstantsFormulasD := forall (lab:constants),
      isFormula ( ((rulesCte lab).(rc_leftBody)) ^) /\ isFormula (((rulesCte lab).(rc_rightBody)) ^).
  Definition UConnectivesFormulasD := forall (lab:uconnectives),
      forall F, isFormula ( ((rulesUnary lab).(ru_leftBody)  F) ^) /\ isFormula (((rulesUnary lab).(ru_rightBody)  F) ^).
  Definition ConnectivesFormulasD := forall (lab:connectives),
      forall F G, isFormula (((rulesBin lab).(rb_leftBody)  F G) ^) /\ isFormula ( ((rulesBin lab).(rb_rightBody)  F G)^).
  Definition QuantifiersFormulasD := forall (lab:quantifiers),
      forall FX, isFormula (((rulesQ lab).(rq_leftBody) FX)^) /\ isFormula (((rulesQ lab).(rq_rightBody) FX)^).
  Definition OLTheoryIsFormulaD :=ConstantsFormulasD /\ UConnectivesFormulasD /\ ConnectivesFormulasD /\QuantifiersFormulasD.

  Hypotheses OLIsFormula : OLTheoryIsFormula.
  Hypotheses OLIsFormulaD : OLTheoryIsFormulaD.
  Hint Unfold  OLTheoryIsFormula ConstantsFormulas UConnectivesFormulas ConnectivesFormulas QuantifiersFormulas : core.
  Hint Unfold  OLTheoryIsFormulaD ConstantsFormulasD UConnectivesFormulasD ConnectivesFormulasD QuantifiersFormulasD :core.

  Theorem OLTheoryWellFormed : forall F, OLTheory F -> isFormula F.
    intros.
    destruct OLIsFormula as [HC [HU [HB HQ]]];autounfold in *.
    inversion H;subst.
    inversion H0;subst;autounfold;constructor;auto;firstorder.
    constructor;auto.
  Qed.

  Theorem OLTheoryCutWellFormed : forall F n,  (OLTheoryCut n) F -> isFormula F.
    intros. 
    destruct OLIsFormula as [HC [HU [HB HQ]]];autounfold in *.
    inversion H;subst.
    inversion H0;subst;autounfold;constructor;auto;firstorder.
    constructor;auto.
    inversion H0;subst.
    unfold RCUT.
    constructor;auto.
  Qed.

  Theorem OLTheoryWellFormedD : forall F, OLTheory F -> isFormula (F ^).
    intros.
    destruct OLIsFormulaD as [HC [HU [HB HQ]]];autounfold in *.
    inversion H;subst.
    inversion H0;subst;autounfold;simpl;constructor;auto;firstorder.
    constructor;auto.
  Qed.

  Theorem OLTheoryCutWellFormedD : forall F n,  (OLTheoryCut n) F -> isFormula (F^).
    intros.
    destruct OLIsFormulaD as [HC [HU [HB HQ]]];autounfold in *.
    inversion H;subst.
    inversion H0;subst;autounfold;simpl;constructor;auto;firstorder.
    simpl;auto.
    inversion H0;subst.
    unfold RCUT;simpl.
    constructor;auto.
  Qed.
  
  
  Lemma FocusAtomInv : forall Theory Gamma  A M n,
      ( seqN Theory n Gamma ( (atom A ) :: M) (> []) ) -> 
      ( seqN Theory (S (S n)) Gamma M (>> (atom A ) ) ).
    intros.
    solveLL.
    rewrite Permutation_app_comm ;auto.
  Qed.
  
  Lemma DerPosAtom_inv :
    forall G N A h P,  seqN P h G N (>> (atom A )) ->
                       exists m,
                         seqN P m G ((atom A ) :: N) (> []) /\
                         h = S (S m) .
    intros.
    FLLInversionAll.
    rewrite Permutation_app_comm in H7;simpl in H7.
    eauto.
  Qed.

  
  Ltac FocusStepAtom H :=
    let H' := fresh H in
    let x := fresh "h" in
    let x' := fresh in
    apply DerPosAtom_inv in H as H';
    destruct H' as [x H'];
    destruct H' as [H' x'];subst.


  
  (** Applies some permutation to match the hypothesis [Hcut]
          with the current goal *)
  Ltac FindSolution Hcut :=
    repeat(
        match goal with
          [ H : Permutation ?M _ |- _] => rewrite H
        end);
    repeat (rewrite app_assoc_reverse);
    repeat (rewrite app_assoc_reverse in Hcut);
    auto ;
    try rewrite <- Permutation_middle;CutTac;
    try rewrite <- Permutation_middle;CutTac;
    match type of Hcut with
    | (seq _ _ ?M _) =>
      apply exchangeLC with (LC:=M);auto;try SolvePermutation 
    end.

  (** During the proof of cut-elimination, there are many
          points where it is needed to decide, e.g., where the the
          atom [A] is [M] or [N] given that [Permutation (A :: _) (B
          :: M ++ N)]. This tactics takes care of generating the
          needed cases. *)

  Ltac CaseIn H :=
    let H' := fresh H"'" in
    
    match (type of H)  with
    (* case for 1 premise *)
    | Permutation (?F :: _) (_ :: _) =>
      apply Permutation_in with (x:= F) in H as H';CutTac;
      inversion H';CutTac;[idtac 
                          | match goal with
                            | [HH : In F _ |- _] =>
                              let L := fresh "L" in
                              apply InPermutation in HH;
                              destruct HH as [L HH];
                              rewrite HH in *; 
                              CleanContext
                            end
                          ]
    (* cases for 2 premises *)
    | Permutation (_ ++ _) ( (atom ?F ) :: _) =>
      apply Permutation_sym in H;
      CaseIn H
    | Permutation ((atom ?F ) :: _) (_ ++ _)  =>
      apply PermutationInCons in H as H';
      apply in_app_or in H';
      destruct H';
      match goal with
      | [HIn : In (atom F ) _ |- _ ] => apply InPermutation in HIn;
                                        let L' := fresh "L" in
                                        destruct HIn as [L' HIn];
                                        rewrite HIn in *;
                                        clear HIn
                                              
      end
    end;subst;CutTac.

  (** Extracting the needed facts given that all the OL constants are well-defined *)
  Ltac wellConstant HSeq :=
    let HS := type of HSeq in
    match HS with
    | (seqN ?Rules ?n ?Gamma ?M (>> ?Side ?C)) =>
      let Side' :=
          match Side with makeRRuleConstant => Right | makeLRuleConstant => Left end in
      
      match goal with
        [  LTWell:wellTheory |- _ ] =>
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize ((proj1 (proj2 LTWell)) Rules Gamma M C Side' );intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ];
        match goal with
          [isOL:  isOLFormula (t_cons ?C)  |- _] =>
          destruct bpEnum;[ apply LTWell' in HSeq; contradiction (* fail case *)
                          | generalize (LTWell' _ HSeq isOL);intro;CleanContext (* axiom *)
                          | generalize (LTWell' _ HSeq isOL);intro;CleanContext] (* one premise *)
        end
          
      end
    end.

  (** Extracting well-formed conditions for binary predicates *)
  Ltac wellFormedBin HSeq :=
    let HS := type of HSeq in
    match HS with
    | (seqN ?Rules ?n ?Gamma ?M (>> ?Side ?C ?F ?G)) =>
      let Side' :=
          match Side with makeRRuleBin => Right | makeLRuleBin => Left end in
      match goal with
        [  LTWell:wellTheory |- _ ] =>
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize ((proj1 (proj2 (proj2 (proj2 LTWell)))) Rules Gamma M C Side' );intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ]
      end
    end.

  (** Solving the case of [GenericBiPoleFail] bipoles *)
  Ltac bipoleFail :=
    match goal with
      [HBP : GenericBiPoleFail _ ?G ?M _ _ _, HSeq: seqN _ _ ?G ?M _ |- _] =>
      solve [apply HBP in HSeq;contradiction]
    end.

  (**  Solving the case for [GenericBiPole1P] *)
  Ltac bipole1P :=
    match goal with
      [ HBP: GenericBiPole1P _ ?G ?M ?T ?Rl _ _, HSeq: seqN _ _ ?G ?M (>> ?Rl), HIs: isOLFormula ?T |- _]
      =>
      let HSeq' := fresh "HSeq" in
      let HSeq'' := fresh "HSeq'" in
      apply HBP in HSeq as HSeq';
      apply HSeq' in HIs as HSeq'';
      clear HSeq' HBP
    end.

  (** Solving the case for [GenericBiPoleAxiom] *)
  Ltac bipoleAxiom :=
    match goal with
      [ HBP: GenericBiPoleAxiom _ ?G ?M ?T _ _ _, HSeq: seqN _ _ ?G ?M _, HIs: isOLFormula ?T |- _]
      =>
      let HSeq' := fresh "HSeq" in
      let HSeq'' := fresh "HSeq'" in
      apply HBP in HSeq as HSeq';
      apply HSeq' in HIs as HSeq'';
      clear HSeq' HBP
    end.
  
  (* Extracts the form of the binary (works for one and two premises *)
  Ltac  bipoleBinary :=
    match goal with
      [LTWell' : BiPoleBinary _ _ _ ?C _ _, HSeq: seqN _ ?n _ _ (>> _ ?C ?F ?G), isOL:  isOLFormula (t_bin ?C ?F ?G)  |- _] =>
      generalize (LTWell'  F G _ HSeq isOL);intro;CleanContext
    end.

  (* HSeq is the sequent where the case analysis will be performed *)
  Ltac wellFormedU HSeq  :=
    let HS := type of HSeq in
    match HS with
    | (seqN ?Rules ?n ?Gamma ?M (>> ?Side ?C ?F)) =>
      let Side' :=
          match Side with makeRRuleUnary => Right | makeLRuleUnary => Left end in
      match goal with
        [  LTWell:wellTheory |- _ ] => 
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize ((proj1 (proj2 (proj2 LTWell))) Rules Gamma M C Side' );intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ] 
      end
    end.
  

  (** Extracts the form of the binary connectives (works for one and two premises *)
  Ltac  bipoleUnary :=
    match goal with
      [LTWell' : BiPoleUnary _ _ _ ?C _ _, HSeq: seqN _ ?n _ _ (>> _ ?C ?F), isOL:  isOLFormula (t_ucon ?C ?F)  |- _] =>
      generalize (LTWell'  F _ HSeq isOL);intro;CleanContext
    end.

  Ltac wellFormedQ HSeq :=
    let HS := type of HSeq in
    match HS with
    | (seqN ?Rules ?n ?Gamma ?M (>> ?Side ?C ?F)) =>
      let Side' :=
          match Side with makeRRuleQ => Right | makeLRuleQ => Left end in
      
      match goal with
        [  LTWell:wellTheory |- _ ] =>
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize ((proj2 (proj2 (proj2 (proj2 LTWell)))) Rules Gamma M C Side' );intro LTWell'
      end
    end.
  
  (** Extracts the form for quantifiers *)
  Ltac  bipoleQ :=
    let HUniform := fresh "HUniform" in
    let LTWell'' := fresh "LTWell'" in
    match goal with
      [LTWell' : BiPoleQuantifier _ _ _ ?C _ _, HSeq: seqN _ ?n _ _ (>> _ ?C ?FX),
                                                      isOL:  isOLFormula (t_quant ?C ?FX)  |- _] =>
      generalize (LTWell'  FX) ; intro LTWell'' ; destruct LTWell'' as [HUniform LTWell''] ;
      generalize (LTWell''  _ HSeq isOL);intro;CleanContext; clear LTWell''
                                                                   
    end.
  
  (* This tactic solves the cases where the cut atom is not
principal in the last rule applied. [HUp] must be the a premise of the
form [seq Gamma (A: Delta) (> [])] where [A] is the cut-atom (not used
in the derivation). [Hs2] is the other branch of the cut-derivation of
the form [ > up + ] or [ > down + ] . [IH] is the inductive hypothesis
of the theorem. [HDer] is the hypothesis generated by the bipole
decomposition (telling how to rebuild the proof from the presmies. *)
  Ltac SolveCaseOnePremiseCut HUp Hs2 IH HDer n :=
    simpl in HUp;
    let s1 := type of HUp in
    let s2 := type of Hs2 in
    match s1 with
    | (seqN _ ?x1 (?Gamma ++ ?x0) ((atom (?pred1 ?A) ) :: ?M0 ++ ?x) (> [])) => (**** BEFORE UP UP ?A *)
      match s2 with
      | ( seqN _ ?x2 _ ?M (>> (atom (?pred2 ?A) )) ) => (** BEFORE DOWN *)
        apply FocusAtomInv in  HUp; (* move (up A ) to the focused phase *)
        apply  weakeningGenN_rev with (CC':= x0) in Hs2;(*rewrite Permutation_app_comm in Hs2 ;*)
        let Hcut := fresh "Hcut" in
        match pred1 with
        | up =>
          (* Using the IH to obtain the cut-free proof *)
          assert (Hcut : seq (OLTheoryCut (pred n)) (Gamma ++ x0) (M ++ (M0 ++ x)) (> []))
            by (eapply IH with (m:=  plus x2 (S (S x1))) (FCut := A) (h1 := (S (S x1))) (h2 := x2);auto;try lia;CutTac); 
          (* rebuilding the derivation from the cut-free proof *)
          rewrite app_assoc in Hcut
        | down =>
          assert (Hcut : seq (OLTheoryCut (pred n)) (Gamma ++ x0) ((M0 ++ x) ++ M) (> []))
            by (
                (* rebuilding the derivation from the cut-free proof *)
                eapply IH with (m:=  plus x2 (S (S x1))) (FCut := A) (h2 := (S (S x1))) (h1 := x2);auto;try lia;CutTac);                
          rewrite app_assoc_reverse in Hcut;
          rewrite (Permutation_app_comm x M) in Hcut;
          rewrite app_assoc in Hcut
        end;
        apply HDer in Hcut;CutTac ;FindSolution Hcut
      end
    end.
  
  (** Similar to the previous one but considering rules with 2 premises *)
  Ltac SolveCaseTwoPremisesCut HUp Hs2 IH HDer HPrem n :=
    simpl in HUp;
    let s1 := type of HUp in
    let s2 := type of Hs2 in
    match s1 with
    | (seqN _ ?x1 (?Gamma ++ ?x0) ((atom (?pred1 ?A) ) :: ?M0 ++ ?x) (> [])) =>
      match s2 with
      | ( seqN _ ?x2 _ ?M (>> (atom (?pred2 ?A) )) ) =>
        apply FocusAtomInv in  HUp; (* move (up A ) to the focused phase *)
        apply  weakeningGenN_rev with (CC':= x0) in Hs2;(*rewrite Permutation_app_comm in Hs2 ;*)
        let Hcut := fresh "Hcut" in
        match pred1 with
        | up =>
          (* Using the IH to obtain the cut-free proof *)
          assert (Hcut : seq (OLTheoryCut (pred n)) (Gamma ++ x0) (M ++ (M0 ++ x)) (> [])) 
            by (
                eapply IH with (m:=  plus x2 (S (S x1))) (FCut := A) (h1 := (S (S x1))) (h2 := x2);auto;try lia;IsPositiveLSolve);
          (* rebuilding the derivation from the cut-free proof *)
          rewrite app_assoc in Hcut;
          (* working on the second derivation *)
          apply seqNtoSeq in HPrem;
          apply WeakTheory with (theory' := (OLTheoryCut (pred n)) ) in HPrem ;auto using TheoryEmb1;CutTac
        | down =>
          (* Using the IH to obtain the cut-free proof *)
          assert (Hcut : seq (OLTheoryCut (pred n)) (Gamma ++ x0) ( (M0 ++ x) ++ M) (> [])) 
            by (
                eapply IH with (m:=  plus x2 (S (S x1))) (FCut := A) (h2 := (S (S x1))) (h1 := x2);auto;try lia; try IsPositiveLSolve) ;
          (* rebuilding the derivation from the cut-free proof *)
          rewrite (Permutation_app_comm M0 x) in Hcut;
          rewrite app_assoc_reverse in Hcut;
          rewrite ( Permutation_app_comm x) in Hcut;
          (* working on the second derivation *)
          apply seqNtoSeq in HPrem ;
          apply WeakTheory with (theory' := (OLTheoryCut (pred n)) ) in HPrem ;auto using TheoryEmb1;CutTac
        end;
        let s3 := type of HPrem in
        match s3 with
        | (seq _ _ (?deltaX ++ _) _) =>
          try (eapply HDer with (Delta2 := deltaX) in Hcut;CutTac);
          try (eapply HDer with (Delta1 := deltaX) in Hcut;CutTac)
        end;  FindSolution Hcut
      end
    end.

  Ltac DualPred p FCut :=
    eval compute in
      match (p FCut) with
      | (down FCut) => up FCut
      | (up FCut) => down FCut
      end.

  Ltac SolveOnePremise :=
    match goal with
    |[IH: forall (m:nat),_ ,
        HForall : (forall (D G : list oo) (theory' : oo -> Prop), _ -> (seq _ (_ ++ ?xg) (_ ++ ?dx) _) -> _),
        HS : seqN _ _ (_ ++ ?xg) ( ( (atom (?p ?FCut)) :: _) ++ ?dx) (> []) |- seq (OLTheoryCut (pred ?n)) _ _ _ ] =>
     match p with
     |down => match goal with | [HSeq: seqN _ _ _ _ (>> atom (up FCut))  |- _] => SolveCaseOnePremiseCut HS HSeq IH HForall n end
     |up => match goal with | [HSeq: seqN _ _ _ _ (>> atom (down FCut))  |- _] => SolveCaseOnePremiseCut HS HSeq IH HForall n end
              
     end
    |[IH: forall (m:nat),_ ,
        HForall : (forall (D G : list oo) (theory' : oo -> Prop), _ -> _ ->(seq _ (_ ++ ?xg) (_ ++ ?dx) _) -> _),
        HS : seqN _ _ (_ ++ ?xg) ( ( (atom (?p ?FCut)) :: _) ++ ?dx) (> []) |- seq (OLTheoryCut (pred ?n)) _ _ _ ] =>
     match p with
     |down => match goal with | [HSeq: seqN _ _ _ _ (>> atom (up FCut))  |- _] => SolveCaseOnePremiseCut HS HSeq IH HForall n end
     |up => match goal with | [HSeq: seqN _ _ _ _ (>> atom (down FCut))  |- _] => SolveCaseOnePremiseCut HS HSeq IH HForall n end
              
     end
       
    end.

  Ltac SolveTwoPremises1 :=
    match goal with
      [IH: forall (m:nat),_ ,
         HForall : (forall (D1 D2 G : list oo) (theory' : oo -> Prop), _ -> (seq _ (_ ++ ?dx) _ _) -> (seq _ (_ ++ ?dy) _ _)  -> _), HS : seqN _ ?x (_ ++ ?dx) ( ( (atom (?p ?FCut)) :: _) ++ _) (> []), HS' : seqN _ ?x (_ ++ ?dy) _ (> [])   |- seq (OLTheoryCut (pred ?n)) _ _ _ ] =>
      let p' := DualPred p FCut in
      match goal with
        [HSeq: seqN _ _ _ _ (>> atom p')  |- _] => SolveCaseTwoPremisesCut HS HSeq IH HForall HS' n 
      end
    end.
  Ltac SolveTwoPremises2 :=
    match goal with
      [IH: forall (m:nat),_ ,
         HForall : (forall (D1 D2 G : list oo) (theory' : oo -> Prop), _ -> (seq _ (_ ++ ?dy) _ _) -> (seq _ (_ ++ ?dx) _ _)  -> _), HS : seqN _ ?x (_ ++ ?dx) ( ( (atom (?p ?FCut)) :: _) ++ _) (> []), HS' : seqN _ ?x (_ ++ ?dy) _ (> [])   |- seq (OLTheoryCut (pred ?n)) _ _ _ ] =>
      let p' := DualPred p FCut in
      match goal with
        [HSeq: seqN _ _ _ _ (>> atom p')  |- _] => SolveCaseTwoPremisesCut HS HSeq IH HForall HS' n 
      end
    end.
  Ltac SolveTwoPremises3 :=
    match goal with
      [IH: forall (m:nat),_ ,
         HForall : (forall (D1 D2 G : list oo) (theory' : oo -> Prop), _ -> _ ->  (seq _ (_ ++ ?dx) _ _) -> (seq _ (_ ++ ?dy) _ _)  -> _), HS : seqN _ ?x (_ ++ ?dx) ( ( (atom (?p ?FCut)) :: _) ++ _) (> []), HS' : seqN _ ?x (_ ++ ?dy) _ (> [])   |- seq (OLTheoryCut (pred ?n)) _ _ _ ] =>
      let p' := DualPred p FCut in
      match goal with
        [HSeq: seqN _ _ _ _ (>> atom p')  |- _] => SolveCaseTwoPremisesCut HS HSeq IH HForall HS' n 
      end
    end.
  Ltac SolveTwoPremises4 :=
    match goal with
      [IH: forall (m:nat),_ ,
         HForall : (forall (D1 D2 G : list oo) (theory' : oo -> Prop), _ -> _ -> (seq _ (_ ++ ?dy) _ _) -> (seq _ (_ ++ ?dx) _ _)  -> _), HS : seqN _ ?x (_ ++ ?dx) ( ( (atom (?p ?FCut)) :: _) ++ _) (> []), HS' : seqN _ ?x (_ ++ ?dy) _ (> [])   |- seq (OLTheoryCut (pred ?n)) _ _ _ ] =>
      let p' := DualPred p FCut in
      match goal with
        [HSeq: seqN _ _ _ _ (>> atom p')  |- _] => SolveCaseTwoPremisesCut HS HSeq IH HForall HS' n 
      end
    end.

  Ltac SolveTwoPremises :=
    first [SolveTwoPremises1 | SolveTwoPremises2 | SolveTwoPremises3 |SolveTwoPremises4].

  (** Case for two premisses when the context is shared (additive) *)
  Ltac SolveTwoPremisesAddLinear :=
    match goal with
      [IH : forall (_ :nat), _, Hsq1 : seqN OLTheory ?x4' (?Gamma' ++ ?x2') ( ( (atom (?p ?FCut') ) :: ?L) ++ ?x0) (> []),
         Hsq2:     seqN OLTheory ?x4' (?Gamma' ++ ?x3') (( (atom (?p ?FCut') ) :: ?L') ++ ?x1) (> []),
         HFall : forall (_ _ : _) _, _ -> (seq _ (_ ++ ?x2') (_ ++ ?x0') (> []) ) -> (seq _ (_ ++ ?x3') (_ ++ ?x1) (> [])) -> _ , HPer: Permutation ?M _|- seq (OLTheoryCut (pred ?n)) ?Gamma' (?M ++ ?N) (> [])] => 
      let p' := (match p with up => constr:(down FCut') | down => constr:(up FCut')end ) in 
      let Hsq1' := fresh "Hsq1" in
      let Hsq2' := fresh "Hsq2" in
      let Hcut1 := fresh "Cut" in
      let Hcut2 := fresh "Cut" in
      match goal with
        [ HOther :seqN _ ?hh1 _ ?N' (>> atom p') |- _] =>
        simpl in Hsq1; simpl in Hsq2;
        apply FocusAtomInv in Hsq1; apply FocusAtomInv in Hsq2;
        apply  weakeningGenN_rev with (CC':= x2') in HOther as Hsq1';
        apply  weakeningGenN_rev with (CC':= x3') in HOther as Hsq2';
        assert(Hcut1 :seq (OLTheoryCut (pred n)) (Gamma' ++ x2') ((L' ++ x0') ++ N') (> [])) by
            ( eapply IH with  (FCut := FCut') (m:= plus hh1 (S (S x4'))) (h1:= hh1) (h2:= (S (S x4')));auto; try lia; try IsPositiveLSolve) ;
        assert(Hcut2 :seq (OLTheoryCut (pred n)) (Gamma' ++ x3') ((L' ++ x1) ++ N') (> [])) by
            (eapply IH with  (FCut := FCut') (m:= plus hh1 (S (S x4'))) (h1:= hh1) (h2:= (S (S x4')));auto; try lia; try IsPositiveLSolve);
        rewrite HPer;
        rewrite Permutation_assoc_comm in Hcut1;
        rewrite Permutation_assoc_comm in Hcut2;
        eapply HFall;CutTac 
      end
    end.

  (** Symmetric case *)
  Ltac SolveTwoPremisesAddLinear' :=
    match goal with
      [H : forall (_ :nat), _, Hsq1 : seqN OLTheory ?x4 (?Gamma ++ ?x2) ( ( (atom (?p ?FCut') ) :: ?L) ++ ?x0) (> []),
         Hsq2:     seqN OLTheory ?x4 (?Gamma ++ ?x3) (( (atom (?p ?FCut') ) :: ?L) ++ ?x1) (> []),
         HFall : forall (_ _ : _) _, _ -> (seq _ (_ ++ ?x2) (_ ++ ?x0) (> []) ) -> (seq _ (_ ++ ?x3) (_ ++ ?x1) (> [])) -> _ , HPer: Permutation ?N _|- seq (OLTheoryCut (pred ?n)) ?Gamma (?M ++ ?N) (> [])] =>
      let p' := (match p with up => constr:(down FCut') | down => constr:(up FCut')end ) in 
      let Hsq1' := fresh "Hsq1" in
      let Hsq2' := fresh "Hsq2" in
      let Hcut1 := fresh "Cut" in
      let Hcut2 := fresh "Cut" in
      match goal with
        [ HOther :seqN _ ?hh1 _ ?N (>> atom p') |- _] => 
        simpl in Hsq1; simpl in Hsq2;
        apply FocusAtomInv in Hsq1; apply FocusAtomInv in Hsq2;
        apply  weakeningGenN_rev with (CC':= x2) in HOther as Hsq1';
        apply  weakeningGenN_rev with (CC':= x3) in HOther as Hsq2';
        assert(Hcut1 :seq (OLTheoryCut (pred n)) (Gamma ++ x2) (M ++ (L ++ x0) ) (> [])) by
            (eapply H with  (FCut := FCut') (m:= plus  (S (S x4)) hh1) (h2:= hh1) (h1:= (S (S x4)));auto; try lia; try IsPositiveLSolve);
        assert(Hcut2 :seq (OLTheoryCut (pred n)) (Gamma ++ x3) (M ++ (L ++ x1) ) (> [])) by
            (eapply H with  (FCut := FCut') (m:= plus (S (S x4)) hh1 ) (h2:= hh1) (h1:= (S (S x4)));auto; try lia; try IsPositiveLSolve);
        rewrite Permutation_midle_app in Hcut1;
        rewrite Permutation_midle_app in Hcut2;
        rewrite Per_app_assoc in Hcut1;
        rewrite Per_app_assoc in Hcut2;
        rewrite Permutation_app_comm;rewrite  HPer;simpl;
        eapply HFall;CutTac
                       
      end
    end.

  (** Two premises case when the atom is taken from the classical case *)
  Ltac SolveTwoPremisesAdClassic :=
    match goal with
      [H : forall (_ :nat), _, HPer: Permutation ((atom (?p ?FCut')) :: ?M) ?x, Hsq1 : seqN OLTheory ?x4 (?Gamma ++ ?x2) ( ?x ++ ?x0) (> []),
         Hsq2: seqN OLTheory ?x4 (?Gamma ++ ?x3) (?x ++ ?x1) (> []),
         HFall : forall (_ _ : _) _, _ -> _  -> (seq _ (_ ++ ?x2) (_ ++ ?x0) (> []) ) -> (seq _ (_ ++ ?x3) (_ ++ ?x1) (> [])) -> _  |- seq (OLTheoryCut (pred ?n)) ?Gamma (?M ++ ?N) (> [])] =>
      
      let p' := (match p with up => constr:(down FCut') | down => constr:(up FCut')end ) in 
      let Hsq1' := fresh "Hsq1" in
      let Hsq2' := fresh "Hsq2" in
      let Hcut1 := fresh "Cut" in
      let Hcut2 := fresh "Cut" in
      match goal with
        [ HOther :seqN _ ?hh1 _ ?N (>> atom p') |- _] =>
        rewrite <- HPer in Hsq1;simpl in Hsq1;
        rewrite <-  HPer in Hsq2;simpl in Hsq2;
        apply FocusAtomInv in Hsq1;
        apply FocusAtomInv in Hsq2;
        apply  weakeningGenN_rev with (CC':= x2) in HOther as Hsq1';
        apply  weakeningGenN_rev with (CC':= x3) in HOther as Hsq2';
        assert(Hcut1: seq (OLTheoryCut (pred n)) (Gamma ++ x2) ((M ++ x0) ++ (N)) (> []))
          by (eapply H with (m:= plus hh1 (S (S x4))) (FCut := FCut') (h1:= hh1) (h2:= (S (S x4)));auto;try lia; try IsPositiveLSolve );
        assert(Hcut2 :seq (OLTheoryCut (pred n)) (Gamma ++ x3) ((M ++ x1) ++ (N)) (> [])) by
            (eapply H with  (FCut := FCut') (m:= plus hh1 (S (S x4))) (h1:= hh1) (h2:= (S (S x4)));auto; try lia; try IsPositiveLSolve);
        rewrite Permutation_assoc_comm in Hcut1;
        rewrite Permutation_assoc_comm in Hcut2;
        eapply HFall;CutTac
      end
        
    end.

  (** Symmetric case *)
  Ltac SolveTwoPremisesAdClassic' :=
    match goal with
      [H : forall (_ :nat), _, HPer: Permutation ((atom (?p ?FCut')) :: ?N) ?x, Hsq1 : seqN OLTheory ?x4 (?Gamma ++ ?x2) ( ?x ++ ?x0) (> []),
         Hsq2: seqN OLTheory ?x4 (?Gamma ++ ?x3) (?x ++ ?x1) (> []),
         HFall : forall (_ _ : _) _, _ -> _  -> (seq _ (_ ++ ?x2) (_ ++ ?x0) (> []) ) -> (seq _ (_ ++ ?x3) (_ ++ ?x1) (> [])) -> _  |- seq (OLTheoryCut (pred ?n)) ?Gamma (?M ++ ?N) (> [])] =>
      
      let p' := (match p with up => constr:(down FCut') | down => constr:(up FCut')end ) in 
      let Hsq1' := fresh "Hsq1" in
      let Hsq2' := fresh "Hsq2" in
      let Hcut1 := fresh "Cut" in
      let Hcut2 := fresh "Cut" in
      match goal with
        [ HOther :seqN _ ?hh1 _ _ (>> atom p') |- _] =>
        rewrite <- HPer in Hsq1;simpl in Hsq1;
        rewrite <-  HPer in Hsq2;simpl in Hsq2;
        apply FocusAtomInv in Hsq1;
        apply FocusAtomInv in Hsq2;
        apply  weakeningGenN_rev with (CC':= x2) in HOther as Hsq1';
        apply  weakeningGenN_rev with (CC':= x3) in HOther as Hsq2';
        assert(Hcut1: seq (OLTheoryCut (pred n)) (Gamma ++ x2) (M ++ (N ++ x0) ) (> []))
          by (eapply H with (m:= plus (S (S x4)) hh1) (FCut := FCut') (h2:= hh1) (h1:= (S (S x4)));auto;try lia; try IsPositiveLSolve );
        assert(Hcut2 :seq (OLTheoryCut (pred n)) (Gamma ++ x3) (M ++ (N ++ x1) ) (> [])) by
            (eapply H with  (FCut := FCut') (m:= plus (S (S x4)) hh1 ) (h2:= hh1) (h1:= (S (S x4)));auto; try lia; try IsPositiveLSolve);
        rewrite Per_app_assoc in Hcut1;
        rewrite Per_app_assoc in Hcut2;
        eapply HFall;CutTac
      end
        
    end.

  (** Solve the case when focusing on a unary Right (resp. Left) unary
  connective rule and the current atom in the context is [down]
  (resp. [downs] *)
  
  Ltac SolveUnary :=
    match goal with
      [ HSeq : seqN _ _ _ (atom (up _) :: _) (>> makeLRuleUnary _ _) |- _ ] => wellFormedU HSeq
    | [ HSeq : seqN _ _ _ (atom (down _) :: _) (>> makeRRuleUnary _ _) |- _ ] => wellFormedU HSeq
    end;
    match goal with
      [ bpEnum : BipoleEnum |- _ ] => destruct bpEnum;bipoleUnary
    end;
    [ (* one premise case *)
      match goal with [H : _ \/ _ |- _ ] =>
                      destruct H;CleanContext;[UpDownMismatch;SolveOnePremise | SolveOnePremise]
      end
    |
    (* two premises multiplicative *)
    match goal with [H : _ \/ _ |- _ ] =>
                    destruct H;CleanContext;
                    [ UpDownMismatch;match goal with [HDIFF: Permutation (_ ++ _) (atom _ :: _) |- _] => CaseIn HDIFF;SolveTwoPremises end | match goal with [HDIFF : Permutation (atom _ :: _) ( _ ++ _) |- _ ] => CaseIn HDIFF;SolveTwoPremises end]
    end
    | (* two premises additive *)
    match goal with [H : _ \/ _ |- _ ] =>
                    first[
                        destruct H;CleanContext;
                        [UpDownMismatch;SolveTwoPremisesAddLinear | SolveTwoPremisesAdClassic]
                      | destruct H;CleanContext;
                        [UpDownMismatch;SolveTwoPremisesAddLinear' | SolveTwoPremisesAdClassic']
                      ]
    end
      
    ].
  
  (** Similar to [SolveUnary] for binary connectives *)
  Ltac SolveBinary :=
    match goal with
      [ HSeq : seqN _ _ _ (atom (up _) :: _) (>> makeLRuleBin _ _ _) |- _ ] => wellFormedBin HSeq
    | [ HSeq : seqN _ _ _ (atom (down _) :: _) (>> makeRRuleBin _ _ _) |- _ ] => wellFormedBin HSeq
    end;
    match goal with
      [ bpEnum : BipoleEnum |- _ ] => destruct bpEnum;bipoleBinary
    end;
    [ (* one premise case *)
      match goal with [H : _ \/ _ |- _ ] =>
                      destruct H;CleanContext;[UpDownMismatch;SolveOnePremise | SolveOnePremise]
      end
    | (* two premises case *)
    match goal with [H : _ \/ _ |- _ ] =>
                    destruct H;CleanContext;
                    [ UpDownMismatch;match goal with [HDIFF: Permutation (_ ++ _) (atom _ :: _) |- _] => CaseIn HDIFF;SolveTwoPremises end | match goal with [HDIFF : Permutation (atom _ :: _) ( _ ++ _) |- _ ] => CaseIn HDIFF;SolveTwoPremises end]
    end
    | (* two premises addtive case *)
    match goal with [H : _ \/ _ |- _ ] =>
                    first[
                        destruct H;CleanContext; [UpDownMismatch;SolveTwoPremisesAddLinear | SolveTwoPremisesAdClassic]
                      | destruct H;CleanContext; [UpDownMismatch;SolveTwoPremisesAddLinear' | SolveTwoPremisesAdClassic'] ]
    end
    ].


  (** Similar to [SolveUnary] for quantifiers *)
  Ltac SolveQuantifier :=
    match goal with
      [ HSeq : seqN _ _ _ (atom (up _) :: _) (>> makeLRuleQ _ _ ) |- _ ] => wellFormedQ HSeq
    | [ HSeq : seqN _ _ _ (atom (down _) :: _) (>> makeRRuleQ _ _) |- _ ] => wellFormedQ HSeq
    end;

    bipoleQ;
    (* one premise case onlye *)
    match goal with [H : _ \/ _ |- _ ] =>
                    destruct H;CleanContext;[UpDownMismatch;SolveOnePremise | SolveOnePremise]
    end.


  (** Similar to [SolveUnary] for Constant symbols on the right *)
  Ltac SolveRightConstant :=
    match goal with
      [ HIs : isOLFormula (t_cons ?C), HSeq :  seqN ?theory _ ?Gamma (atom (down ?F) :: ?M) (>> makeRRuleConstant ?C) |- _ ] =>
      wellConstant HSeq;
      [ (* case axiom *)
        match goal with
          [ H : _ \/ _  |- _] =>
          destruct H ; CleanContext;
          [ (* linear case *)
            match goal with
              [HPer: Permutation (_ :: _) (_ :: _), HFall : forall (D : list oo) _ _, _ |- _ ] =>
              UpDownMismatch; rewrite HPer;simpl; apply HFall;CutTac end
          |  (* classical case *)
          match goal with
            [ HFall : forall (D : _ oo) _ _, _ |- _ ] =>
            apply HFall;CutTac
          end ]
        end
      | (* case one premise *)
      match goal with
        [ H : _ \/ _  |- _] =>
        destruct H ; CleanContext;[ UpDownMismatch; SolveOnePremise | SolveOnePremise]
      end ]
    end.

  (** Similar to [SolveUnary] for Constant symbols on the left *)
  Ltac SolveLeftConstant :=
    match goal with
      [ HIs : isOLFormula (t_cons ?C), HSeq :  seqN ?theory _ ?Gamma (atom (up ?F) :: ?M) (>> makeLRuleConstant ?C) |- _ ] =>
      wellConstant HSeq;
      [ (* axiom case *)
        match goal with
        | [ H : _ \/ _ |- _ ] =>
          destruct H;CleanContext;
          [ (* linear case *)
            match goal with
              [HPer : Permutation (_ :: _) (_ :: _), HForall: forall (D: list oo) _ _,_ |- _] =>
              UpDownMismatch;  rewrite HPer;simpl; rewrite Permutation_app_comm; apply HForall ; CutTac
            end
          | (* classical case *)
          match goal with
            [HForall: forall (D: multiset oo) _ _,_ |- _] =>
            apply HForall;CutTac
          end
          ]
        end
      | (* one premise case *)
      match goal with
      | [ H : _ \/ _ |- _ ] =>
        destruct H;CleanContext;[UpDownMismatch;SolveOnePremise | SolveOnePremise]
      end             
      ]
    end.
  
  (** This is the case when a constant is principal in both premises *)
  Theorem ConstantPrincipalCase :
    forall Gamma M N C,
      IsPositiveAtomFormulaL Gamma ->
      IsPositiveAtomFormulaL M ->
      IsPositiveAtomFormulaL N ->
      (seq OLTheory Gamma M (>> rc_leftBody (rulesCte C))) ->
      (seq OLTheory Gamma N (>> rc_rightBody (rulesCte C))) ->
      seq OLTheory Gamma (N ++ M) (> []).
    intros.
    apply seqtoSeqN in H2.     apply seqtoSeqN in H3.
    destruct H2.     destruct H3.
    destruct OLIsFormula as [HC [HU [HB HQ]]]. (*;autounfold in *. *)
    destruct OLIsFormulaD as [HCD [HUD [HBD HQD]]]. (*;autounfold in *. *)
    generalize( (proj1 (proj1 LTWell)) C);intro CutC.
    unfold CutCoherenceCte in CutC.
    apply EmptySubSet with (theory:= OLTheory ) in CutC.
    apply weakeningGen with (CC':= Gamma) in CutC .
    apply seqtoSeqN in CutC.   destruct CutC as [h CutC].
    rewrite app_nil_r in CutC.
    assert(HCut1: seq OLTheory Gamma ([] ++ N)  ( > [ (rc_leftBody (rulesCte C)) ^])).
    eapply @GeneralCut with  ( dualC:= (rc_rightBody (rulesCte C)) ) (C:=  rc_rightBody (rulesCte C) ^); eauto using OLTheoryWellFormed,  OLTheoryWellFormedD, IsPositiveAtomNotAsync, IsPositiveIsFormula.
    rewrite <- ng_involutive;auto.
    apply HCD. apply HC. constructor.
    apply HCD. constructor.
    simpl in HCut1.
    apply seqtoSeqN in HCut1.  destruct HCut1 as [h2 HCut1].
    eapply @GeneralCut with (dualC := (rc_leftBody (rulesCte C))) (C:= (rc_leftBody (rulesCte C)) ^); eauto using OLTheoryWellFormed,  OLTheoryWellFormedD, IsPositiveAtomNotAsync,IsPositiveIsFormula.
    rewrite <- ng_involutive;auto.
    apply HCD. apply HC. 
  Qed.

  (** This is the case when a unary connective is principal in both premises *)
  Theorem UConnectivePrincipalCase :
    forall Gamma M N C F n n',
      IsPositiveAtomFormulaL Gamma ->
      IsPositiveAtomFormulaL M ->
      IsPositiveAtomFormulaL N ->
      (seq OLTheory Gamma M (>> ru_leftBody (rulesUnary C) F)) ->
      (seq OLTheory Gamma N (>> ru_rightBody (rulesUnary C) F)) ->
      (lengthUexp (t_ucon C F) n') ->
      isOLFormula (t_ucon C F) ->
      n' <= n ->
      seq (OLTheoryCut (pred n)) Gamma (N ++ M) (> []).
  Proof with solveF.
    intros.
    inversion H4;subst.
    inversion H5;subst. inversion H7.
    destruct n ;[ lia | simpl].
    apply seqtoSeqN in H2.     apply seqtoSeqN in H3.
    destruct H2 as [h1 H2].
    destruct H3 as [h2 H3].

    destruct OLIsFormula as [HC [HU [HB HQ]]]. 
    destruct OLIsFormulaD as [HCD [HUD [HBD HQD]]]. 
    
    generalize( (proj1 (proj2 ((proj1 LTWell)))) C);intro CutC.
    unfold CutCoherenceUnary in CutC.
    generalize (CutC F _ H10 H8) ;intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply seqtoSeqN in Cut1. destruct Cut1 as [hh  Cut1].
    apply WeakTheoryN with (theory' := OLTheoryCut n) in Cut1;auto using TheoryEmb2.
    apply weakeningGenN with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheoryN with (theory' := OLTheoryCut n) in H2;auto using TheoryEmb1.
    apply WeakTheoryN with (theory' := OLTheoryCut n) in H3;auto using TheoryEmb1.
    assert(Cut1': seq (OLTheoryCut n) Gamma ([] ++ N) ( >[(ru_leftBody (rulesUnary C) F) ^] )).
    eapply @GeneralCut with (dualC := (ru_rightBody (rulesUnary C) F)) (C := (ru_rightBody (rulesUnary C) F)  ^) ;
      eauto using OLTheoryWellFormed,  OLTheoryWellFormedD, IsPositiveAtomNotAsync, IsPositiveIsFormula, OLTheoryCutWellFormed, OLTheoryCutWellFormedD;simpl;auto...
    rewrite <- ng_involutive;auto.
    apply HUD.
    apply HU.
    constructor...
    apply HUD.
    apply seqtoSeqN in Cut1'.  destruct Cut1' as [h3 Cut1'].
    eapply @GeneralCut with (dualC := (ru_leftBody (rulesUnary C) F)) (C:= (ru_leftBody (rulesUnary C) F) ^); eauto using OLTheoryWellFormed,  OLTheoryWellFormedD, IsPositiveAtomNotAsync,IsPositiveIsFormula, OLTheoryCutWellFormed, OLTheoryCutWellFormedD.
    rewrite <- ng_involutive;auto.
    apply HUD. apply HU.
  Qed.
  
  (** This is the case when a binary connective is principal in both premises *)
  Theorem BinConnectivePrincipalCase :
    forall Gamma M N C F G n n',
      IsPositiveAtomFormulaL Gamma ->
      IsPositiveAtomFormulaL M ->
      IsPositiveAtomFormulaL N ->
      (seq OLTheory Gamma M (>> rb_leftBody (rulesBin C) F G)) ->
      (seq OLTheory Gamma N (>> rb_rightBody (rulesBin C) F G)) ->
      lengthUexp (t_bin C F G) n' ->
      isOLFormula (t_bin C F G) ->
      n' <= n ->
      seq (OLTheoryCut (pred n)) Gamma (N ++ M) (> []).
  Proof with solveF.
    intros.
    inversion H4;subst.
    inversion H5;subst. inversion H7.
    destruct n ;[ lia | simpl].
    apply seqtoSeqN in H2.     apply seqtoSeqN in H3.
    destruct H2 as [h1 H2].
    destruct H3 as [h2 H3].

    destruct OLIsFormula as [HC [HU [HB HQ]]]. 
    destruct OLIsFormulaD as [HCD [HUD [HBD HQD]]].
    generalize ((proj1 (proj2 (proj2 (proj1 LTWell)))) C);intro CutC.
    unfold CutCoherenceBin in CutC.
    
    generalize (CutC F _ _ _ H11 H12 H9 H13) ;intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1;[| lia].
    apply seqtoSeqN in Cut1. destruct Cut1 as [hh  Cut1].
    apply WeakTheoryN with (theory' := OLTheoryCut n) in Cut1;auto using TheoryEmb2.
    apply weakeningGenN with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheoryN with (theory' := OLTheoryCut n) in H2;auto using TheoryEmb1.
    apply WeakTheoryN with (theory' := OLTheoryCut n) in H3;auto using TheoryEmb1.
    
    assert(Cut1': seq (OLTheoryCut n) Gamma ([] ++ N) ( >[ (rb_leftBody (rulesBin C) F G) ^] )).
    eapply @GeneralCut with (dualC := (rb_rightBody (rulesBin C) F G)) (C := (rb_rightBody (rulesBin C) F G) ^) ;
      eauto using OLTheoryWellFormed,  OLTheoryWellFormedD, IsPositiveAtomNotAsync, IsPositiveIsFormula, OLTheoryCutWellFormed, OLTheoryCutWellFormedD;simpl;auto...
    rewrite <- ng_involutive;auto.
    apply HBD.
    apply HB.
    constructor...
    apply HBD.
    apply seqtoSeqN in Cut1'.  destruct Cut1' as [h3 Cut1'].
    eapply @GeneralCut with (dualC := (rb_leftBody (rulesBin C) F G)) (C:= (rb_leftBody (rulesBin C) F G) ^); eauto using OLTheoryWellFormed,  OLTheoryWellFormedD, IsPositiveAtomNotAsync,IsPositiveIsFormula, OLTheoryCutWellFormed, OLTheoryCutWellFormedD.
    rewrite <- ng_involutive;auto.
    apply HBD. apply HB.
  Qed.

  (** This is the case when a quantifier is principal in both premises *)
  Theorem QuantifierPrincipalCase :
    forall Gamma M N C FX FX0 n n',
      IsPositiveAtomFormulaL Gamma ->
      IsPositiveAtomFormulaL M ->
      IsPositiveAtomFormulaL N ->
      (seq OLTheory Gamma M (>> rq_leftBody (rulesQ C) FX0)) ->
      (seq OLTheory Gamma N (>> rq_rightBody (rulesQ C) FX)) ->
      isOLFormula (t_quant C FX) ->
      isOLFormula (t_quant C FX0) ->
      lengthUexp (t_quant C FX) n' ->
      uniform FX -> uniform FX0 ->
      lbind 0 FX0 = lbind 0 FX ->
      n' <= n ->
      seq (OLTheoryCut (pred n)) Gamma (N ++ M) (> []).
  Proof with solveF.
    intros.
    inversion H4. inversion H11.
    inversion H5. inversion H15.
    subst.
    assert (ext_eq FX FX0).
    eapply lbindEq;eauto.
    assert (ext_eq FX FX1). eapply lbindEq;eauto.
    assert (ext_eq FX FX2). eapply lbindEq;eauto.  rewrite <- H9. auto.
    inversion H6...
    destruct n ;[ lia | simpl].
    assert (ext_eq FX M0). eapply lbindEq;eauto.
    generalize ( ( proj2 ( proj2 ( proj2 (proj1 LTWell)))) C) ;intro CutC.
    assert (Hsize: lengthUexp (FX (Var 0)) n0).
    { rewrite H20...  apply proper_VAR.  }
    assert(HIs: (forall t : expr Econ, proper t -> isOLFormula (FX t))).
    {intros t pt. rewrite H15... }
    unfold CutCoherenceQ in *.
    generalize (CutC FX FX0 n0 H7 H8 H11 Hsize HIs); intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1; [ | lia].
    apply WeakTheory with (theory' := OLTheoryCut n) in Cut1;auto using TheoryEmb1.
    apply weakeningGen with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheory with (theory' := OLTheoryCut n) in H2;auto using TheoryEmb1.
    apply WeakTheory with (theory' := OLTheoryCut n) in H3;auto using TheoryEmb1.
    destruct OLIsFormula as [HC [HU [HB HQ]]]. 
    destruct OLIsFormulaD as [HCD [HUD [HBD HQD]]].

    apply seqtoSeqN in H2.  apply seqtoSeqN in H3. apply seqtoSeqN in Cut1.
    destruct H2 as [h1 H2]. destruct H3 as [h2 H3]. destruct Cut1 as [h3 Cut1].
    

    assert(Cut1': seq (OLTheoryCut n) Gamma ([] ++ N) ( >[(rq_leftBody (rulesQ C) FX0) ^] )).
    eapply @GeneralCut with (dualC := (rq_rightBody (rulesQ C) FX)) (C := (rq_rightBody (rulesQ C) FX) ^) ;
      eauto using OLTheoryWellFormed,  OLTheoryWellFormedD, IsPositiveAtomNotAsync, IsPositiveIsFormula, OLTheoryCutWellFormed, OLTheoryCutWellFormedD;simpl;auto...
    rewrite <- ng_involutive;auto.
    apply HQD.
    apply HQ.
    constructor. apply HQD. constructor.
    simpl in Cut1'.
    apply seqtoSeqN in Cut1'.
    destruct Cut1' as [h4 Cut1']. 

    
    eapply @GeneralCut with (dualC := (rq_leftBody (rulesQ C) FX0)) (C := (rq_leftBody (rulesQ C) FX0) ^) ;
      eauto using OLTheoryWellFormed,  OLTheoryWellFormedD, IsPositiveAtomNotAsync, IsPositiveIsFormula, OLTheoryCutWellFormed, OLTheoryCutWellFormedD;simpl;auto...
    rewrite <- ng_involutive;auto.
    apply HQD.
    apply HQ.
    
  Qed.

  (** Finding the right hypotheses to use the theorem [ConstantPrincipalCase] *)
  Ltac SolvePrincipalCaseCte :=
    apply WeakTheory with (theory := OLTheory) ;auto using TheoryEmb1;
    do 2 (match goal with
            [H : Permutation (?F :: _) (?F :: _) |- _ ] => apply Permutation_cons_inv in H;rewrite H
          end);
    try(
        match goal with
          [ H :  seq _ _ ?X (>>  rc_leftBody (rulesCte _)) |- seq _ _ (?X ++ _) _ ] => rewrite Permutation_app_comm
        end);
    eapply ConstantPrincipalCase;eauto using PermIsFormula, PermIsFormula'.

  (** Finding the right hypotheses to use the theorem [UConnectivePrincipalCase] *)
  Ltac SolvePrincipalCaseU :=
    do 2 (match goal with
            [H : Permutation (?F :: _) (?F :: _) |- _ ] => apply Permutation_cons_inv in H;rewrite H
          end);
    try(
        match goal with
          [ H :  seq _ _ ?X (>> ru_leftBody (rulesUnary _) _) |- seq _ _ (?X ++ _) _ ] => rewrite Permutation_app_comm
        end);
    eapply UConnectivePrincipalCase;eauto using PermIsFormula, PermIsFormula'.

  (** Finding the right hypotheses to use the theorem [BinConnectivePrincipalCase] *)
  Ltac SolvePrincipalCaseBin :=
    do 2 (match goal with
            [H : Permutation (?F :: _) (?F :: _) |- _ ] => apply Permutation_cons_inv in H;rewrite H
          end);
    try(
        match goal with
          [ H :  seq _ _ ?X (>> rb_leftBody (rulesBin _) _ _ ) |- seq _ _ (?X ++ _) _ ] => rewrite Permutation_app_comm
        end);
    eapply BinConnectivePrincipalCase;eauto using PermIsFormula, PermIsFormula'.


  (** Inductive hypothesis in the theorem [OLCutElimStep]. This is
  useful to simplify the theorems below *)
  Definition OOCutTheoremDef n' h : Prop :=
    forall m : nat,
      m <= h ->
      forall h2 h1 : nat,
        m = h1 + h2 ->
        forall n : nat,
          n' <= n ->
          forall FCut : uexp,
            isOLFormula FCut ->
            lengthUexp FCut n' ->
            forall M : list oo,
              IsPositiveAtomFormulaL M ->
              forall N : list oo,
                IsPositiveAtomFormulaL N ->
                forall Gamma : list oo,
                  IsPositiveAtomFormulaL Gamma ->
                  seqN OLTheory h1 Gamma N (>> atom (up FCut)) ->
                  seqN OLTheory h2 Gamma M (>> atom (down FCut)) -> seq (OLTheoryCut (pred n )) Gamma (M ++ N) (> []).

  (** The following theorems are instances of the cases when the FCut
  formula cannot be principal. For instance, when the focus is on a
  LeftRule and the current atom in the context is of the form [up
  FCut]. Similarly, when the focus is on a RightRule and the current
  atom in the context is of the form [down FCut].  *)
  
  Theorem RightBinDown n' h n0 n1 n FCut M N Gamma C0 F G:
    (seqN OLTheory n1 Gamma (atom (down FCut) :: M) (>> makeRRuleBin C0 F G)) ->
    OOCutTheoremDef n' h ->
    (S h = S (S (S n0)) + S (S (S n1))) -> 
    n' <= n ->
    isOLFormula FCut -> 
    lengthUexp FCut n' -> 
    IsPositiveAtomFormulaL M ->
    IsPositiveAtomFormulaL N ->
    IsPositiveAtomFormulaL Gamma -> 
    (seqN OLTheory (S (S (S n0))) Gamma N (>> atom (up FCut))) ->
    buildTheory (makeRRuleBin C0 F G) ->
    isOLFormula (t_bin C0 F G) ->
    seq (OLTheoryCut (pred n)) Gamma (M ++ N) (> []).
  Proof. 
    intros.
    unfold OOCutTheoremDef in *.
    SolveBinary.
  Qed.
  Theorem LeftBinUp n' h n0 n1 n FCut M N Gamma C0 F G:
    (seqN OLTheory n0 Gamma (atom (up FCut) :: N) (>> makeLRuleBin C0 F G)) ->
    OOCutTheoremDef n' h ->
    (S h = S (S (S n0)) + S (S (S n1))) -> 
    n' <= n ->
    isOLFormula FCut -> 
    lengthUexp FCut n' -> 
    IsPositiveAtomFormulaL M ->
    IsPositiveAtomFormulaL N ->
    IsPositiveAtomFormulaL Gamma -> 
    (seqN OLTheory (S (S (S n1))) Gamma M (>> atom (down FCut))) ->
    buildTheory (makeLRuleBin C0 F G) ->
    isOLFormula (t_bin C0 F G) ->
    seq (OLTheoryCut (pred n)) Gamma (M ++ N) (> []).
  Proof. 
    intros.
    unfold OOCutTheoremDef in *.
    SolveBinary.
  Qed.

  
  Theorem RightUnaryDown n' h n0 n1 n FCut M N Gamma C0 F:
    (seqN OLTheory n1 Gamma (atom (down FCut) :: M) (>> makeRRuleUnary C0 F)) ->
    OOCutTheoremDef n' h ->
    (S h = S (S (S n0)) + S (S (S n1))) -> 
    n' <= n ->
    isOLFormula FCut -> 
    lengthUexp FCut n' -> 
    IsPositiveAtomFormulaL M ->
    IsPositiveAtomFormulaL N ->
    IsPositiveAtomFormulaL Gamma -> 
    (seqN OLTheory (S (S (S n0))) Gamma N (>> atom (up FCut))) ->
    buildTheory (makeRRuleUnary C0 F ) ->
    isOLFormula (t_ucon C0 F) ->
    seq (OLTheoryCut (pred n)) Gamma (M ++ N) (> []).
  Proof. 
    intros.
    unfold OOCutTheoremDef in *.
    SolveUnary.
  Qed.

  Theorem LeftUnaryUp n' h n0 n1 n FCut M N Gamma C0 F:
    (seqN OLTheory n0 Gamma (atom (up FCut) :: N) (>> makeLRuleUnary C0 F)) ->
    OOCutTheoremDef n' h ->
    (S h = S (S (S n0)) + S (S (S n1))) -> 
    n' <= n ->
    isOLFormula FCut -> 
    lengthUexp FCut n' -> 
    IsPositiveAtomFormulaL M ->
    IsPositiveAtomFormulaL N ->
    IsPositiveAtomFormulaL Gamma -> 
    (seqN OLTheory (S (S (S n1))) Gamma M (>> atom (down FCut))) ->
    buildTheory (makeLRuleUnary C0 F ) ->
    isOLFormula (t_ucon C0 F) ->
    seq (OLTheoryCut (pred n)) Gamma (M ++ N) (> []).
  Proof. 
    intros.
    unfold OOCutTheoremDef in *.
    SolveUnary.
  Qed.

  
  Theorem RightCteDown n' h n0 n1 n FCut M N Gamma C0:
    (seqN OLTheory n1 Gamma (atom (down FCut) :: M) (>> makeRRuleConstant C0)) ->
    OOCutTheoremDef n' h ->
    (S h = S (S (S n0)) + S (S (S n1))) -> 
    n' <= n ->
    isOLFormula FCut -> 
    lengthUexp FCut n' -> 
    IsPositiveAtomFormulaL M ->
    IsPositiveAtomFormulaL N ->
    IsPositiveAtomFormulaL Gamma -> 
    (seqN OLTheory (S (S (S n0))) Gamma N (>> atom (up FCut))) ->
    buildTheory (makeRRuleConstant C0  ) ->
    isOLFormula (t_cons C0) ->
    seq (OLTheoryCut (pred n)) Gamma (M ++ N) (> []).
  Proof. 
    intros.
    unfold OOCutTheoremDef in *.
    SolveRightConstant.
  Qed.


  Theorem LeftCteUp n' h n0 n1 n FCut M N Gamma C0:
    (seqN OLTheory n0 Gamma (atom (up FCut) :: N) (>> makeLRuleConstant C0)) ->
    OOCutTheoremDef n' h ->
    (S h = S (S (S n0)) + S (S (S n1))) -> 
    n' <= n ->
    isOLFormula FCut -> 
    lengthUexp FCut n' -> 
    IsPositiveAtomFormulaL M ->
    IsPositiveAtomFormulaL N ->
    IsPositiveAtomFormulaL Gamma -> 
    (seqN OLTheory (S (S (S n1))) Gamma M (>> atom (down FCut))) ->
    buildTheory (makeLRuleConstant C0  ) ->
    isOLFormula (t_cons C0) ->
    seq (OLTheoryCut (pred n)) Gamma (M ++ N) (> []).
  Proof. 
    intros.
    unfold OOCutTheoremDef in *.
    SolveLeftConstant.
  Qed.

  Theorem LeftQuantUp n' h n0 n1 n FCut M N Gamma C0 F:
    (seqN OLTheory n0 Gamma (atom (up FCut) :: N) (>> makeLRuleQ C0 F)) ->
    OOCutTheoremDef n' h ->
    (S h = S (S (S n0)) + S (S (S n1))) -> 
    n' <= n ->
    isOLFormula FCut -> 
    lengthUexp FCut n' -> 
    IsPositiveAtomFormulaL M ->
    IsPositiveAtomFormulaL N ->
    IsPositiveAtomFormulaL Gamma -> 
    (seqN OLTheory (S (S (S n1))) Gamma M (>> atom (down FCut))) ->
    buildTheory (makeLRuleQ C0 F ) ->
    isOLFormula (t_quant C0 F) ->
    seq (OLTheoryCut (pred n)) Gamma (M ++ N) (> []).
  Proof. 
    intros.
    unfold OOCutTheoremDef in *.
    SolveQuantifier.
  Qed.

  Theorem RightQuantDown n' h n0 n1 n FCut M N Gamma C0 F:
    (seqN OLTheory n1 Gamma (atom (down FCut) :: M) (>> makeRRuleQ C0 F)) ->
    OOCutTheoremDef n' h ->
    (S h = S (S (S n0)) + S (S (S n1))) -> 
    n' <= n ->
    isOLFormula FCut -> 
    lengthUexp FCut n' -> 
    IsPositiveAtomFormulaL M ->
    IsPositiveAtomFormulaL N ->
    IsPositiveAtomFormulaL Gamma -> 
    (seqN OLTheory (S (S (S n0))) Gamma N (>> atom (up FCut))) ->
    buildTheory (makeRRuleQ C0 F ) ->
    isOLFormula (t_quant C0 F) ->
    seq (OLTheoryCut (pred n)) Gamma (M ++ N) (> []).
  Proof. 
    intros.
    unfold OOCutTheoremDef in *.
    SolveQuantifier.
  Qed.

  (** Solve all the trivial cases when the current atom cannot be
  principal *)
  Ltac SolveAll :=
    match goal with
    | [ HSeq :  seqN _ _ _ (atom (down _) :: _) (>> makeRRuleBin _ _ _) |- _ ] => eapply RightBinDown in HSeq;eauto
    | [ HSeq :  seqN _ _ _ (atom (down _) :: _) (>> makeRRuleUnary _ _) |- _ ] => eapply RightUnaryDown in HSeq;eauto
    | [ HSeq :  seqN _ _ _ (atom (down _) :: _) (>> makeRRuleConstant _) |- _ ] => eapply  RightCteDown in HSeq;eauto
    | [ HSeq :  seqN _ _ _ (atom (down _) :: _) (>> makeRRuleQ _ _) |- _ ] => eapply RightQuantDown in HSeq;eauto
    | [ HSeq :  seqN _ _ _ (atom (up _) :: _) (>> makeLRuleQ _ _) |- _ ] => eapply LeftQuantUp in HSeq;eauto
    | [ HSeq :  seqN _ _ _ (atom (up _) :: _) (>> makeLRuleConstant _) |- _ ] => eapply LeftCteUp in HSeq;eauto
    | [ HSeq :  seqN _ _ _ (atom (up _) :: _) (>> makeLRuleUnary _ _) |- _ ] => eapply LeftUnaryUp in HSeq; eauto
    | [ HSeq :  seqN _ _ _ (atom (up _) :: _) (>> makeLRuleBin _ _ _) |- _ ] => eapply LeftBinUp in HSeq; eauto
    end.

  Theorem PosAtomFocus' : forall  Gamma Th N X, (seq Th Gamma N (>> atom X)) ->
                                             (seq Th Gamma (atom X :: N) (> [])) .
    intros.
    FLLInversionAll.
    rewrite Permutation_app_comm in H6;auto.
  Qed.

  Theorem PosAtomFocus : forall Gamma Th N X h, (seqN Th h Gamma N (>> atom X)) ->
                                                (seq Th Gamma (atom X :: N) (> [])) .
    intros.
    apply seqNtoSeq in H.
    eapply PosAtomFocus';auto.
  Qed.

  (** Non Principal cases when the INIT rule is applied in one premise
  and some sequent rule in the other premise *)
  Theorem InitOtherRuleUp  n0 n1 n FCut M N Gamma F FInit:
    (seqN OLTheory n0 Gamma (atom (up FCut) :: N) (>> F)) ->
    isOLFormula FCut ->
    IsPositiveAtomFormulaL M ->
    IsPositiveAtomFormulaL N ->
    IsPositiveAtomFormulaL Gamma -> 
    (seqN OLTheory (S (S (S n1))) Gamma M (>> atom (down FCut))) ->
    (seqN OLTheory (S (S (S n0))) Gamma N (>> atom (up FCut))) ->
    (seqN OLTheory n1 Gamma (atom (down FCut) :: M) (>> RINIT FInit)) ->
    (isOLFormula FInit) -> 
    seq (OLTheoryCut (pred n)) Gamma (M ++ N) (> []) .
  Proof with CutTac.
    intros.
    apply Init_inversion2 with (M0:=M) in H6...
    destruct H8...
    apply PosAtomFocus in H5; apply WeakTheory with (theory := OLTheory);eauto using TheoryEmb1.
    invTri H5.
    apply seqNtoSeq in H13.
    apply AbsorptionClassic in H13...
    apply WeakTheory with (theory := OLTheory);eauto using TheoryEmb1.
    apply IsPositiveAtomNotAsync...
  Qed.
  
  Theorem InitOtherRuleDown n0 n1 n FCut M N Gamma F FInit:
    (seqN OLTheory n0 Gamma (atom (up FCut) :: N) (>> F)) ->
    isOLFormula FCut ->
    IsPositiveAtomFormulaL M ->
    IsPositiveAtomFormulaL N ->
    IsPositiveAtomFormulaL Gamma -> 
    (seqN OLTheory (S (S (S n0))) Gamma N (>> atom (up FCut))) ->
    (seqN OLTheory (S n1) Gamma (atom (down FCut) :: M) (> [])) ->
    (seqN OLTheory n0 Gamma (atom (up FCut) :: N) (>> RINIT FInit)) ->
    (isOLFormula FInit) -> 
    seq (OLTheoryCut (pred n)) Gamma (M ++ N) (> []) .
  Proof with CutTac.
    intros.
    apply Init_inversion1 with (M0:=M) in H6...
    destruct H8...
    apply PosAtomFocus in H4; apply WeakTheory with (theory := OLTheory);eauto using TheoryEmb1.
    apply seqNtoSeq in H5.
    rewrite Permutation_app_comm...
    
    assert (seq OLTheory Gamma M (> [atom (down FInit)]))...
    solveLL.
    apply seqNtoSeq in H5.
    rewrite Permutation_app_comm...
    apply AbsorptionClassic in H6...
    rewrite app_nil_r.
    apply WeakTheory with (theory := OLTheory);eauto using TheoryEmb1.
    apply IsPositiveAtomNotAsync...
  Qed.


  
  (** Main theorem showing that it is possible to fins a proof with
  the theory [ (OLTheoryCut (pred n) )] *)
  Theorem OLCutElimStep :
    forall h1 h2 n N M Gamma FCut n',
      isOLFormula FCut ->
      IsPositiveAtomFormulaL Gamma ->
      IsPositiveAtomFormulaL N ->
      IsPositiveAtomFormulaL M ->
      (seqN OLTheory h1 Gamma N (>> (atom (up FCut) )) ) ->
      (seqN OLTheory h2 Gamma M (>> (atom (down FCut) )) ) ->
      lengthUexp FCut n' -> n'<=n ->
      (seq (OLTheoryCut (pred n) ) Gamma (M ++ N) (> [])) .
  Proof with try CutTac.
    intros h1 h2 n N M Gamma FCut n' HisF PosG PosN PosM Hseq1 Hseq2 HL HL'.
    remember (plus h1 h2) as h.
    generalize dependent Gamma.
    generalize dependent N.
    generalize dependent M.
    generalize dependent FCut.
    generalize dependent n. 
    generalize dependent h1.
    generalize dependent h2.

    induction h using strongind;intros.
    (* base case... there is no proof of size 0 *)
    assert (h1 = 0) by lia ...
    inversion Hseq1.
    
    (* Inductive case *)
    
    FocusStepAtom Hseq1. rename Hseq0 into Hseq1'.
    FocusStepAtom Hseq2. rename Hseq0 into Hseq2'.

    inversion Hseq1'... rename H2 into Hseq1''.
    inversion Hseq2'... rename H4 into Hseq2''.
    
    (* Now we proceed by cases on the last rule applied on both
    derivations Hseq1'' and Hseq2'' *)
    inversion H0 ;inversion H2...
    
    inversion H4;CutTac ;inversion H6;CutTac;try SolveAll.

    (* The remaining 16 cases are possible principal cases: focus on a
    RightFormula and the atom is of the form (up FCut *)
    
    { (* constant and constant *)
      wellConstant Hseq1''.
      + (* axiom *)
        destruct H8;CleanContext.
        
        CaseIn H1.
        { (* principal case *)
          wellConstant Hseq2''.
          destruct H9;CleanContext.
          CaseIn H9.
          (* principal case *)
          SolvePrincipalCaseCte.
          
          rewrite H9;simpl. apply H11...
          apply H11...
          
          destruct H11;CleanContext.
          CaseIn H11.
          (* principal case*)
          SolvePrincipalCaseCte.
          
          SolveOnePremise.
          SolveOnePremise.
        }
        rewrite H1;rewrite Permutation_app_comm;simpl. apply H8...
        apply H8...
      + (*one premise *)
        destruct H8;CleanContext;[| SolveOnePremise].
        CaseIn H8;[| SolveOnePremise].
        {
          wellConstant Hseq2''.
          destruct H12;CleanContext.
          CaseIn H12.
          (* principal case *)
          SolvePrincipalCaseCte.
          rewrite H12;simpl. apply H15...
          apply H15...
          
          destruct H15;CleanContext.
          CaseIn H15;[SolvePrincipalCaseCte | SolveOnePremise ].
          SolveOnePremise.
          
        }
    }
    { (* constant and unary connective *)
      wellFormedU Hseq2'';destruct bpEnum; bipoleUnary.
      destruct H8;CleanContext.
      CaseIn H8;[ | SolveOnePremise].
      {  (* the other cannot be principal *)
        wellConstant Hseq1''.
        destruct H12;CleanContext.
        UpDownMismatch.
        rewrite H12. rewrite Permutation_app_comm;simpl. apply H15...
        apply H15...

        destruct H15;CleanContext.
        UpDownMismatch; SolveOnePremise.
        SolveOnePremise.
      }
      SolveOnePremise.
      
      destruct H10;CleanContext.
      CaseIn H10.
      {
        wellConstant Hseq1''.
        destruct H15;CleanContext.
        UpDownMismatch. 
        rewrite H15. rewrite Permutation_app_comm;simpl. apply H18...
        apply H18...

        destruct H18;CleanContext;[ | SolveOnePremise].
        UpDownMismatch;
          SolveOnePremise.
      }  
      CaseIn H15; SolveTwoPremises.
      CaseIn H11; SolveTwoPremises.

      destruct H10;CleanContext.
      CaseIn H10.
      {
        wellConstant Hseq1''.
        destruct H15;CleanContext.
        UpDownMismatch. 
        rewrite H15. rewrite Permutation_app_comm;simpl. apply H18...
        apply H18...

        destruct H18;CleanContext.
        UpDownMismatch.  SolveOnePremise.
        SolveOnePremise.
      }
      SolveTwoPremisesAddLinear.
      SolveTwoPremisesAdClassic.
    }
    
    { (* binary and right constant *)
      wellFormedBin Hseq2'';destruct bpEnum; bipoleBinary.
      destruct H8;CleanContext.
      CaseIn H8;[|SolveOnePremise].
      {  (* the other cannot be principal *)
        wellConstant Hseq1''.
        destruct H12;CleanContext.
        UpDownMismatch. 
        rewrite H12. rewrite Permutation_app_comm;simpl. apply H15...
        apply H15...

        destruct H15;CleanContext.
        UpDownMismatch;  SolveOnePremise.
        SolveOnePremise.
        
      }
      SolveOnePremise.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* the other cannot be principal *)
        wellConstant Hseq1''.
        destruct H15;CleanContext.
        UpDownMismatch. 
        rewrite H15. rewrite Permutation_app_comm;simpl. apply H18...
        apply H18...

        destruct H18;CleanContext.
        UpDownMismatch.  SolveOnePremise.
        SolveOnePremise.
      } 
      CaseIn H15; SolveTwoPremises.
      CaseIn H11; SolveTwoPremises.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* the other cannot be principal *)
        wellConstant Hseq1''.
        destruct H15;CleanContext.
        UpDownMismatch. 
        rewrite H15. rewrite Permutation_app_comm;simpl. apply H18...
        apply H18...

        destruct H18;CleanContext.
        UpDownMismatch;  SolveOnePremise.
        SolveOnePremise.
      }
      SolveTwoPremisesAddLinear.
      SolveTwoPremisesAdClassic.
    }

    { (* quantifier and right constant *)
      wellFormedQ Hseq2''; bipoleQ.
      destruct H8;CleanContext.
      CaseIn H8;[|SolveOnePremise].
      {  (* the other cannot be principal *)
        wellConstant Hseq1''.
        destruct H12;CleanContext.
        UpDownMismatch;
          rewrite H12. rewrite Permutation_app_comm;simpl. apply H15...
        apply H15...

        destruct H15;CleanContext.
        UpDownMismatch;  SolveOnePremise.
        SolveOnePremise.
        
      }
      SolveOnePremise.
    }

    { (* unary and left constant *)
      wellFormedU Hseq1''; destruct bpEnum;bipoleUnary.
      destruct H8;CleanContext.
      CaseIn H8;[|SolveOnePremise].
      {  (* the other cannot be principal *)
        wellConstant Hseq2''.
        destruct H12;CleanContext.
        UpDownMismatch. 
        rewrite H12. apply H15...
        apply H15...

        destruct H15;CleanContext.
        UpDownMismatch.  SolveOnePremise.
        SolveOnePremise.
      }
      SolveOnePremise.

      destruct H10;CleanContext.
      CaseIn H10.
      {
        (* the other cannot be principal *)
        wellConstant Hseq2''.
        destruct H15;CleanContext.
        UpDownMismatch. 
        rewrite H15.  apply H18...
        apply H18...

        destruct H18;CleanContext.
        UpDownMismatch.  SolveOnePremise.
        SolveOnePremise.
      }
      CaseIn H15;SolveTwoPremises.
      CaseIn H11;SolveTwoPremises.

      destruct H10;CleanContext.
      CaseIn H10. 
      {
        (* the other cannot be principal *)
        wellConstant Hseq2''.
        destruct H15;CleanContext.
        UpDownMismatch. 
        rewrite H15.  apply H18...
        apply H18...

        destruct H18;CleanContext.
        UpDownMismatch.  SolveOnePremise.
        SolveOnePremise.
      }
      SolveTwoPremisesAddLinear'.
      SolveTwoPremisesAdClassic'.
    }

    { (* unary unary *) 
      wellFormedU Hseq1'';destruct bpEnum; bipoleUnary.
      + (*one premise *)
        destruct H8;CleanContext.
        (* linear context *)
        CaseIn H8.
        {
          wellFormedU Hseq2'';destruct bpEnum; bipoleUnary.
          destruct H15;CleanContext.
          CaseIn H15;[|SolveOnePremise].
          (* principal case *)
          SolvePrincipalCaseU.
          SolveOnePremise.
          
          destruct H17;CleanContext.
          CaseIn H17.
          { (* principal case *)
            SolvePrincipalCaseU. 
          }
          CaseIn H22.
          SolveCaseTwoPremisesCut H19 Hseq1 H H23 H20 n.
          SolveCaseTwoPremisesCut H20 Hseq1 H H23 H19 n.
          CaseIn H18.
          SolveCaseTwoPremisesCut H20 Hseq1 H H24 H21 n.
          SolveCaseTwoPremisesCut H21 Hseq1 H H24 H20 n.

          (* two premises additive *)
          destruct H17;CleanContext.
          (* linear case *)
          CaseIn H17.
          (* principal case *)
          SolvePrincipalCaseU.
          SolveTwoPremisesAddLinear.
          (* classical case *)
          SolveTwoPremisesAdClassic.
        }
        SolveOnePremise.
        (* classical case *)
        SolveOnePremise.
      + (* two premise *)
        destruct H10;CleanContext.
        (* linear context *)
        CaseIn H10.
        {
          wellFormedU Hseq2'';destruct bpEnum; bipoleUnary.
          destruct H18;CleanContext.
          CaseIn H18.
          { (* principal case *)
            SolvePrincipalCaseU. 
          }
          SolveOnePremise.
          SolveOnePremise.
          destruct H20;CleanContext.
          CaseIn H20.
          { (* principal case *)
            SolvePrincipalCaseU. 
          }
          CaseIn H25.
          SolveCaseTwoPremisesCut H22 Hseq1 H H26 H23 n.
          SolveCaseTwoPremisesCut H23 Hseq1 H H26 H22 n.
          CaseIn H21.
          SolveCaseTwoPremisesCut H23 Hseq1 H H27 H24 n.
          SolveCaseTwoPremisesCut H24 Hseq1 H H27 H23 n.

          destruct H20;CleanContext.
          CaseIn H20.
          { (* principal case *)
            SolvePrincipalCaseU. 
          }
          SolveTwoPremisesAddLinear.
          SolveTwoPremisesAdClassic.
        }
        CaseIn H15; SolveTwoPremises.
        (* classical case *)
        CaseIn H11; SolveTwoPremises.
      + (* two premises additive *)
        destruct H10;CleanContext.
        (* linear context *)
        CaseIn H10.
        {
          wellFormedU Hseq2'';destruct bpEnum; bipoleUnary.
          destruct H18;CleanContext.
          CaseIn H18.
          { (* principal case *)
            SolvePrincipalCaseU. 
          }
          SolveOnePremise.
          SolveOnePremise.
          destruct H20;CleanContext.
          CaseIn H20.
          (* principal case *)
          SolvePrincipalCaseU. 
          
          CaseIn H25.
          SolveCaseTwoPremisesCut H22 Hseq1 H H26 H23 n.
          SolveCaseTwoPremisesCut H23 Hseq1 H H26 H22 n.
          CaseIn H21.
          SolveCaseTwoPremisesCut H23 Hseq1 H H27 H24 n.
          SolveCaseTwoPremisesCut H24 Hseq1 H H27 H23 n.
          destruct H20;CleanContext.
          CaseIn H20.
          (* principal case *)
          SolvePrincipalCaseU. 
          
          SolveTwoPremisesAddLinear.
          SolveTwoPremisesAdClassic.
        }
        SolveTwoPremisesAddLinear'.
        SolveTwoPremisesAdClassic'.
    }
    { (* binary and unary *)
      wellFormedU Hseq1'';destruct bpEnum; bipoleUnary.
      destruct H8;CleanContext.
      CaseIn H8;[|SolveOnePremise].
      (* priniciapl the other cannot be *)
      { wellFormedBin Hseq2'';destruct bpEnum;bipoleBinary.
        destruct H15;CleanContext.
        UpDownMismatch.
        SolveOnePremise.
        SolveOnePremise.

        destruct H17;CleanContext.
        UpDownMismatch.
        CaseIn HDIFF1.
        SolveCaseTwoPremisesCut H19 Hseq1 H H23 H20 n.
        SolveCaseTwoPremisesCut H20 Hseq1 H H23 H19 n.
        CaseIn H18.
        SolveCaseTwoPremisesCut H20 Hseq1 H H24 H21 n.
        SolveCaseTwoPremisesCut H21 Hseq1 H H24 H20 n.

        destruct H17;CleanContext.
        UpDownMismatch.
        SolveTwoPremisesAddLinear.
        SolveTwoPremisesAdClassic.
        
      }
      SolveOnePremise.
      destruct H10;CleanContext.
      CaseIn H10.
      { (* principal the other cannot be *)
        wellFormedBin Hseq2'';destruct bpEnum;bipoleBinary.
        destruct H18;CleanContext.
        UpDownMismatch.
        SolveOnePremise.
        SolveOnePremise.

        destruct H20;CleanContext.
        UpDownMismatch.
        CaseIn HDIFF1.
        SolveCaseTwoPremisesCut H22 Hseq1 H H26 H23 n.
        SolveCaseTwoPremisesCut H23 Hseq1 H H26 H22 n.
        CaseIn H21.
        SolveCaseTwoPremisesCut H23 Hseq1 H H27 H24 n.
        SolveCaseTwoPremisesCut H24 Hseq1 H H27 H23 n.

        destruct H20;CleanContext.
        UpDownMismatch.
        SolveTwoPremisesAddLinear.
        SolveTwoPremisesAdClassic.
      }
      CaseIn H15; SolveTwoPremises.
      CaseIn H11; SolveTwoPremises.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* principal the other cannot be *)
        wellFormedBin Hseq2'';destruct bpEnum;bipoleBinary.
        destruct H18;CleanContext.
        UpDownMismatch.
        SolveOnePremise.
        SolveOnePremise.

        destruct H20;CleanContext.
        UpDownMismatch.
        CaseIn HDIFF1.
        SolveCaseTwoPremisesCut H22 Hseq1 H H26 H23 n.
        SolveCaseTwoPremisesCut H23 Hseq1 H H26 H22 n.
        CaseIn H21.
        SolveCaseTwoPremisesCut H23 Hseq1 H H27 H24 n.
        SolveCaseTwoPremisesCut H24 Hseq1 H H27 H23 n.

        destruct H20;CleanContext.
        UpDownMismatch.
        SolveTwoPremisesAddLinear.
        SolveTwoPremisesAdClassic.
      }
      SolveTwoPremisesAddLinear'.
      SolveTwoPremisesAdClassic'.
    }

    { (* unary and quantifieer *)
      wellFormedU Hseq1'';destruct bpEnum; bipoleUnary.
      destruct H8;CleanContext.
      CaseIn H8;[|SolveOnePremise].
      (* priniciapl the other cannot be *)
      { wellFormedQ Hseq2'';bipoleQ.
        destruct H15;CleanContext.
        UpDownMismatch.
        SolveOnePremise.
        SolveOnePremise.
      }
      SolveOnePremise.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* principal the other cannot be *)
        wellFormedQ Hseq2'';bipoleQ.
        destruct H18;CleanContext.
        UpDownMismatch.
        SolveOnePremise.
        SolveOnePremise.
      }
      CaseIn H15; SolveTwoPremises.
      CaseIn H11; SolveTwoPremises.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* principal the other cannot be *)
        wellFormedQ Hseq2'';bipoleQ.
        destruct H18;CleanContext.
        UpDownMismatch.
        SolveOnePremise.
        SolveOnePremise.
      }
      SolveTwoPremisesAddLinear'.
      SolveTwoPremisesAdClassic'.
    }
    { (* constant adn bin *)
      wellFormedBin Hseq1'' ; destruct bpEnum ;  bipoleBinary.
      destruct H8;CleanContext.
      CaseIn H8;[|SolveOnePremise].
      { (* the other cannot be principal *)
        wellConstant Hseq2''.
        destruct H12;CleanContext.
        UpDownMismatch. 
        rewrite H12.  apply H15...
        apply H15...

        destruct H15;CleanContext.
        UpDownMismatch.  SolveOnePremise.
        SolveOnePremise.
      }
      SolveOnePremise.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* the other cannot be principal *)
        wellConstant Hseq2''.
        destruct H15;CleanContext.
        UpDownMismatch. 
        rewrite H15.  apply H18...
        apply H18...

        destruct H18;CleanContext.
        UpDownMismatch.  SolveOnePremise.
        SolveOnePremise.
      }
      CaseIn H15;SolveTwoPremises.
      CaseIn H11;SolveTwoPremises.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* the other cannot be principal *)
        wellConstant Hseq2''.
        destruct H15;CleanContext.
        UpDownMismatch. 
        rewrite H15.  apply H18...
        apply H18...

        destruct H18;CleanContext.
        UpDownMismatch.  SolveOnePremise.
        SolveOnePremise.
      }
      SolveTwoPremisesAddLinear'.
      SolveTwoPremisesAdClassic'.
    }
    { (* binary and unary *)
      wellFormedU Hseq2'';destruct bpEnum; bipoleUnary.
      destruct H8;CleanContext.
      CaseIn H8;[|SolveOnePremise].
      (* priniciapl the other cannot be *)
      { wellFormedBin Hseq1'';destruct bpEnum;bipoleBinary.
        destruct H15;CleanContext.
        UpDownMismatch.
        SolveOnePremise.
        SolveOnePremise.

        destruct H17;CleanContext.
        UpDownMismatch.
        CaseIn HDIFF1. 
        SolveCaseTwoPremisesCut H19 Hseq2 H H23 H20 n.
        SolveCaseTwoPremisesCut H20 Hseq2 H H23 H19 n.
        CaseIn H18.
        SolveCaseTwoPremisesCut H20 Hseq2 H H24 H21 n.
        SolveCaseTwoPremisesCut H21 Hseq2 H H24 H20 n.

        destruct H17;CleanContext.
        UpDownMismatch.
        SolveTwoPremisesAddLinear'.
        SolveTwoPremisesAdClassic'.
        
      }
      SolveOnePremise.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* principal the other cannot be *)
        wellFormedBin Hseq1'';destruct bpEnum;bipoleBinary.
        destruct H18;CleanContext.
        UpDownMismatch.
        SolveOnePremise.
        SolveOnePremise.

        destruct H20;CleanContext.
        UpDownMismatch.
        CaseIn HDIFF1.
        SolveCaseTwoPremisesCut H22 Hseq2 H H26 H23 n.
        SolveCaseTwoPremisesCut H23 Hseq2 H H26 H22 n.
        CaseIn H21.
        SolveCaseTwoPremisesCut H23 Hseq2 H H27 H24 n.
        SolveCaseTwoPremisesCut H24 Hseq2 H H27 H23 n.
        
        destruct H20;CleanContext.
        UpDownMismatch.
        SolveTwoPremisesAddLinear'.
        SolveTwoPremisesAdClassic'.
      }
      CaseIn H15; SolveTwoPremises.
      CaseIn H11; SolveTwoPremises.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* principal the other cannot be *)
        wellFormedBin Hseq1'';destruct bpEnum;bipoleBinary.
        destruct H18;CleanContext.
        UpDownMismatch.
        SolveOnePremise.
        SolveOnePremise.

        destruct H20;CleanContext.
        UpDownMismatch.
        CaseIn HDIFF1.
        SolveCaseTwoPremisesCut H22 Hseq2 H H26 H23 n.
        SolveCaseTwoPremisesCut H23 Hseq2 H H26 H22 n.
        CaseIn H21.
        SolveCaseTwoPremisesCut H23 Hseq2 H H27 H24 n.
        SolveCaseTwoPremisesCut H24 Hseq2 H H27 H23 n.
        
        destruct H20;CleanContext.
        UpDownMismatch.
        SolveTwoPremisesAddLinear'.
        SolveTwoPremisesAdClassic'.
      }
      SolveTwoPremisesAddLinear.
      SolveTwoPremisesAdClassic.
    }
    
    { (* binary binary *)
      wellFormedBin Hseq1'';destruct bpEnum; bipoleBinary.
      + (*one premise *)
        destruct H8;CleanContext.
        (* linear context *)
        CaseIn H8;[|SolveOnePremise].
        {
          wellFormedBin Hseq2'';destruct bpEnum; bipoleBinary.
          destruct H15;CleanContext.
          CaseIn H15.
          { (* principal case *)
            SolvePrincipalCaseBin.
          }
          
          SolveOnePremise.
          SolveOnePremise.
          destruct H17;CleanContext.
          CaseIn H17.
          { (* principal case *)
            SolvePrincipalCaseBin.
          }
          CaseIn H22.
          clear H13.
          SolveCaseTwoPremisesCut H19 Hseq1 H H23 H20 n.
          SolveCaseTwoPremisesCut H20 Hseq1 H H23 H19 n.
          CaseIn H18.
          SolveCaseTwoPremisesCut H20 Hseq1 H H24 H21 n.
          SolveCaseTwoPremisesCut H21 Hseq1 H H24 H20 n.

          destruct H17;CleanContext.
          CaseIn H17.
          { (* principal case *)
            SolvePrincipalCaseBin.
          }
          SolveTwoPremisesAddLinear.
          SolveTwoPremisesAdClassic.
          
          
        }
        (* classical case *)
        SolveOnePremise.
      + (* two premise *)
        destruct H10;CleanContext.
        (* linear context *)
        CaseIn H10.
        {
          wellFormedBin Hseq2'';destruct bpEnum; bipoleBinary.
          destruct H18;CleanContext.
          CaseIn H18;[|SolveOnePremise].
          { (* principal case *)
            SolvePrincipalCaseBin.
          }
          SolveOnePremise.

          destruct H20;CleanContext.
          CaseIn H20.
          { (* principal case *)
            SolvePrincipalCaseBin.
          }
          CaseIn H25.
          SolveCaseTwoPremisesCut H22 Hseq1 H H26 H23 n.
          SolveCaseTwoPremisesCut H23 Hseq1 H H26 H22 n.
          CaseIn H21.
          SolveCaseTwoPremisesCut H23 Hseq1 H H27 H24 n.
          SolveCaseTwoPremisesCut H24 Hseq1 H H27 H23 n.

          destruct H20;CleanContext.
          CaseIn H20.
          { (* principal case *)
            SolvePrincipalCaseBin.
          }
          SolveTwoPremisesAddLinear.
          SolveTwoPremisesAdClassic.
        }
        CaseIn H15; SolveTwoPremises.
        (* classical case *)
        CaseIn H11; SolveTwoPremises.
      + (* two premises additive *)
        destruct H10;CleanContext.
        (* linear context *)
        CaseIn H10.
        {
          wellFormedBin Hseq2'';destruct bpEnum; bipoleBinary.
          destruct H18;CleanContext.
          CaseIn H18;[|SolveOnePremise].
          (* principal case *)
          SolvePrincipalCaseBin.
          
          SolveOnePremise.

          destruct H20;CleanContext.
          CaseIn H20.
          (* principal case *)
          SolvePrincipalCaseBin.
          
          CaseIn H25.
          SolveCaseTwoPremisesCut H22 Hseq1 H H26 H23 n.
          SolveCaseTwoPremisesCut H23 Hseq1 H H26 H22 n.
          CaseIn H21.
          SolveCaseTwoPremisesCut H23 Hseq1 H H27 H24 n.
          SolveCaseTwoPremisesCut H24 Hseq1 H H27 H23 n.

          destruct H20;CleanContext.
          CaseIn H20.
          (* principal case *)
          SolvePrincipalCaseBin.
          
          SolveTwoPremisesAddLinear.
          SolveTwoPremisesAdClassic.
        }
        SolveTwoPremisesAddLinear'.
        SolveTwoPremisesAdClassic'.
    }
    
    { (* binary and quantifieer *)
      wellFormedBin Hseq1'';destruct bpEnum; bipoleBinary.
      destruct H8;CleanContext.
      CaseIn H8;[|SolveOnePremise].
      (* priniciapl the other cannot be *)
      { wellFormedQ Hseq2'';bipoleQ.
        destruct H15;CleanContext.
        UpDownMismatch;
          SolveOnePremise.
        SolveOnePremise.
      }
      SolveOnePremise.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* principal the other cannot be *)
        wellFormedQ Hseq2'';bipoleQ.
        destruct H18;CleanContext.
        UpDownMismatch;
          SolveOnePremise.
        SolveOnePremise.
      }
      CaseIn H15; SolveTwoPremises.
      CaseIn H11; SolveTwoPremises.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* principal the other cannot be *)
        wellFormedQ Hseq2'';bipoleQ.
        destruct H18;CleanContext.
        UpDownMismatch;
          SolveOnePremise.
        SolveOnePremise.
      }
      SolveTwoPremisesAddLinear'.
      SolveTwoPremisesAdClassic'.
    }
    
    { (* constant and quantifier *)
      wellFormedQ Hseq1'';bipoleQ.
      destruct H8;CleanContext.
      CaseIn H8;[|SolveOnePremise].
      { (* the other cannot be principal *)
        wellConstant Hseq2''.
        destruct H12;CleanContext.
        UpDownMismatch. 
        rewrite H12.  apply H15...
        apply H15...

        destruct H15;CleanContext.
        UpDownMismatch.  SolveOnePremise.
        SolveOnePremise.
      }
      SolveOnePremise.
    }

    { (* unary and quantifieer *)
      wellFormedU Hseq2'';destruct bpEnum; bipoleUnary.
      destruct H8;CleanContext.
      CaseIn H8;[|SolveOnePremise].
      (* priniciapl the other cannot be *)
      { wellFormedQ Hseq1'';bipoleQ.
        destruct H15;CleanContext.
        UpDownMismatch;
          SolveOnePremise.
        SolveOnePremise.
      }
      SolveOnePremise.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* principal the other cannot be *)
        wellFormedQ Hseq1'';bipoleQ.
        destruct H18;CleanContext.
        UpDownMismatch;
          SolveOnePremise.
        SolveOnePremise.
      }
      CaseIn H15; SolveTwoPremises.
      CaseIn H11; SolveTwoPremises.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* principal the other cannot be *)
        wellFormedQ Hseq1'';bipoleQ.
        destruct H18;CleanContext.
        UpDownMismatch.
        SolveOnePremise.
        SolveOnePremise.
      }
      SolveTwoPremisesAddLinear.
      SolveTwoPremisesAdClassic.

    }
    { (* binary and quantifieer *)
      wellFormedBin Hseq2'';destruct bpEnum; bipoleBinary.
      destruct H8;CleanContext.
      CaseIn H8;[|SolveOnePremise].
      (* priniciapl the other cannot be *)
      { wellFormedQ Hseq1'';bipoleQ.
        destruct H15;CleanContext.
        UpDownMismatch;
          SolveOnePremise.
        SolveOnePremise.
      }
      SolveOnePremise.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* principal the other cannot be *)
        wellFormedQ Hseq1'';bipoleQ.
        destruct H18;CleanContext.
        UpDownMismatch.
        SolveOnePremise.
        SolveOnePremise.
      }
      CaseIn H15; SolveTwoPremises.
      CaseIn H11; SolveTwoPremises.

      destruct H10;CleanContext.
      CaseIn H10.
      { (* principal the other cannot be *)
        wellFormedQ Hseq1'';bipoleQ.
        destruct H18;CleanContext.
        UpDownMismatch.
        SolveOnePremise.
        SolveOnePremise.
      }
      SolveTwoPremisesAddLinear.
      SolveTwoPremisesAdClassic.
    }
    
    { (* Quantifier Quantifier *)
      wellFormedQ Hseq1'';  bipoleQ.
      + (*one premise *)
        destruct H8;CleanContext.
        (* linear context *)
        CaseIn H8.
        {  
          wellFormedQ Hseq2''.
          bipoleQ.
          destruct H15;CleanContext.
          apply Permutation_cons_inv in H8.

          apply PProp_perm_select in H15.
          destruct H15.
          destruct H15.
          inversion H15...
          { (* principal case *)
            rewrite H19. rewrite H8.
            rewrite Permutation_app_comm.
            eapply QuantifierPrincipalCase;eauto using PermIsFormula, PermIsFormula'.
          }
          CleanContext.
          rewrite H15 in H17.
          SolveOnePremise. rewrite H8;perm.
          SolveOnePremise.
        }
        SolveOnePremise.
        (* classical case *)
        SolveOnePremise.
    }
    { (* INIT and another rule *)
      eapply InitOtherRuleUp;eauto.
      
    }
    { (* INIT and another rule *)
      eapply InitOtherRuleDown;eauto.
    } 
    { (* INIT INIT *)
      
      apply Init_inversion1 with (M0 := N) in Hseq1''...
      apply Init_inversion2 with (M0 := M) in Hseq2''...
      clear H.
      destruct H7;destruct H8...

      decide3 (RINIT OO0)...
      tensor [atom (up OO0) ][ atom (down OO0)].

      decide3 (RINIT OO0)...
      tensor (@nil oo) [ atom (down OO0)].

      decide3 (RINIT OO0)...
      tensor [atom (up OO0) ] (@nil oo).

      decide3 (RINIT OO0)...
      tensor (@nil oo) (@nil oo).
    }
  Qed. 

  (** A particular instance of the previous theorem for constants *)
  Theorem OLCutElimStepCte :
    forall h1 h2 N M Gamma FCut,
      isOLConstant FCut ->
      IsPositiveAtomFormulaL Gamma ->
      IsPositiveAtomFormulaL N ->
      IsPositiveAtomFormulaL M ->
      (seqN OLTheory h1 Gamma N (>> (atom (up FCut) )) ) ->
      (seqN OLTheory h2 Gamma M (>> (atom (down FCut) )) )  ->
      (seq (OLTheoryCut 0 ) Gamma (M ++ N) (> [])) .
    intros.
    assert(lengthUexp FCut 1) ...
    inversion H...
    constructor.
    change 0 with (pred 1).
    eapply OLCutElimStep;eauto.
  Qed.

  (** A particular instance of the previous theorem for atomic propositions *)
  Theorem OLAtomicCutElimStep :
    forall h1 h2 A Gamma M N,
      isOLAtom A ->
      IsPositiveAtomFormulaL Gamma ->
      IsPositiveAtomFormulaL M ->
      IsPositiveAtomFormulaL N ->
      (seqN OLTheory h1 Gamma N (>> (atom (up A) )) ) ->
      (seqN OLTheory h2 Gamma M (>> (atom (down A) )) ) ->
      (seq OLTheory Gamma (M ++ N) (> [])) .
  Proof with CutTac.
    intros.
    assert(lengthUexp A 1) ...
    inversion H...
    constructor.
    assert ((seq (OLTheoryCut 0 ) Gamma (M ++ N) (> [])) ).
    change 0 with (pred 1).
    eapply OLCutElimStep;eauto.
    inversion H...
    apply WeakTheory with (theory' := OLTheory) in H6;auto;try apply  OOTheryCut0.
  Qed.
  
  Theorem OLCutElimAux :
    forall n h  B N ,
      IsPositiveAtomFormulaL B ->
      IsPositiveAtomFormulaL N ->
      seqN  (OLTheoryCut n) h  B N (>[] ) ->
      seq   (OLTheoryCut 0) B     N (>[] ) .
  Proof with CutTac.
    induction n ; induction h using strongind ; intros.
    eapply seqNtoSeq;eauto.
    eapply seqNtoSeq;eauto.
    inversion H1.
    
    inversion H2...
    inversion H4...
    inversion H3...
    + (* constant *)
      inversion H7...
      wellConstant H6.
      destruct H9;CleanContext.
      rewrite H5. apply H10...
      apply H10...
      
      destruct H10;CleanContext.
      apply H in H12...
      FindSolution H12.
      apply H in H12...
    + (* constant *)
      inversion H7...
      
      wellConstant H6.
      destruct H9;CleanContext.
      rewrite H5. apply H10...
      apply H10...

      destruct H10;CleanContext.
      apply H in H12...
      FindSolution H12.
      apply H in H12...
    + (* unary *)
      wellFormedU H6;destruct bpEnum; bipoleUnary.
      destruct H9;CleanContext.
      apply H in H11... FindSolution H11.
      apply H in H11...

      destruct H11;CleanContext.
      apply H in H13... apply H in H14... FindSolution H14.
      apply H in H14... apply H in H15... FindSolution H14.

      destruct H11;CleanContext.
      apply H in H13... apply H in H14... FindSolution H14.
      apply H in H14... apply H in H15... FindSolution H14.
      
    +  (* Unary *)
      wellFormedU H6;destruct bpEnum; bipoleUnary.
      destruct H9;CleanContext.
      apply H in H11... FindSolution H11.
      apply H in H11...

      destruct H11;CleanContext.
      apply H in H13... apply H in H14... FindSolution H14.
      apply H in H14... apply H in H15... FindSolution H14.
      destruct H11;CleanContext.
      apply H in H13... apply H in H14... FindSolution H14.
      apply H in H14... apply H in H15... FindSolution H14.
      
    + (* right rule *)
      wellFormedBin H6;destruct bpEnum; bipoleBinary.
      destruct H9;CleanContext.
      apply H in H11... FindSolution H11.
      apply H in H11...

      destruct H11;CleanContext.
      apply H in H13... apply H in H14... FindSolution H14.
      apply H in H14... apply H in H15... FindSolution H14.
      destruct H11;CleanContext.
      apply H in H13... apply H in H14... FindSolution H14.
      apply H in H14... apply H in H15... FindSolution H14.
      
    + (* left binary rule *)
      wellFormedBin H6;destruct bpEnum; bipoleBinary.
      destruct H9;CleanContext.
      apply H in H11... FindSolution H11.
      apply H in H11...

      destruct H11;CleanContext.
      apply H in H13... apply H in H14... FindSolution H14.
      apply H in H14... apply H in H15... FindSolution H14.

      destruct H11;CleanContext.
      apply H in H13... apply H in H14... FindSolution H14.
      apply H in H14... apply H in H15... FindSolution H14.

      
    + (* right quantifier *)
      wellFormedQ H6; bipoleQ.
      destruct H9;CleanContext.
      apply H in H11... FindSolution H11.
      apply H in H11...

    + (* left quantifier *)
      wellFormedQ H6; bipoleQ.
      destruct H9;CleanContext.
      apply H in H11... FindSolution H11.
      apply H in H11...
    + (* init case *)
      clear H IHn H2.
      apply seqNtoSeq in H6.
      unfold RINIT in H6.
      FLLInversionAll.

      rewrite H7. decide3 (RINIT OO). tensor  [atom (up OO) ] [atom (down OO)].
      rewrite H7. decide3 (RINIT OO). tensor  (@nil oo) [atom (down OO)].
      rewrite H7. decide3 (RINIT OO). tensor  [atom (up OO) ] (@nil oo).
      rewrite H7. decide3 (RINIT OO). tensor  (@nil oo) (@nil oo) .
      
    +  (* The principal case *)
      inversion H3...
      CleanContext.
      
      FLLInversionAll;CleanContext.
      apply H in H19...
      apply H in H20...
      apply WeakTheory with (theory' := OLTheory) in H19;auto;try apply  OOTheryCut0.
      apply WeakTheory with (theory' := OLTheory) in H20;auto;try apply  OOTheryCut0.
      assert (seq OLTheory B N0 (>> (atom (down F0) ))) by solveLL.
      assert (seq OLTheory B M (>> (atom (up F0) ))) by solveLL.
      apply seqtoSeqN  in H5.
      apply seqtoSeqN  in H6.
      CleanContext.
      rewrite H11.
      apply WeakTheory with (theory := OLTheory).
      apply OOTheryCut0.

      destruct m.
      generalize(LengthFormula H7 H8);intro;lia.
      assert (seq (OLTheoryCut (pred  (S (n)))) B (M ++ N0) (> [])) .
      rewrite Permutation_app_comm.
      eapply OLCutElimStep;eauto...
      simpl in H10.
      apply seqtoSeqN  in H10. CleanContext.
      apply IHn in H10 ...
      apply WeakTheory with (theory' := OLTheory) in H10;auto;try apply  OOTheryCut0.
  Qed.
  
  (** Cut-elimination theorem for Object Logics satisfying cut-coherence *)
  Theorem OLCutElimination :
    forall n h  B N ,
      IsPositiveAtomFormulaL B ->
      IsPositiveAtomFormulaL N ->
      seqN  (OLTheoryCut n) h  B N (>[] ) ->
      seq   OLTheory B     N (>[] ) .
  Proof with CutTac.
    intros.
    apply OLCutElimAux in H1 ...
    eapply WeakTheory with (theory':= OLTheory) in H1 ...
    apply OOTheryCut0.
  Qed.
  
End CutElimination.
