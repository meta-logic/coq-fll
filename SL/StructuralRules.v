(** * Structural Rules

This file proves some structural properties as exchange (for the
classical and linear context) as well as weakening and contraction in
the classical context. *)

Require Export FLL.Misc.Utils. 
Require Export FLL.SL.Sequent.

Export ListNotations.
Export LLNotations .
Set Implicit Arguments.


Section FLLBasicTheory.
  Context `{OLS: OLSig}.
  
  Section StructuralProperties.
    Variable theory : oo -> Prop. (* Theory Definition *)
    
    Notation " n '|-F-' B ';' L ';' X " := (seqN theory n B L X)  (at level 80).
    Hint Constructors seqN : core .
    Notation " '|-f-' B ';' L ';' X " := (seq theory B L X)  (at level 80).
    Hint Constructors seq : core.

    
    (**  Exchange Rule: Classical Context *)
    Theorem exchangeCCN : forall n  CC CC' LC  (X: Arrow) ,
        Permutation CC CC' ->
        n |-F- CC ; LC ; X -> n |-F- CC' ; LC ; X.
      induction n using strongind;intros.
      + inversion H0;subst;eauto.
        apply tri_init2;eauto using Permutation_in.
      + inversion H1;subst;eauto.
        apply tri_init2;eauto using Permutation_in.
        apply tri_quest.
        eapply H with (CC' := CC' ++ [F]) (CC := CC ++ [F]);auto  using Permutation_app_tail.
        apply @tri_dec2 with (F:=F);eauto using Permutation_in.
    Qed.

    (** Exchange Rule: Linear Context *)
    Theorem exchangeLCN : forall n CC LC LC'  (X: Arrow),
        Permutation LC LC' ->
        (n |-F- CC ; LC ; X) -> n |-F- CC ; LC' ; X.
    Proof with subst;auto.
      induction n using strongind;intros.
      + inversion H0 ...
        apply Permutation_unq in H ...
        apply Permutation_nil in H ...
        apply Permutation_nil in H ...
      + inversion H1;subst;eauto.
        apply Permutation_unq in H0 ...
        apply Permutation_nil in H0 ...
        apply Permutation_nil in H0 ...
        apply @tri_tensor with (M:=M) (N:=N) (MN :=LC');
          eauto using Permutation_sym ,Permutation_trans.
        apply Permutation_nil in H0 ...
        apply tri_store ...
        eapply H;eauto using Permutation_app_tail.

        generalize (Remove_Permutation_Ex2 H4 H0);intros.
        destruct H2 as [M' [H2 H2']].
        eapply @tri_dec1 with (F:=F) (L':=M') ...
        apply H with (LC' := M') (LC:= L');auto.
        rewrite <- H2'...
    Qed.

    (**  Weakening on the classical context *)
    Theorem weakeningN : forall n CC LC  F X ,
        (n |-F- CC ; LC ; X) -> n |-F- F :: CC ; LC ; X.
      induction n using strongind;intros.
      + inversion H;subst;eauto.
        apply tri_init2. right;auto.
      + inversion H0;subst;eauto.
        apply tri_init2. right;auto.
        apply @tri_dec2 with (F:=F0);eauto. right;auto.
    Qed.
    
    Theorem weakeningGenN (CC LC : multiset oo) CC' X n:
      n |-F- CC ; LC ; X -> n |-F- CC'++ CC ; LC ; X.
      intro H.
      induction CC';simpl;auto.
      apply weakeningN;auto.
    Qed.

    

    Theorem weakeningGenN_rev (CC LC : multiset oo) CC' X n:
      n |-F- CC ; LC ; X -> n |-F- CC++ CC' ; LC ; X.
      intros.
      eapply exchangeCCN with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGenN;auto.
    Qed.

    
    (**  Weakening on the classical context *)
    Theorem weakening (CC LC : multiset oo) F X:
    |-f- CC ; LC ; X -> |-f- F :: CC ; LC ; X.
      intro H.
      induction H;eauto.
      apply tri_init2'. right;auto.
      apply @tri_dec2' with (F:=F0);eauto. right;auto.
    Qed.

    Theorem weakeningGen (CC LC : multiset oo) CC' X:
    |-f- CC ; LC ; X -> |-f- CC' ++ CC ; LC ; X.
      intro H.
      induction CC';simpl;auto.
      apply weakening;auto.
    Qed.

    (**  Exchange Rule: Classical Context *)
    Theorem exchangeCC (CC CC' LC : multiset oo) (X: Arrow):
      Permutation CC CC' ->
    |-f- CC ; LC ; X -> |-f- CC' ; LC ; X.
      intros Hp Hseq.
      generalize dependent CC'.
      induction Hseq;intros;eauto using Permutation_in.
      + apply tri_quest'.
        apply IHHseq;auto using Permutation_app_tail.
    Qed.

    (** Exchange Rule: Linear Context *)
    Theorem exchangeLC (CC LC LC' : multiset oo) (X: Arrow):
      Permutation LC LC' ->
    |-f- CC ; LC ; X -> |-f- CC ; LC' ; X.
    Proof with subst;auto.
      intros Hp Hseq.
      generalize dependent LC'.
      induction Hseq;intros;eauto.
      + apply Permutation_unq in Hp ...
      + apply Permutation_nil in Hp ...
      + apply Permutation_nil in Hp ...
      + apply @tri_tensor' with (M:=M) (N:=N) (MN :=LC');
          eauto using Permutation_sym ,Permutation_trans.
      + apply Permutation_nil in Hp ...
      + apply tri_store' ...
        apply IHHseq.
        apply Permutation_app_tail...
      + generalize (Remove_Permutation_Ex2 H0 Hp) ;intros.
        destruct H1 as [M' [H1 H1']]. 
        eapply @tri_dec1' with (F:=F) (L':=M') ...
        apply IHHseq.
        rewrite H1' ...
    Qed.

    (** Contraction on the classical context *)
    Theorem contractionN  : forall n CC LC  F X ,
        (n |-F- (F :: CC) ; LC ; X) -> In F CC -> n |-F- CC ; LC ; X.
      induction n using strongind;intros.
      + inversion H;subst;eauto.
        inversion H1;subst;auto.
      + inversion H0;subst;eauto.
        inversion H2;subst;auto.
        simpl in H3. apply H in H3;auto using in_or_app.
        inversion H4;subst.
        apply H in H5;auto.
        apply @tri_dec2 with (F:=F0);eauto.
        apply H in H5;auto.
        apply @tri_dec2 with (F:=F0);eauto.
    Qed.

    Global Instance seq_morphismN  (n:nat) :
      Proper ((@Permutation oo) ==> (@Permutation oo) ==> eq ==> iff)
             (seqN theory n).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      +  refine (exchangeCCN H _);auto.
         refine (exchangeLCN H0 _);auto.
      + apply Permutation_sym in H.
        apply Permutation_sym in H0.
        refine (exchangeCCN H _);auto.
        refine (exchangeLCN H0 _);auto.
    Qed.


    Global Instance seq_morphism  :
      Proper ((@Permutation oo) ==> (@Permutation oo) ==> eq ==> iff)
             (seq theory).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      +  refine (exchangeCC H _);auto.
         refine (exchangeLC H0 _);auto.
      + apply Permutation_sym in H.
        apply Permutation_sym in H0.
        refine (exchangeCC H _);auto.
        refine (exchangeLC H0 _);auto.
    Qed.
    
    Add Parametric Relation (L : multiset oo) (L' : multiset oo)  :
      (multiset oo ) (@Permutation oo)
        reflexivity proved by (@Permutation_refl oo)
        symmetry proved by (@Permutation_sym oo)
        transitivity proved by (@Permutation_trans oo) as eq_perm_seq.

  End StructuralProperties.

  
  (**  Weakening on the theory [theory] *)
  Section WeakeningTheory. 
    Hint Constructors seqN seq : core .
    Variable theory theory' : oo ->Prop .
    Theorem WeakTheoryN : forall n CC LC X ,
        (forall F, theory F -> theory' F) ->
        seqN theory n CC LC X -> seqN theory' n CC LC X.
      induction n using strongind;intros.
      + inversion H0;eauto.
      + inversion H1;subst;eauto.
    Qed.
    
    Theorem WeakTheory : forall CC LC X,
        (forall F, theory F -> theory' F) ->
        seq theory CC LC X -> seq theory'  CC LC X.
      intros.
      induction H0;eauto.
    Qed.

    
  End WeakeningTheory.

  Definition EmptyTheory (F :oo) := False.
  Lemma EmptySubSetN : forall (theory : oo-> Prop) CC LC X n,
      seqN EmptyTheory n CC LC X -> seqN theory n CC LC X.
    intros.
    apply WeakTheoryN with (theory:= EmptyTheory);auto.
    intros.
    inversion H0.
  Qed.
  Lemma EmptySubSet : forall (theory : oo-> Prop) CC LC X,
      seq EmptyTheory CC LC X -> seq theory CC LC X.
    intros.
    apply WeakTheory with (theory:= EmptyTheory);auto.
    intros.
    inversion H0.
  Qed.

  
  (** Admissible rules including alternative definitions for the initial rule *)
  Section AdmissibleRules.
    Variable theory : oo -> Prop. 

    Theorem InitPosNegDwN : forall Gamma A,
        seqN theory 4 Gamma   [perp A ] (DW (atom A)).
      intros.
      apply tri_rel.
      constructor.
      apply tri_store.
      intro. inversion H.
      eapply tri_dec1 with (F:= ( perp A)).
      intro;inversion H.
      constructor.
      apply tri_init1.
    Qed.
    
    Theorem InitPosNegN : forall Gamma A,
        seqN theory 2 Gamma [atom A ; perp A ] (UP []).
      intros.
      eapply tri_dec1 with (F:= (perp A )).
      intro;inversion H.
      repeat constructor.
      apply tri_init1.
    Qed.
    
    Theorem InitPosNegN' : forall Gamma A,
        seqN theory 2 Gamma [perp A ; atom A ] (UP []).
      intros.
      eapply tri_dec1 with (F:= (perp A )).
      intro;inversion H.
      repeat constructor.
      apply tri_init1.
    Qed.
    

    Theorem InitPosNegDw : forall Gamma A,
        seq theory Gamma [perp A ] (DW (atom A)).
      intros.
      apply tri_rel'.
      constructor.
      apply tri_store'.
      intro. inversion H.
      eapply tri_dec1' with (F:= (perp A)).
      intro;inversion H.
      constructor.
      apply tri_init1'.
    Qed.
    
    Theorem InitPosNeg : forall Gamma A,
        seq theory Gamma [atom A ; perp A ] (UP []).
      intros.
      eapply tri_dec1' with (F:= (perp A)).
      intro;inversion H.
      repeat constructor.
      apply tri_init1'.
    Qed.

    Theorem InitPosNeg' : forall Gamma A,
        seq theory Gamma [perp A ; atom A ] (UP []).
      intros.
      eapply tri_dec1' with (F:= (perp A)).
      intro;inversion H.
      repeat constructor.
      apply tri_init1'.
    Qed.
    
  End AdmissibleRules.

  (** Some simple invertibility lemmas *)
  Section Invertibility.
    Variable theory : oo -> Prop. (* Theory Definition *)

    Theorem FocusAtomN: forall n Gamma Delta A,
        (seqN theory n Gamma Delta (>> ((perp A ) ))) ->
        Delta = [ (atom A)] \/ (Delta = [] /\ In (atom A ) Gamma) . 
    Proof with subst;auto.
      intros.
      inversion H ...
      inversion H1.
    Qed.

    Theorem FocusAtom: forall Gamma Delta A,
        (seq theory Gamma Delta (>> ((perp A ) ))) ->
        Delta = [(atom A)]  \/ (Delta = [] /\ In (atom A) Gamma) .
    Proof with subst;auto.
      intros.
      inversion H ...
      inversion H1.
    Qed.
    
    Theorem FocusAtomTensorN: forall n Gamma Delta A F,
        (seqN theory n Gamma Delta (>> ((perp A) ** F))) ->
        In (atom A) Delta \/ In (atom A) Gamma .
    Proof with subst;auto.
      intros.
      inversion H ...
      inversion H6 ...
      left.
      rewrite H2...
      constructor ...
      inversion H8...
      inversion H1...

      inversion H1...
    Qed.
    

    Theorem FocusAtomTensor: forall Gamma Delta A F,
        (seq theory Gamma Delta (>> ((perp A) ** F))) ->
        In (atom A) Delta \/ In (atom A) Gamma .
    Proof with subst;eauto.
      intros.
      inversion H ...
      inversion H5 ...
      left.
      rewrite H2.
      constructor...
      inversion H7...
      inversion H1...
      inversion H1...
    Qed.
    
    Theorem FocusAtomTensorInvN: forall n  A F,
        (seqN theory n []  [atom A] (>> ((perp A) ** F))) ->
        (seqN theory (sub n  1 ) [] [] (>> (F))).
    Proof with subst;auto.
      intros.
      inversion H ...
      apply FocusAtomN  in H6.
      destruct H6;subst.
      apply Permutation_unq in H2;subst.
      inversion H2...
      simpl.
      rewrite Nat.sub_0_r;auto.
      inversion H0.
      inversion H3.
      inversion H1...
    Qed.

  End Invertibility.

  Section GeneralResults.
    Variable Theory : oo -> Prop. (* Theory Definition *)
    Hint Constructors seqN : core .
    Hint Constructors seq : core . 
    
    (** Measure of derivations *)
    Theorem HeightGeq : forall n Gamma Delta X,
        (seqN Theory n Gamma Delta X) ->
        forall m, m>=n -> seqN Theory m Gamma Delta X.
    Proof with eauto.
      induction n;intros ...
      + inversion H ...
      + inversion H;subst; try mgt0;intuition.
        (* tensor *)
        eapply tri_tensor;eauto;eapply IHn;try lia ...
        
        (* dec *)
        eapply @tri_dec1 with (F:=F);eauto;eapply IHn;try lia...
        eapply @tri_dec2 with (F:=F);eauto;eapply IHn;try lia...
        eapply @tri_dec3 with (F:=F);eauto;eapply IHn;try lia...
        (* exists*)
        eapply tri_ex;eauto;eapply IHn;try lia...
    Qed.

    (** HeightGeq with Exchange Linear Context *)
    Theorem HeightGeqEx : forall n CC LC LC' X, 
        Permutation LC LC' ->
        (seqN Theory n  CC LC' X) ->
        forall m, m>=n -> (seqN Theory m  CC LC X).
    Proof with eauto.
      intros.
      eapply HeightGeq with (n:=n);auto.
      symmetry in H.
      eapply exchangeLCN;eauto.
    Qed.
  End GeneralResults.

  (** Adequacy relating the system with and without inductive meassures *)
  Section Adequacy.
    (* Relating the system with and without measures *)
    Variable theory : oo -> Prop. (* Theory Definition *)
    Hint Constructors seqN : core .
    Hint Constructors seq : core. 
    

    Theorem seqNtoSeq : forall n Gamma Delta X ,  (seqN theory n Gamma Delta X) -> seq theory  Gamma Delta X.
      induction n using strongind;intros;eauto.
      + inversion H;subst;eauto.
      + inversion H0;subst;eauto.
    Qed.

    Axiom seqtoSeqN : forall Gamma Delta X ,
        (seq theory  Gamma Delta X) ->  exists n, (seqN theory n Gamma Delta X).

    Theorem contraction  : forall CC LC  F X ,
        ( seq theory   (F :: CC) LC X) -> In F CC -> (seq theory CC LC  X).
      intros.
      apply seqtoSeqN in H.
      destruct H.
      apply contractionN in H;auto.
      eapply seqNtoSeq;eauto.
    Qed.
    
    Theorem contractionSet  : forall CC LC X L, (forall F, In F L -> In F CC) ->
        ( seq theory (L ++ CC) LC X) -> (seq theory CC LC  X).
      intros.
      induction L.
      simpl in H0;auto.
      apply IHL;intros.
      apply H. firstorder.
      eapply exchangeCC with (CC':=a :: (L ++ CC)) in H0;[|auto].
      apply seqtoSeqN in H0 .
      destruct H0.
      apply contractionN in H0;auto.
      eapply seqNtoSeq;eauto.
      apply in_or_app.
      firstorder.
    Qed.  
    
  End Adequacy.


  (** Weakening in the linear context when the formula belongs to the theory *)
  Section MoreWeakening.
    Variable theory : oo -> Prop .
    Hint Constructors seq : core .
    Hint Constructors seqN : core .
    Hint Constructors IsPositiveAtom : core .
    
    Theorem WeakLinearTheoryN : forall n CC LC F X ,
        ~ IsPositiveAtom F ->
        (seqN theory n CC (F::LC) X) -> theory F ->
        seqN theory n CC LC X.

    Proof with auto.
      induction n;intros;subst.
      + inversion H0;subst...
        contradict H ...
      + inversion H0;subst;eauto.
        contradict H ...
        assert(In F (M++N)).
        apply Permutation_in with (l:= F::LC)...
        constructor ...

        (* Tensor: 2 cases, F is in N or in M *)
        apply in_app_or in H2.
        destruct H2.
        ++
          apply in_split in H2;
            destruct H2 as [l1 H2];
            destruct H2 as [l2 H2];subst.
          rewrite Permutation_midle in H4.
          apply IHn in H4 ...

          rewrite Permutation_midle in H3.
          simpl in H3.
          apply Permutation_cons_inv in H3.
          rewrite H3.
          eapply tri_tensor;eauto.
        ++
          apply in_split in H2;
            destruct H2 as [l1 H2];
            destruct H2 as [l2 H2];subst.
          rewrite Permutation_midle in H5.
          apply IHn in H5 ...
          rewrite app_assoc in H3.
          rewrite Permutation_midle in H3.
          apply Permutation_cons_inv in H3.
          rewrite H3.
          rewrite <- app_assoc.
          eapply tri_tensor;eauto.
        ++ inversion H4;subst. (* F = F0 or F in LC *)
           eapply @tri_dec3 with (F:=F) ...

           apply IHn in H5  ...
           eapply @tri_dec1 with (F:=F0);eauto.
    Qed.
    
    Theorem WeakLinearTheory : forall CC LC F X,
        ~ IsPositiveAtom F ->
        (seq theory CC (F::LC) X) -> theory F -> seq theory CC LC X.
      intros.
      apply seqtoSeqN in H0.
      destruct H0.
      apply WeakLinearTheoryN in H0;auto.
      apply seqNtoSeq in H0;auto.
    Qed.
  End MoreWeakening.
End FLLBasicTheory.
