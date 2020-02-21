(** Invertibility lemmas: Positive phase

This file proves some invertibility lemmas showing that positive rules
can be switched.
 *)

Require Export FLL.Misc.Hybrid.
Require Export FLL.SL.FLLTactics.
Require Import Lia.
Require Import FLL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Export FLL.SL.InvNegativePhase.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Section InvPosPhase.
  Context `{OLS: OLSig}.

  Variable theory : oo -> Prop .
  Notation " n '|---' B ';' L ';' X " := (seqN theory n B L X) (at level 80).
  Notation " '|--' B ';' L ';' X " := (seq theory B L X) (at level 80).

  Generalizable All Variables.
  Global Instance Forall_morph : 
    Proper ((@Permutation oo) ==> Basics.impl) (isNotAsyncL).
  Proof.
    unfold Proper; unfold respectful; unfold Basics.impl;intros.
    eapply Forall_Permute;eauto.
  Qed. 

  Ltac solveList :=
    match goal with
      [ H : [] = ?M ++ [?F] |- _ ] =>
      symmetry in H; apply app_eq_nil in H;inversion H as [H' H''];inversion H''
    | [ H :  ?M ++ [?F] = [ ] |- _ ] =>
      apply app_eq_nil in H; inversion H as [H' H''];inversion H''
    end.

  Ltac seqPermutation := 
    match goal with
      [ H : Permutation ?M ?T ,
            Hs : |-- ?B ; ?M ; ?Arrow |- _ ] =>
      assert(|-- B ; T ; Arrow) by (refine(exchangeLC _ Hs); rewrite H; auto)
    | [ H : Permutation ?T ?M ,
            Hs : |-- ?B ; ?M ; ?Arrow |- _ ] =>
      assert(|-- B ; T ; Arrow) by (refine(exchangeLC _ Hs); rewrite <- H; auto)  
    end.

  Ltac seqPerm H S := 
    match type of H with
      Permutation ?M ?T => match type of S with
                             |-- ?B ; ?M ; ?Arrow => 
                             assert(|-- B ; T ; Arrow); refine(exchangeLC _ S);rewrite H;auto
                           | ?n |--- ?B ; ?M ; ?Arrow => 
                             assert(n |--- B ; T ; Arrow); refine(exchangeLCN _ S);rewrite H;auto
                           end
    | Permutation ?T ?M => match type of S with
                             |-- ?B ; ?M ; ?Arrow => 
                             assert(|-- B ; T ; Arrow); refine(exchangeLC _ S);rewrite H;auto
                           | ?n |--- ?B ; ?M ; ?Arrow => 
                             assert(n |--- B ; T ; Arrow); refine(exchangeLCN _ S);rewrite H;auto
                           end                      
    end.   

  Section AbsorptionTheory.

    Theorem AbsorptionAtom :  forall n B M A X , theory (perp A) -> n |--- B; (perp A) ::  M; X -> n |--- B; M; X.
    Proof with solveF.
      induction n;intros ;inversion H0;subst;eauto;clear H0...
      + (* tensor: A+ is in N or in M0 *)
        assert (In (perp A)  ( M0 ++ N)).
        apply Permutation_in with (l:= (perp A) :: M)...
        apply in_app_or in H0;destruct H0.
        ++ (* A+  in H0 *)
          apply InPermutation in H0;destruct H0.
          rewrite H0 in H3.
          apply IHn in H3...
          rewrite H0 in H2;simpl in H2.
          apply Permutation_cons_inv in H2.
          rewrite H2.
          tensor.
        ++ (* A+ in N *)
          apply InPermutation in H0;destruct H0.
          rewrite H0 in H4.
          apply IHn in H4...
          rewrite H0 in H2;simpl in H2.
          apply Permutation_cons_app_inv in H2.
          rewrite H2.
          tensor.
      + (*dec1 *)
        inversion H3;subst;eauto.
    Qed.
    

    Definition RUpTheory (n:nat) := forall B L  F  M , 
        isNotAsyncL M -> theory F -> ~ IsPositiveAtom F -> ~ IsNegativeAtom F ->
        n |--- B ;M ; UP (L ++ [F])  -> |-- B ; M ; UP (L ).

    Definition RDownTheory (n:nat) := forall B  F  M  H, 
        isNotAsyncL M -> ~ asynchronous F ->  ~ IsPositiveAtom F -> ~ IsNegativeAtom F -> theory F -> 
        n |--- B ; M ++ [F]  ; DW H -> |-- B ; M  ; DW H.

    Definition RIndTheory (n:nat) := RUpTheory n /\ RDownTheory (n -1). 

    Lemma RDownTheory0 : RDownTheory 0.
    Proof with subst;auto.
      unfold RDownTheory;intros.
      inversion H5;subst;[|solveList|solveList ]. 
      symmetry in H9.
      apply app_eq_unit in H9.
      destruct H9...
      inversion H.
      inversion H7...
      assert(IsPositiveAtom (atom A)) by constructor.
      contradiction.

      inversion H...
      inversion H7.
    Qed.

    Lemma RUpTheory0 : RUpTheory 0.
    Proof with subst;auto.
      unfold RUpTheory;intros.
      destruct L.
      + inversion H3...
        eapply tri_dec3' with (F:= Top) ...
        solveLL'.
      + inversion H3 ...
        eapply tri_top'.
    Qed.

    (* =============================================== *)
    (* PROOF OF RUpTheory *)
    (* =============================================== *)   

    Theorem InvTheoryUP: forall  n ,
        (forall m : nat, m <= n -> RIndTheory m) -> RUpTheory (S n).
    Proof with subst;auto;solveF.
      intros n IH.
      unfold RUpTheory; intros B L1 F M1 FB FNA HnP HnN HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1... 
        ++
          eapply tri_dec3' with (F:=top)...
          solveLL'.       
        ++ 
          apply seqNtoSeq in H3;auto. 
        ++ 
          eapply tri_dec3' with (F:=F0 $ G) ...
          eapply tri_rel' ...  solveLL'. 
          apply seqNtoSeq in H3;auto. 
        ++ 
          eapply tri_dec3' with (F:=F0 & G) ...
          eapply tri_rel' ...  solveLL'. 
          apply seqNtoSeq in H4;auto.
          apply seqNtoSeq in H5;auto. 
        ++ 
          eapply tri_dec3' with (F:=? F0) ...
          eapply tri_rel' ...  solveLL'.
          apply seqNtoSeq in H3;auto. 
        ++ 
          assert(RIndTheory n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        *
          eapply Remove_Permutation_Ex2 with (M:=[F] ++ M1) in H0;[|perm].
          do 2 destruct H0.
          inversion H0;subst.
          **
            eapply tri_dec3' with (F0:= F);auto.
            apply seqNtoSeq in H1;auto.
            rewrite H2;auto.
          **   
            eapply tri_dec1' with (F1:= F0) (L'0:=l2);auto.
            eapply HDown with (F:= F);auto.
            apply Remove_Permute in H9;auto.
            rewrite H9 in FB.
            change (F0 :: l2) with ([F0] ++ l2) in FB.
            eapply ForallAppInv2 in FB...
            simpl; rewrite Nat.sub_0_r.
            eapply exchangeLCN with (LC:=F :: l2);auto.
            perm.
            rewrite H2;auto. 
        *
          eapply tri_dec2' with (F1:=F0) ...
          eapply HDown with (F:= F);auto.
          simpl; rewrite Nat.sub_0_r;auto.
        *
          eapply tri_dec3' with (F1:=F0) ...
          eapply HDown with (F:= F);auto.
          simpl; rewrite Nat.sub_0_r;auto.
          ++ 
            eapply tri_dec3' with (F:=F{ FX}) ...
            eapply tri_rel' ...
            eapply tri_fx' ...
            intro.
            generalize (H5 x);intros.
            apply H in H0.
            apply seqNtoSeq in H0;auto. 
      + (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RIndTheory n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ...
        ++
          solveLL'.
        ++
          solveLL';
            eapply HUp with (F:=F);auto. 
        ++
          solveLL';
            eapply HUp with (F:=F);auto. 
        ++
          solveLL';
            eapply HUp with (F:=F);auto. 
        ++ 
          solveLL';
            eapply HUp with (F:=F);auto.
        ++ 
          eapply tri_store';auto.
          eapply HUp with (F:=F);auto.
          apply ForallApp...
        ++ 
          eapply tri_fx';auto; intros.
          generalize (H5 x H);intros.

          eapply HUp with (F:=F);auto. 
    Qed.

    (* =============================================== *)
    (* PROOF OF RDownTheory *)
    (* =============================================== *)   

    Theorem InvTheoryDW: forall  n ,
        (forall m : nat, m <= n -> RIndTheory m) -> RDownTheory (n).
    Proof with subst;auto;solveF.
      intros n IH.
      unfold RDownTheory.  intros B F M H  HM1pos HPosF  HB HnP HnN HD1.
      inversion HD1;subst ... 
      + 
        symmetry in H3.
        apply app_eq_unit in H3.
        inversion H3...
      +
        solveList. 
      + 
        solveList.
      +
        apply PProp_perm_sel in H1.
        destruct H1.
        ++
          do 2 destruct H.
          assert(HRI: RIndTheory (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          simpl in HDown.
          rewrite Nat.sub_0_r in HDown.

          assert(n0 |--- B; (x ++ [F]); (>> F0)).
          seqPerm H H2. 

          apply HDown in H1 ...

          eapply tri_tensor' with (N0:=N) (M1:=x) ...
          rewrite H0;auto.
          apply seqNtoSeq in H6;auto.
          rewrite <- H0 in HM1pos.
          apply ForallAppInv1 in HM1pos...
        ++
          do 2 destruct H.
          assert(HRI: RIndTheory (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          simpl in HDown.
          rewrite Nat.sub_0_r in HDown.
          assert(n0 |--- B; (x ++ [F]); (>> G)).
          seqPerm H H6. 

          apply HDown in H1 ...

          eapply tri_tensor' with (N0:=x) (M1:=M0) ...
          rewrite H0;auto.
          apply seqNtoSeq in H2;auto.
          rewrite <- H0 in HM1pos.
          apply ForallAppInv2 in HM1pos...
      +
        assert(HRI: RIndTheory (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        simpl in HDown.
        rewrite Nat.sub_0_r in HDown.
        apply HDown in H4 ...
        apply tri_plus1';auto.
      + 
        assert(HRI: RIndTheory (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        simpl in HDown.
        rewrite Nat.sub_0_r in HDown.
        apply HDown in H4 ...
        apply tri_plus2';auto.
      +
        solveList. 
      +
        eapply UpExtension in H5.
        destruct H5.
        destruct H0. 
        assert(HRI: RIndTheory x)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        apply HUp in H2 ...
        eapply tri_rel'...
        apply ForallApp...
      +
        assert(HRI: RIndTheory (S n0)) by ( apply IH;auto).
        destruct HRI as [HUp  HDown] ...
        simpl in HDown;
          rewrite Nat.sub_0_r in HDown.
        apply HDown in H6 ...
        eapply tri_ex'  with (t0:=t) ...
    Qed.

    Theorem InvAuxTheory : forall n, RIndTheory n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RIndTheory.
        split; [apply RUpTheory0 | apply RDownTheory0].
      + unfold RIndTheory in *.
        split;[|simpl; rewrite Nat.sub_0_r].
        apply InvTheoryUP; assumption.
        apply InvTheoryDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem AbsorptionTheory : forall B L F  M,   
        theory F -> ~ IsPositiveAtom F -> ~ IsNegativeAtom F ->  isNotAsyncL M -> isFormulaL (F::L) -> 
        |-- B ; M ; UP (F :: L) -> |-- B; M  ; UP L .
    Proof.
      intros.
      assert(|-- B; M; (> L ++ [F])).
      eapply EquivUpArrow2. 
      apply ForallApp; inversion H3;subst;auto.
      exact H4. perm.

      assert(HRn:  forall n, RUpTheory n) by (apply InvAuxTheory).
      apply seqtoSeqN in H5;auto. 
      destruct H5.
      generalize (HRn x);intros.
      eapply H6;eauto.
    Qed.

  End AbsorptionTheory.


  Section AbsorptionClassic.

    Definition RUp (n:nat) := forall B L  F  M , 
      isNotAsyncL M -> In F B ->
      n |--- B ;M ; UP (L ++ [F])  -> |-- B ; M ; UP (L ).  

    Definition RDown (n:nat) := forall B  F  M  H, 
        isNotAsyncL M -> ~ asynchronous F ->
        In F B -> n |--- B ; M ++ [F]  ; DW H -> |-- B ; M  ; DW H.

    Definition RInd (n:nat) := RUp n /\ RDown (n -1). 

    Lemma RDown0 : RDown 0.
    Proof with subst;auto.
      unfold RDown;intros.
      inversion H3;subst;[|solveList|solveList].
      symmetry in H7.
      apply app_eq_unit in H7.
      destruct H7.
      inversion H...
      inversion H5...
      eapply tri_init2'... 
      inversion H...
      inversion H5.
    Qed.

    Lemma RUp0 : RUp 0.
    Proof with subst;auto.
      unfold RUp;intros.
      destruct L.
      + inversion H1...
        eapply tri_dec2' with (F:= Top) ...
        intro. inversion H2.
        apply tri_rel'. constructor.
        apply seqNtoSeq in H1...
      + inversion H1 ...
        eapply tri_top'.
    Qed.

    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   

    Theorem InvCopyUP: forall  n ,
        (forall m : nat, m <= n -> RInd m) -> RUp (S n).
    Proof with subst;auto;solveF.
      intros n IH.
      unfold RUp; intros B L1 F M1 FB FNA HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1... 
        ++
          eapply tri_dec2' with (F:=top)...
          solveLL'.       
        ++ 
          apply seqNtoSeq in H3;auto. 
        ++
          eapply tri_dec2' with (F:=F0 $ G) ...
          eapply tri_rel' ...  solveLL'. 
          apply seqNtoSeq in H3;auto. 
        ++ 
          eapply tri_dec2' with (F:=F0 & G) ...
          eapply tri_rel' ...  solveLL'. 
          apply seqNtoSeq in H4;auto.
          apply seqNtoSeq in H5;auto. 
        ++ 
          eapply tri_dec2' with (F:=? F0) ...
          eapply tri_rel' ...  solveLL'.
          apply seqNtoSeq in H3;auto. 
        ++ 
          assert(RInd n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        * 
          eapply Remove_Permutation_Ex2 with (M:=[F] ++ M1) in H0;[|perm].
          do 2 destruct H0.
          inversion H0;subst.
          **
            eapply tri_dec2' with (F0:= F);auto.
            apply seqNtoSeq in H1;auto.
            rewrite H2;auto.
          **   
            eapply tri_dec1' with (F1:= F0) (L'0:=l2);auto.
            eapply HDown with (F:= F);auto.
            apply Remove_Permute in H9;auto.
            change (F0 :: l2) with ([F0] ++ l2) in H9.
            rewrite H9 in FB.       
            apply ForallAppInv2 in FB...
            simpl; rewrite Nat.sub_0_r.
            eapply exchangeLCN with (LC:=F :: l2);auto.
            perm.
            seqPerm H2 H1...
        * 
          eapply tri_dec2' with (F1:=F0) ...
          eapply HDown with (F:= F);auto.
          simpl; rewrite Nat.sub_0_r;auto.
        *
          eapply tri_dec3' with (F1:=F0) ...
          eapply HDown with (F:= F);auto.
          simpl; rewrite Nat.sub_0_r;auto.
          ++ 
            eapply tri_dec2' with (F:=F{ FX}) ...
            eapply tri_rel' ...
            eapply tri_fx' ...
            intro.
            generalize (H5 x);intro.
            intro. apply H in H0.
            apply seqNtoSeq in H0;auto. 
      + (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RInd n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ...
        ++
          solveLL'.
        ++
          solveLL';
            eapply HUp with (F:=F);auto. 
        ++
          solveLL';
            eapply HUp with (F:=F);auto. 
        ++ 
          solveLL';
            eapply HUp with (F:=F);auto. 
        ++ 
          solveLL';
            eapply HUp with (F:=F);auto.
          intuition.   
        ++ 
          eapply tri_store';auto.
          eapply HUp with (F:=F);auto.
          apply ForallApp...
        ++ 
          eapply tri_fx';auto. intros.
          generalize (H5 x H);intros.
          eapply HUp with (F:=F);auto. 
    Qed.

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   

    Theorem InvCopyDW: forall  n ,
        (forall m : nat, m <= n -> RInd m) -> RDown (n).
    Proof with subst;auto;solveF.
      intros n IH.
      unfold RDown.  intros B F M H  HM1pos HPosF  HB HD1.
      inversion HD1;subst ... 
      +
        symmetry in H3.
        apply app_eq_unit in H3.
        inversion H3...
        eapply tri_init2' ...
      +
        solveList.
      +
        solveList.
      + 
        apply PProp_perm_sel in H1.
        destruct H1.
        ++ 
          do 2 destruct H.
          assert(HRI: RInd (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          simpl in HDown;
            rewrite Nat.sub_0_r in HDown.
          assert(n0 |--- B; (x ++ [F]); (>> F0)).
          seqPerm H H2.

          apply HDown in H1 ...

          eapply tri_tensor' with (N0:=N) (M1:=x) ...
          rewrite H0;auto.
          apply seqNtoSeq in H6;auto.
          rewrite <- H0 in HM1pos.       
          apply ForallAppInv1 in HM1pos...
        ++
          do 2 destruct H.
          assert(HRI: RInd (S n0)) by (apply IH;auto).
          destruct HRI as [HUp  HDown] ...
          simpl in HDown.
          rewrite Nat.sub_0_r in HDown.
          assert(n0 |--- B; (x ++ [F]); (>> G)).
          seqPerm H H6.

          apply HDown in H1 ...

          eapply tri_tensor' with (N0:=x) (M1:=M0) ...
          rewrite H0;auto.
          apply seqNtoSeq in H2;auto.
          rewrite <- H0 in HM1pos.       
          apply ForallAppInv2 in HM1pos...
      + 
        assert(HRI: RInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        simpl in HDown.
        rewrite Nat.sub_0_r in HDown.
        apply HDown in H4 ...
        apply tri_plus1';auto.
      +
        assert(HRI: RInd (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        simpl in HDown.
        rewrite Nat.sub_0_r in HDown.
        apply HDown in H4 ...
        apply tri_plus2';auto.
      +
        solveList. 
      +
        eapply UpExtension in H5.
        destruct H5.
        destruct H0. 
        assert(HRI: RInd x)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...

        apply HUp in H2 ...

        eapply tri_rel'...
        apply ForallApp... 
      +
        assert(HRI: RInd (S n0)) by ( apply IH;auto).
        destruct HRI as [HUp  HDown] ...
        simpl in HDown.
        rewrite Nat.sub_0_r in HDown.
        apply HDown in H6 ...
        eapply tri_ex'  with (t0:=t) ...
    Qed.


    Theorem InvAux : forall n, RInd n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RInd.
        split; [apply RUp0 | apply RDown0].
      + unfold RInd in *.
        split;[|simpl;  rewrite Nat.sub_0_r].
        apply InvCopyUP; assumption.
        apply InvCopyDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem AbsorptionClassic : forall B L F  M,
        In F B -> isNotAsyncL M -> isFormulaL (F::L) ->
        (|-- B ; M ; UP (F :: L)) ->
        |-- B; M  ; UP L .
    Proof.
      intros.
      assert(|-- B; M; (> L ++ [F])).
      eapply EquivUpArrow2. 
      apply ForallApp; inversion H1;subst;auto.
      exact H2. perm.

      assert(HRn:  forall n, RUp n) by (apply InvAux).
      apply seqtoSeqN in H3;auto. 
      destruct H3.
      generalize (HRn x);intros. eapply H4;eauto.
    Qed.

  End AbsorptionClassic. 

  Section InvExists.


    (* uniform_oo FX ->
proper t -> *)

    Definition RUpExists (n:nat) := forall B L M FX t, 
      isNotAsyncL M -> uniform_oo FX -> proper t -> 
      n |--- B ;M ; UP (L ++ [FX t])  -> |-- B ; M ++ [E{ FX}] ; UP L.

    Definition RDownExists (n:nat) := forall B M H FX t, 
        isNotAsyncL M -> positiveFormula (FX t) -> uniform_oo FX -> proper t ->
        n |--- B ; M ++ [FX t]  ; DW H -> |-- B ; M ++ [E{ FX}]  ; DW H.


    Definition RIndExists (n:nat) := RUpExists n /\ RDownExists (n -1). 

    Lemma RDownE0 : RDownExists 0.
    Proof with subst;auto;solveF.
      unfold RDownExists.
      intros.
      inversion H4;subst;[|solveList|solveList]...
      symmetry in H8.
      apply app_eq_unit in H8.
      inversion H8...
      rewrite H6 in H1.
      inversion H1. 
    Qed.

    Lemma Remove_app_in' :
      forall (F:oo) (L: list oo), remove F (L ++ [F]) (L).
      intros.
      assert(remove (F) (L ++ [F]) (L++[])).
      eapply Remove_app_in with (F:=F) (L1:=L) (L2:=nil).
      rewrite app_nil_r in H.
      assumption.
    Qed.



    Lemma RUpE0 : RUpExists 0.
    Proof with subst;auto;solveF.
      unfold RUpExists.
      intros.
      destruct L.
      + inversion H2...
        eapply tri_dec1' with (F:= E{ FX}) (L':=M) ...
        2:{
          eapply tri_ex';eauto. 
          rewrite <- H7 in *.
          apply tri_rel' ...

          solveLL'. }
        apply Remove_app_in'.
      + inversion H2 ...
        solveLL'.
    Qed.

    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   
    Theorem InvExUP: forall  n , (forall m : nat, m <= n -> RIndExists m) -> RUpExists (S n).
    Proof with subst;auto;solveF.
      intros n IH.
      unfold RUpExists.  intros B L1  M1 FX t HM1pos Habs Hprop HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1... 
        ++
          eapply tri_dec1' with (F:=E{ FX}) (L':=M1)...
          apply Remove_app_in'.
          eapply tri_ex'...  
          exact Hprop. 
          rewrite <- H3. 
          solveLL'.
        ++ 
          eapply tri_dec1' with (F:=E{ FX}) (L':=M1)...
          apply Remove_app_in'.
          eapply tri_ex'...  
          exact Hprop. 
          rewrite <- H0. 
          solveLL'.
          apply seqNtoSeq in H3;auto. 
        ++ 
          eapply tri_dec1' with (F0:=E{ FX}) (L':=M1)...
          apply Remove_app_in'.
          eapply tri_ex'...  
          exact Hprop. 
          rewrite <- H0. 
          solveLL'.
          apply seqNtoSeq in H3;auto. 
        ++ 
          eapply tri_dec1' with (F0:=E{ FX}) (L':=M1)...
          apply Remove_app_in'.
          eapply tri_ex'...  
          exact Hprop. 
          rewrite <- H0. 
          solveLL'.
          apply seqNtoSeq in H4;auto.
          apply seqNtoSeq in H5;auto. 
        ++ 
          eapply tri_dec1' with (F0:=E{ FX}) (L':=M1)...
          apply Remove_app_in'.
          eapply tri_ex'...  
          exact Hprop. 
          rewrite <- H0. 
          solveLL'.
          apply seqNtoSeq in H3;auto.
        ++ 
          assert(RIndExists n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        * 
          eapply Remove_Permutation_Ex2 with (M:=[FX t] ++ M1) in H0;[|perm].
          do 2 destruct H0.

          inversion H0;subst.
          eapply tri_dec1' with (F:=E{ FX}) (L'0:=x)...
          apply Remove_app_in'.

          eapply tri_ex'...  
          exact Hprop.
          apply seqNtoSeq in H1;auto.
          rewrite H2;auto. 

          destruct (NotAsynchronousPosAtoms H4).
          2:{
            eapply tri_dec1' with (F0:= E{ FX}) (L'0:=M1)... 
            apply Remove_app_in'.
            eapply tri_ex' with (t0:=t)...
            eapply tri_rel' ...
            inversion H3...
            eapply tri_store' ... 

            eapply tri_dec1' with (F0:= F)(L'0:=l2++[FX t])...
            apply Remove_app_tail;auto.  
            assert(Permutation (l2 ++ [FX t]) L')by (rewrite <- H2;perm).
            assert( n0 |--- B; l2 ++ [FX t]; (>> F)).
            seqPerm H6 H1. 
            apply seqNtoSeq in H7;auto.
          }
          simpl in HDown; rewrite Nat.sub_0_r in HDown.
          assert(Permutation (l2 ++ [FX t]) L') by (rewrite <- H2;perm).
          assert( n0 |--- B; l2 ++ [FX t]; (>> F)).
          seqPerm H6 H1.

          apply HDown in H7...
          eapply tri_dec1' with (F0:=F)(L'0:=l2++[E{ FX}]) ...
          apply Remove_app_tail;auto.

          apply Remove_Permute in H9;auto.
          rewrite H9 in HM1pos.
          inversion HM1pos...
        *
          destruct (NotAsynchronousPosAtoms H4).
          2:{
            eapply tri_dec1' with (F0:= E{ FX}) (L':=M1)... 
            apply Remove_app_in'.
            eapply tri_ex' with (t0:=t)...
            eapply tri_rel' ...
            inversion H2...
            eapply tri_store' ...
            eapply tri_dec2' with (F0:=F)... 
            apply seqNtoSeq in H1;auto. 
          }
          simpl in HDown; rewrite Nat.sub_0_r in HDown.
          apply HDown in H1 ...
          eapply tri_dec2' with (F0:=F)... 
        *
          destruct (NotAsynchronousPosAtoms H4).
          2:{
            eapply tri_dec1' with (F0:= E{ FX}) (L':=M1)... 
            apply Remove_app_in'.
            eapply tri_ex' with (t0:=t)...
            eapply tri_rel' ...
            inversion H2...
            eapply tri_store' ...
            eapply tri_dec3' with (F0:=F)... 
            apply seqNtoSeq in H1;auto. 
          }
          simpl in HDown; rewrite Nat.sub_0_r in HDown.
          apply HDown in H1 ...
          eapply tri_dec3' with (F0:=F)... 
          ++ 
            eapply tri_dec1' with (F:=E{ FX})(L':=M1)... 
            apply Remove_app_in'.
            eapply tri_ex' with (t0:=t) ...
            rewrite <- H0.
            eapply tri_rel' ...
            solveLL'.
            generalize(H5 x properX);intro.
            apply seqNtoSeq in H;auto.
      +
        (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RIndExists n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ...
        ++
          solveLL'.
        ++
          solveLL';
            eapply HUp;eauto. 
        ++
          solveLL';
            eapply HUp;eauto. 
        ++ 
          solveLL';
            eapply HUp;eauto. 
        ++ 
          solveLL';
            eapply HUp;eauto.
        ++ 
          eapply tri_store';auto.
          assert(|-- B; (M1 ++ [o]) ++ [E{ FX}]; (> L1)).
          eapply HUp;eauto.
          apply ForallApp...

          eapply exchangeLC.
          2:{ exact H. } perm.
        ++
          eapply tri_fx';auto. intros.
          generalize (H5 x H);intros.
          eapply HUp with (t:=t);simpl;eauto.
    Qed.


    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   
    Theorem InvExDW: forall  n , (forall m : nat, m <= n -> RIndExists m) -> RDownExists (n).
    Proof with subst;auto;solveF.
      intros n IH.
      unfold RDownExists.  intros B M  H  FX t HPosF HM1pos Habs Hprop  HD1.
      destruct H; inversion HD1;subst ...
      +
        apply UpExtension in H4 ...
        destruct H4.
        destruct H. 
        assert(HRI: RIndExists x)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown]. clear HDown.
        apply HUp in H1 ...
        eapply tri_rel'...
        apply PosConc... 
      +
        symmetry in H2. 
        apply app_eq_unit in H2.
        inversion H2... clear H2.
        rewrite H1 in HM1pos.
        inversion HM1pos.
      +
        solveList. 
      +
        solveLL'.
      +
        solveList.
      +
        inversion H0.
      +
        apply UpExtension in H4 ...
        destruct H4 as [m H4]. destruct H4 as [H4 H4'].
        assert(HRI: RIndExists m)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        apply HUp in H4' ...
        solveLL'.
        apply PosConc... 
      + 
        apply UpExtension in H6 ...
        destruct H6 as [m H6]. destruct H6 as [H6 H6'].
        assert(HRI: RIndExists m)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        apply HUp in H6' ...
        solveLL'.
        apply PosConc... 
      +
        apply PProp_perm_sel in H3. 
        destruct H3.
        ++ 
          inversion H1...
          assert(n0 |--- B; (x ++ [FX t]); (>> H)).
          seqPerm H2 H7.
          assert(HRI: RIndExists (S n0)).
          auto using le_n_S.
          destruct HRI as [HUp  HDown] ...
          simpl in HDown; rewrite Nat.sub_0_r in HDown.
          apply HDown in H4 ...

          eapply tri_tensor' with (N0:=N) (M1:=x ++ [E{ FX}]) ...
          rewrite <- H3; perm.
          apply seqNtoSeq in H8;auto.
          symmetry in H3.
          rewrite H3 in HPosF.
          apply ForallAppInv1 in HPosF... 
        ++ 
          inversion H1...
          assert(n0 |--- B; (x ++ [FX t]); (>> H0)).
          seqPerm H2 H8.
          assert(HRI: RIndExists (S n0)).
          auto using le_n_S.
          destruct HRI as [HUp  HDown] ...
          simpl in HDown; rewrite Nat.sub_0_r in HDown.
          apply HDown in H4 ...

          eapply tri_tensor' with (N0:=x ++ [E{ FX}]) (M1:=M0) ...
          rewrite <- H3; perm.
          apply seqNtoSeq in H7;auto.
          rewrite <- H3 in HPosF.
          apply ForallAppInv2 in HPosF... 
      + 
        assert(HRI: RIndExists (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        simpl in HDown; rewrite Nat.sub_0_r in HDown.
        apply HDown in H5 ...
        eapply tri_plus1';auto.
      + 
        assert(HRI: RIndExists (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        simpl in HDown; rewrite Nat.sub_0_r in HDown.
        apply HDown in H5 ...
        eapply tri_plus2';auto.
      + 
        apply UpExtension in H6 ...
        destruct H6 as [m H6]. destruct H6 as [H6 H6'].
        assert(HRI: RIndExists m)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        apply HUp in H6' ... solveLL'.
        apply PosConc...
      +
        solveList.
      + 
        apply UpExtension in H5 ...
        destruct H5 as [m H5]. destruct H5 as [H5 H5'].
        assert(HRI: RIndExists m)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        apply HUp in H5' ...
        solveLL'.
        apply PosConc...
      + 
        apply UpExtension in H4 ...
        destruct H4 as [m H4]. destruct H4 as [H4 H4'].
        assert(HRI: RIndExists m)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        apply HUp in H4' ...
        solveLL'.
        apply PosConc...
      +         
        assert(HRI: RIndExists (S n0)) by ( apply IH;auto).
        destruct HRI as [HUp  HDown] ...
        simpl in HDown; rewrite Nat.sub_0_r in HDown.
        apply HDown in H5 ...
        apply tri_ex' with (t1:=t0) ...
    Qed.

    Theorem InvExAux : forall n, RIndExists n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RIndExists.
        split; [apply RUpE0 | apply RDownE0].
      + unfold RIndExists in *.
        split;[|simpl;  rewrite Nat.sub_0_r].
        apply InvExUP; assumption.
        apply InvExDW; assumption.
    Qed.


    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   

    Theorem InvEx : forall B L FX t  M, 
        uniform_oo FX -> proper t -> isFormulaL (FX t :: L) -> 
        |-- B  ;M ; UP (FX t :: L) -> isNotAsyncL M  -> |-- B ; M ++ [E{ FX}]  ; UP L .
    Proof.
      intros.
      apply EquivUpArrow2 with (L' := L ++ [FX t]) in H2 ;eauto.
      assert(HRn:  forall n, RUpExists n) by (apply InvExAux).
      apply seqtoSeqN in H2.
      destruct H2.
      generalize (HRn x);intros.
      apply H4 in H2;auto.
      inversion H1;subst.
      apply ForallApp;auto.
      perm.
    Qed.

  End InvExists.

  Section InvOPlus.

    Definition RUpPlus (n:nat) := forall B L M F G, 
      isNotAsyncL M -> 
      n |--- B ;M ; UP (L ++ [F])  -> |-- B ; M ++ [F op G] ; UP L.

    Definition RDownPlus (n:nat) := forall B M H F G, 
        isNotAsyncL M -> positiveFormula F ->
        n |--- B ; M ++ [F]  ; DW H -> |-- B ; M ++ [F op G]  ; DW H.

    Definition RIndPlus (n:nat) := RUpPlus n /\ RDownPlus (n -1). 

    Lemma RDownP0 : RDownPlus 0.
    Proof with subst;auto;solveF.
      unfold RDownPlus.
      intros.
      inversion H2;subst;[|solveList|solveList] ...
      symmetry in H6.
      apply app_eq_unit in H6.
      inversion H6...
      inversion H1.
    Qed.

    Lemma RUpP0 : RUpPlus 0.
    Proof with subst;auto;solveF.
      unfold RUpPlus.
      intros.
      destruct L.
      + inversion H0;subst.
        eapply tri_dec1' with (F:= top op G) (L':=M)...
        apply Remove_app_in'.
        apply tri_plus1'.
        solveLL'.
      + inversion H0 ...
        solveLL'.
    Qed.

    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)   

    Theorem InvPlusUP: forall  n , (forall m : nat, m <= n -> RIndPlus m) -> RUpPlus (S n).
    Proof with subst;auto;solveF.
      intros n IH.
      unfold RUpPlus.  intros B L1  M1 F  G HM1pos HD1.
      destruct L1;simpl in *.
      + (* L1 is Empty *)
        inversion HD1;subst ...
        ++
          eapply tri_dec1' with (F:= top op G) (L':=M1)...
          apply Remove_app_in'.
          eapply tri_plus1' ...
          solveLL'.
        ++ 
          eapply tri_dec1' with (F:= bot op G) (L':=M1)...
          apply Remove_app_in'.
          eapply tri_plus1' ...
          solveLL'.
          apply seqNtoSeq in H3;auto.
        ++
          eapply tri_dec1' with (F:= (F0 $ G0) op G) (L':=M1)...
          apply Remove_app_in'.
          eapply tri_plus1' ...
          solveLL'.
          apply seqNtoSeq in H3;auto.
        ++ 
          eapply tri_dec1' with (F:= (F0 & G0) op G) (L':=M1)...
          apply Remove_app_in'.
          eapply tri_plus1' ...
          solveLL'.
          apply seqNtoSeq in H4;auto.
          apply seqNtoSeq in H5;auto.
        ++ 
          eapply tri_dec1' with (F:= (? F0) op G) (L':=M1)...
          apply Remove_app_in'.
          eapply tri_plus1' ...
          solveLL'.
          apply seqNtoSeq in H3;auto.
        ++ 
          assert(RIndPlus n) by ( apply IH;auto).
          destruct H as [HUp  HDown].
          inversion H5;subst ...
        *  
          eapply Remove_Permutation_Ex2 with (M:=[F] ++ M1) in H0;[|perm].
          inversion H0...
          inversion H2...

          eapply tri_dec1' with (F0:= F op G) (L'0:=x)...
          apply Remove_app_in'.
          eapply tri_plus1' ...
          rewrite H3.
          apply seqNtoSeq in H1;auto.

          destruct (NotAsynchronousPosAtoms H4).
          2:{
            eapply tri_dec1' with (F1:= F op G) (L'0:=M1)...
            apply Remove_app_in'.
            eapply tri_plus1' ...
            eapply tri_rel' ... inversion H6... 
            eapply tri_store' ...
            eapply tri_dec1' with (F1:= F0)  (L'0:= l2 ++ [F])...
            apply Remove_app_tail;auto.
            eapply seqNtoSeq in H1.
            eapply exchangeLC with (LC:=L')...
            rewrite <- H3;perm. 
          }
          simpl in HDown; rewrite Nat.sub_0_r in HDown.
          assert (Permutation (l2++[F]) L').
          rewrite <- H3;perm.
          assert(n0 |--- B; (l2 ++ [F]); (>> F0)).
          seqPerm H7 H1.
          eapply HDown in H8...
          eapply tri_dec1' with (F1:=F0)(L'0:= l2 ++ [F op G])...
          apply Remove_app_tail;auto.
          exact H8.
          apply Remove_Permute in H10;auto.

          change (F0::l2) with ([F0]++l2) in H10.
          rewrite H10 in HM1pos.
          apply ForallAppInv2 in HM1pos...   
        * 
          destruct (NotAsynchronousPosAtoms H4).
          2:{
            eapply tri_dec1' with (F1:= F op G) (L':=M1)... 
            apply Remove_app_in'.
            eapply tri_plus1'... 
            eapply tri_rel' ...
            inversion H2...

            eapply tri_store' ...
            eapply tri_dec2' with (F1:=F0)... 
            apply seqNtoSeq in H1;auto. 
          }
          simpl in HDown; rewrite Nat.sub_0_r in HDown.
          eapply HDown in H1 ...
          eapply tri_dec2' with (F1:=F0)...
          exact H1. 
        * 
          destruct (NotAsynchronousPosAtoms H4).
          2:{
            eapply tri_dec1' with (F1:= F op G) (L':=M1)... 
            apply Remove_app_in'.
            eapply tri_plus1'... 
            eapply tri_rel' ...
            inversion H2...

            eapply tri_store' ...
            eapply tri_dec3' with (F1:=F0)... 
            apply seqNtoSeq in H1;auto. 
          }
          simpl in HDown; rewrite Nat.sub_0_r in HDown.
          eapply HDown in H1 ...
          eapply tri_dec3' with (F1:=F0)...
          exact H1. 
          ++
            eapply tri_dec1' with (F:=F{ FX} op G) (L':=M1)...
            apply Remove_app_in'.
            eapply tri_plus1'...
            eapply tri_rel' ...
            solveLL'. 
            generalize (H5 x properX);intro.
            apply seqNtoSeq in H;auto.
      + (* L is not empty *)
        inversion HD1;subst; try(
                                 assert(RIndPlus n) by ( apply IH;auto);
                                 destruct H as [HUp  HDown]; clear HDown) ...
        ++ 
          solveLL'.
        ++ 
          solveLL'.
          eapply HUp in H3... exact H3.
        ++ 
          solveLL'.
          change (F0 :: G0 :: L1 ++ [F]) with ((F0 :: G0 :: L1) ++ [F]) in H3.
          eapply HUp in H3... exact H3.
        ++ 
          solveLL'.
          change (F0 :: L1 ++ [F]) with ((F0 :: L1) ++ [F]) in H4.
          eapply HUp in H4... exact H4.
          change (G0 :: L1 ++ [F]) with ((G0 :: L1) ++ [F]) in H5.
          eapply HUp in H5... exact H5.
        ++
          solveLL'.
          change (?F0 :: L1 ++ [F]) with ((?F0 :: L1) ++ [F]) in H3.
          eapply HUp in H3... exact H3.
        ++ 
          eapply HUp in H5... 
          eapply tri_store'...
          eapply exchangeLC with (LC:=(M1 ++ [o]) ++ [F op G]).
          perm. exact H5.
          apply LexpPosConc...
        ++  
          eapply tri_fx'... intros.
          generalize (H5 x H);intro.
          change (FX x :: L1 ++ [F]) with ((FX x :: L1) ++ [F]) in H0.
          eapply HUp in H0 ...
          exact H0.
    Qed.    

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)   
    Theorem InvPlusDW: forall  n , (forall m : nat, m <= n -> RIndPlus m) -> RDownPlus (n).
    Proof with subst;auto;solveF.
      intros n IH.
      unfold RDownPlus.  intros B M  H  F G HPosF HM1pos  HD1.
      destruct H;subst; inversion HD1;subst ...
      + 
        apply UpExtension in H4 ...
        destruct H4.
        destruct H. 
        assert(HRI: RIndPlus x)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown]. clear HDown.
        eapply HUp in H1 ...
        eapply tri_rel' ...
        eassumption.
        apply PosConc...
      + 
        symmetry in H2.
        apply app_eq_unit in H2.
        inversion H2...
        inversion HM1pos.
      + solveList.
      + solveLL'.
      + solveList.      
      + 
        apply UpExtension in H4 ...
        destruct H4 as [m H4]. destruct H4 as [H4 H4'].
        assert(HRI: RIndPlus m)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        eapply HUp in H4' ...
        eapply tri_rel' ...
        exact H4'.
        apply PosConc...
      +  
        apply UpExtension in H4 ...
        destruct H4 as [m H4]. destruct H4 as [H4 H4'].
        assert(HRI: RIndPlus m)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        eapply HUp in H4' ...
        eapply tri_rel' ...
        exact H4'.
        apply PosConc...
      +
        apply UpExtension in H6...
        destruct H6 as [m H6]. destruct H6 as [H6 H6'].
        assert(HRI: RIndPlus m)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        eapply HUp in H6' ...
        eapply tri_rel' ...
        exact H6'.
        apply PosConc...
      +
        eapply Remove_Permutation_Ex2 with (F:=F) (L':= M) in H3.
        2:{ apply Remove_app_in'. }
        inversion_clear H3...

        apply Remove_Permute in H1;auto.
        apply PProp_perm_select' in H1.
        do 3 destruct H1.
        ++ 
          assert(HRI: RIndPlus (S n0)) by( apply IH; auto using le_n_S). 
          destruct HRI as [HUp  HDown] ...
          simpl in HDown; rewrite Nat.sub_0_r in HDown.
          assert (Permutation M0 ( x0 ++ [F])).
          rewrite H1. perm.
          assert(n0 |--- B; (x0 ++ [F]); (>> H)).
          seqPerm H4 H7.
          eapply HDown in H5 ...
          eapply tri_tensor' with (N0:=N) (M1:=x0 ++ [F op G]) ...
          rewrite <- H2. rewrite <- H3. perm.
          exact H5.
          apply seqNtoSeq in H8;auto.
          rewrite H2 in H3.
          rewrite <- H3 in HPosF.
          apply ForallAppInv1 in HPosF...
        ++ 
          assert(HRI: RIndPlus (S n0)) by( apply IH; auto using le_n_S). 
          destruct HRI as [HUp  HDown] ...
          simpl in HDown; rewrite Nat.sub_0_r in HDown.
          assert (Permutation N ( x0 ++ [F])).
          rewrite H1. perm.
          assert(n0 |--- B; (x0 ++ [F]); (>> H0)).

          seqPerm H4 H8.
          eapply HDown in H5 ...
          eapply tri_tensor' with (N0:=x0 ++ [F op G]) (M1:=M0) ...
          rewrite <- H2. rewrite <- H3. perm.

          apply seqNtoSeq in H7;auto.
          exact H5.
          rewrite H2 in H3.
          rewrite <- H3 in HPosF.
          apply ForallAppInv2 in HPosF...
      +
        assert(HRI: RIndPlus (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        simpl in HDown; rewrite Nat.sub_0_r in HDown.
        eapply HDown in H5...
        apply tri_plus1'. exact H5.
      +  
        assert(HRI: RIndPlus (S n0)) by (apply IH ; auto).
        destruct HRI as [HUp  HDown] ...
        simpl in HDown; rewrite Nat.sub_0_r in HDown.
        eapply HDown in H5...
        apply tri_plus2'. exact H5.
      +
        apply UpExtension in H6...
        destruct H6 as [m H6]. destruct H6 as [H6 H6'].
        assert(HRI: RIndPlus m)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        eapply HUp in H6' ...
        eapply tri_rel' ...
        exact H6'.
        apply PosConc...
      + solveList.
      +  
        apply UpExtension in H5 ...
        destruct H5 as [m H5]. destruct H5 as [H5 H5'].
        assert(HRI: RIndPlus m)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        eapply HUp in H5' ...
        eapply tri_rel' ...
        exact H5'.
        apply PosConc...
      +
        apply UpExtension in H4 ...
        destruct H4 as [m H4]. destruct H4 as [H4 H4'].
        assert(HRI: RIndPlus m)  by (apply IH ;auto).
        destruct HRI as [HUp  HDown] ...
        eapply HUp in H4' ...
        eapply tri_rel' ...
        exact H4'.
        apply PosConc...
      + 
        assert(HRI: RIndPlus (S n0)) by ( apply IH;auto).
        destruct HRI as [HUp  HDown] ...
        apply tri_ex' with (t0:=t)...
        simpl in HDown; rewrite Nat.sub_0_r in HDown.
        eapply HDown in H5...
        exact H5. 
    Qed.


    Theorem InvPlusAux : forall n, RIndPlus n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RIndPlus.
        split; [apply RUpP0 | apply RDownP0].
      + unfold RIndPlus in *.
        split.
        apply InvPlusUP; assumption.
        simpl;  rewrite Nat.sub_0_r.
        apply InvPlusDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)   
    Theorem InvPlus : forall B L F G  M,   isFormulaL (F :: L) -> |-- B  ;M ; UP (F :: L) -> isNotAsyncL M  -> |-- B ; M ++ [F op G]  ; UP L .
    Proof.
      intros.
      apply EquivUpArrow2 with (L' := L ++ [F]) in H0 ;eauto.
      assert(HRn:  forall n, RUpPlus n) by (apply InvPlusAux).
      apply seqtoSeqN in H0.
      destruct H0.
      generalize (HRn x);intros.
      eapply H2 in H0;eauto.
      inversion H;subst.
      apply ForallApp;auto.
      perm.
    Qed.


    Lemma OPlusComm : forall B M F G X n, n |--- B ; M ++ [F op G] ; X -> n |--- B ; M ++ [G op F] ; X.
    Proof with subst;auto;solveF.
      intros.
      generalize dependent B.
      generalize dependent M.
      generalize dependent X.
      generalize dependent n.
      induction n using strongind;intros.
      + 
        inversion H...
        symmetry in H3.
        apply app_eq_unit in H3...
        inversion H3...
        solveList.
        solveList.
      + 
        inversion H0;subst ...
        symmetry in H4.
        apply app_eq_unit in H4...
        inversion H4...
        solveList.
        solveList.
        ++ 
          eapply Remove_Permutation_Ex2 with (F:=F op G) (L':= M) in H2.
          2:{ apply Remove_app_in'. }
          inversion_clear H2...

          apply Remove_Permute in H1;auto.
          apply PProp_perm_select' in H1.
          do 3 destruct H1.

          assert(Permutation (F op G :: x0) (x0 ++ [F op G])).
          perm.
          rewrite H6 in H1. rewrite H1 in H3.
          eapply H in H3.
          eapply tri_tensor with (N0:=N) (M1:=x0 ++ [G op F])...
          rewrite <- H2. rewrite <- H5. perm.
          auto.

          assert(Permutation (F op G :: x0) (x0 ++ [F op G])).
          perm.
          rewrite H6 in H1. rewrite H1 in H4.
          eapply H in H4.
          eapply tri_tensor with (N0:=x0 ++ [G op F]) (M1:=M0)...
          rewrite <- H2. rewrite <- H5. perm.
          auto.
        ++ 
          symmetry in H2.
          apply app_eq_nil in H2...
        ++ 
          assert (n |--- B; (M ++ [F0]) ++ [F op G]; (> M0)).
          eapply exchangeLCN.
          2:{ exact H3. }
          perm.

          apply tri_store ...
          eapply H in H1...
          eapply exchangeLCN.
          2:{ exact H1. }
          perm.
        ++ 
          eapply Remove_Permutation_Ex2 with (M:=[F op G] ++ M) in H3;[|perm].

          inversion H3...
          inversion H1...

          eapply tri_dec1 with (F0:= G op F) (L'0:=x)...

          apply Remove_app_in'.
          rewrite H5.
          inversion H4...

          eapply tri_dec1 with (F1:= F0) (L'0:=l2++[G op F])...
          apply Remove_app_tail;auto.
          assert(Permutation (F op G :: l2) (l2++[F op G])).
          perm.
          rewrite <- H5 in H4.
          rewrite H6 in H4.
          apply H in H4...
        ++ 
          Hypothesis ProgIsFormula: forall P, theory P -> isFormula P.
          eapply tri_dec2 with (F1:=F0) ...
        ++ 
          eapply tri_dec3 with (F1:=F0) ...  
        ++ 
          eapply tri_ex with (t0:=t) ...
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM (FLIPPING F and G    *)
    (* =============================================== *)   
    Theorem InvPlusComm: forall B L F G  M,  isFormulaL (G :: L) -> |-- B  ;M ; UP (G :: L) -> isNotAsyncL M  -> |-- B ; M ++ [F op G]  ; UP L .
    Proof.
      intros.
      apply InvPlus with (G:=F)in H0;auto.
      apply seqtoSeqN in H0.
      destruct H0.
      apply OPlusComm in H0.
      apply seqNtoSeq with (n:=x) in H0;auto.
    Qed.

  End InvOPlus.

  (* =============================================== *)
  (** Invertibility of Tensor *)
  (* =============================================== *)   
  Section InvTensor.

    Definition RUpTensor (nm:nat) := forall B L M L' M' F G n m, 
      nm = n + m -> isNotAsyncL M -> isNotAsyncL M' ->  isFormulaL L' -> isFormulaL L ->
      isFormulaL B -> isFormulaL M -> isFormulaL M' -> isFormula (F ** G) ->
      n |--- B ;M ; UP (L ++ [F])  -> m |--- B ;M' ; UP (L' ++ [G])  -> 
                                                     |-- B ; M ++ M' ++  [F ** G] ; UP (L ++ L').

    Definition RDownTensor (nm:nat) := forall B M M' H F G n m, 
        nm = n + m -> isNotAsyncL M -> isNotAsyncL M' -> positiveFormula F -> 
        isFormulaL B -> isFormulaL M -> isFormulaL M' -> isFormula H -> isFormula (F ** G) -> 
        n |--- B ; M ++ [F]  ; DW H -> m |--- B ; M' ; UP [G] -> |-- B ; M ++ M' ++  [F ** G]  ; DW H.


    Definition RIndTensor (n:nat) := RUpTensor n /\ RDownTensor (n -1). 

    Lemma RDownT0 : RDownTensor 0.
    Proof with subst;auto;solveF.
      unfold RDownTensor;intros.

      symmetry in H0. 
      apply plus_is_O in H0.
      destruct H0;subst.

      inversion H9;subst;[|solveList|solveList].
      symmetry in H13.
      apply app_eq_unit in H13.
      inversion H13...
      inversion H3.
    Qed.

    Lemma RUpT0 : RUpTensor 0.
    Proof with subst;auto;solveF.
      unfold RUpTensor;intros.
      symmetry in H. apply plus_is_O in H.
      destruct H;subst.
      inversion H8;subst ...
      destruct L;destruct L';simpl in *.
      +
        inversion H13...
        inversion H9...
        apply seqNtoSeq in H8.
        apply seqNtoSeq in H9.
        assert(|-- B; (M ++ M') ++ [top ** top]; (> [])).
        eapply tri_dec1' with (F:= top ** top) (L':=M++M')... 
        apply Remove_app_in'.
        eapply tri_tensor' with (N:=M) (M0:=M') ...

        solveLL'.
        solveLL'.
        refine(exchangeLC _ H);perm. 
      + 
        inversion H13;subst ... inversion H9;subst ...
        solveLL'.
      + 
        inversion H13 ...
        solveLL'.
      + 
        inversion H13 ...
        solveLL'.
    Qed.

    (* =============================================== *)
    (* F ** G COMMUTES *)
    (* =============================================== *)
    Lemma TensorComm : forall B M F G X n, n |--- B ; M ++ [F ** G] ; X -> n |--- B ; M ++ [G ** F] ; X.
    Proof with subst;auto;solveF.
      intros.
      generalize dependent B.
      generalize dependent M.
      generalize dependent X.
      generalize dependent n.
      induction n using strongind;intros.
      + 
        inversion H...
        symmetry in H3.
        apply app_eq_unit in H3.
        inversion H3...
        solveList.
        solveList.
      + 
        inversion H0;subst ...
        symmetry in H4.
        apply app_eq_unit in H4.
        inversion H4...
        solveList.
        solveList.
        ++ 
          apply PProp_perm_sel in H2.
          destruct H2.
        *
          inversion H1...
          rewrite H2 in H3.
          apply H in H3...
          eapply tri_tensor.
          2:{ exact H3. }
          2:{ exact H4. }
          rewrite <- H5. perm.
        *
          inversion H1...
          rewrite H2 in H4.
          apply H in H4...
          eapply tri_tensor.
          2:{ exact H3. }
          2:{ exact H4. }
          rewrite <- H5. perm.
          ++ 
            solveList.
          ++ 
            assert(n |--- B; (M ++ [F0]) ++ [F ** G]; (> M0)).
            eapply exchangeLCN.
            2:{ exact H3. } perm.
            apply H in H1...

            apply tri_store ...
            eapply exchangeLCN.
            2:{ exact H1. } perm.
          ++ 
            eapply Remove_Permutation_Ex2 with (M:=[F ** G] ++ M) in H3;[|perm].
            destruct H3.
            destruct H1.

            inversion H1...
            2:{
              eapply tri_dec1 with (F1:= F0) (L'0:=l2 ++ [G ** F] )...
              apply Remove_app_tail;auto.
              apply H...
              eapply exchangeLCN.
              2:{ exact H4. }
              rewrite <- H3. perm. }

            inversion H4 ...

            eapply tri_dec1 with (F0:= G ** F) (L'0:=x)...
            apply Remove_app_in'.
            eapply tri_tensor.
            2:{ exact H12. }
            2:{ exact H11. }
            rewrite H3. rewrite H7. perm.
          ++  
            eapply tri_dec2 with (F1:=F0) ...
          ++  
            eapply tri_dec3 with (F1:=F0) ...
          ++ 
            eapply tri_ex with (t0:=t) ...
    Qed.


    Lemma TensorComm' : forall B M F G X , |-- B ; M ++ [F ** G] ; X -> |-- B ; M ++ [G ** F] ; X.
    Proof.
      intros.
      apply seqtoSeqN in H.
      destruct H.
      apply TensorComm in H.
      eapply seqNtoSeq in H;eauto.
    Qed.


    (* =============================================== *)
    (* PROOF OF RUP *)
    (* Cases when one of the lists is not empty *)
    (* =============================================== *)
    Lemma InvTensorConsNil (nm : nat) (IH : forall m : nat, m <= nm -> RIndTensor m) (B L1 M1 : list oo)
          (l : oo) (L2  M2 : list oo) (F  G : oo) (n'  m' : nat) : S nm = n' + m' -> 
                                                                   isNotAsyncL M1 -> isNotAsyncL M2 -> 
                                                                   isFormulaL B -> isFormulaL M1 -> isFormulaL M2 -> isFormula (F ** G) ->
                                                                   isFormula l -> isFormulaL L1 -> isFormulaL L2 ->  
                                                                   n' |--- B; M1; UP (L1 ++ [F]) -> m' |--- B; M2; UP (l :: L2 ++ [G]) -> |-- B; M1 ++ M2 ++ [F ** G]; UP (L1 ++ l :: L2).
    Proof with subst;auto;solveF.
      intros HNM  HM1pos HM2pos isFB isFM1 isFM2 isFT isFl isL1 isL2  HD1 HD2.
      apply EquivUpArrow2 with (L':= L1 ++ l :: L2) (L := l:: L2 ++ L1);eauto ...
      apply ForallApp;auto.

      inversion HD2...
      +
        solveLL'.
      +
        simpl. apply tri_bot'.
        apply EquivUpArrow2 with (L:= L1 ++ L2) (L' := L2 ++ L1);eauto ...
        apply ForallApp;auto.
        assert(HUp : RUpTensor(n' + n)) by (apply IH;omega) ...
        eapply HUp with(n0:=n') (m:=n) ...
      +
        simpl. apply tri_par'.
        apply EquivUpArrow2 with (L:= L1 ++ F0 :: G0 :: L2) (L' := F0 :: G0 :: L2 ++ L1);eauto ...
        inversion isFl...
        change  (F0 :: G0 :: L2 ++ L1) with  ((F0 :: G0 :: L2) ++ L1).
        apply ForallApp;auto.
        assert(HUp : RUpTensor(n' + n)) by (apply IH;omega) ...
        eapply HUp with(n0:=n') (m:=n) ...
        inversion isFl...
      +
        simpl. apply tri_with'.
        apply EquivUpArrow2 with (L:= L1 ++ F0 :: L2) (L' := F0 :: L2 ++ L1);eauto ...

        inversion isFl...
        change  (F0 :: L2 ++ L1) with  ((F0 :: L2) ++ L1).
        apply ForallApp;auto.

        assert(HUp : RUpTensor(n' + n)) by (apply IH;omega) ...
        eapply HUp with(n0:=n') (m:=n) ...

        inversion isFl...

        apply EquivUpArrow2 with (L:= L1 ++ G0 :: L2) (L' := G0 :: L2 ++ L1);eauto ...
        inversion isFl...

        change  (G0 :: L2 ++ L1) with  ((G0 :: L2) ++ L1).
        apply ForallApp;auto.


        assert(HUp : RUpTensor(n' + n)) by (apply IH;omega) ...
        eapply HUp with(n0:=n') (m:=n) ...
        inversion isFl...
      +
        simpl. apply tri_quest'.
        apply EquivUpArrow2 with (L:= L1 ++ L2) (L' := L2 ++ L1);eauto ...

        apply ForallApp;auto.

        assert(HUp : RUpTensor(n' + n)) by (apply IH;omega) ...
        eapply HUp with(n0:=n') (m:=n) ...
        inversion isFl...
        apply ForallApp;auto.

        eapply weakeningGenN_rev;auto.
      +
        simpl. apply tri_store'...
        apply EquivUpArrow2 with (L:= L1 ++ L2) (L' := L2 ++ L1);eauto ...

        apply ForallApp;auto.

        assert(HUp : RUpTensor(n' + n)) by (apply IH;omega). 
        assert(|-- B; M1 ++ (M2 ++ [l]) ++ [F ** G]; (> L1 ++ L2)).
        eapply HUp with(n0:=n') (m:=n) ...

        apply ForallApp...
        apply ForallApp...
        refine(exchangeLC _ H);perm.
      +
        simpl. apply tri_fx'...
        intros.
        generalize (H5 x H);intro.
        assert(HUp : RUpTensor(n' + n)) by (apply IH;omega).

        apply EquivUpArrow2 with (L:= L1 ++ FX x ::L2) (L' := FX x :: L2 ++ L1);eauto ...

        inversion isFl...

        change  (FX x :: L2 ++ L1) with  ((FX x :: L2) ++ L1).
        apply ForallApp;auto.
        eapply HUp with(n0:=n') (m:=n) ...
        inversion isFl...
    Qed.

    (* ================================================ *)
    (* PROOF OF RUP *)
    (* Case when the 2 formulas are async. or pos. atoms*)
    (* ================================================ *)

    Lemma ITCaseAsyncAsync:
      forall n m B M1 M2 F G, (asynchronous F \/  IsPositiveAtom F) -> (asynchronous G \/ IsPositiveAtom G) -> 
                              (n |--- B; M1; UP [F]) -> (m |--- B; M2; UP [G]) -> |-- B; M1 ++ M2 ++ [F ** G]; UP [].
    Proof with subst;auto;solveF.
      intros.
      assert(|-- B; (M1 ++ M2) ++ [F ** G]; (> [])).
      eapply tri_dec1' with (F0:= F ** G) (L':=M1++M2)...
      apply Remove_app_in'.
      eapply tri_tensor' with (N:=M2) (M:=M1)...

      eapply tri_rel'... 
      apply AsIsPosRelease;auto.
      apply seqNtoSeq in H1;auto.

      eapply tri_rel'... 
      apply AsIsPosRelease;auto.
      apply seqNtoSeq in H2;auto.

      eapply exchangeLC.
      2:{ exact H3. }
      perm.
    Qed.

    (** We assume that the theory produces only well-formed LL formulas *)
    Hypothesis TheoryIsFormula: forall P, theory P -> isFormula P.

    Lemma ITAsyncSync  :
      forall nm n m  B M1 M2 F G,
        (asynchronous F \/ IsPositiveAtom F) ->  ~ asynchronous G -> 
        (forall m : nat, m <= nm -> RIndTensor m) -> nm = n + m ->  isNotAsyncL M1 -> isNotAsyncL M2 -> 
        isFormulaL B -> isFormulaL M1 -> isFormulaL M2 -> isFormula (F ** G) -> 
        n |--- B; M1; UP [F] ->  m |--- B; M2 ++ [G]; UP [] ->  |-- B; M1 ++ M2 ++ [F ** G]; UP [].
    Proof with subst;auto;solveF.
      intros nm n m  B M1 M2 F G AF AG IH Hnm HM1 HM2 isFB isFM1 isFM2 isFMT HD1 HD2.
      apply NotAsynchronousPosAtoms' in AG; destruct AG as [AG | AG].
      +
        (* G is a positive atom... then, release works (Lemma  ITCaseAsyncAsync) *)
        eapply ITCaseAsyncAsync;eauto. 
        apply tri_store;auto using IsPositiveAtomNotAssync... 
        eauto.
      +
        (* G cannot do release *)
        inversion HD2;subst.
        ++ 
          apply Remove_Permute in H0;auto.
          apply PProp_perm_select' in H0.
          do 2 destruct H0.
        *
          inversion H0...
          rewrite <- H4 in H1.
          rewrite H0.
          assert(|-- B; (M1 ++ (F0 :: x)) ++ [F ** G]; (> [])).
          eapply tri_dec1' with (F1:= F0) (L'0:=(M1 ++ x) ++ [F ** G])...
          eapply Remove_app_tail.
          apply Remove_app_in.

          assert(IH2 : RIndTensor(n + S n0)) by(  apply IH;auto); destruct IH2 as [HUp HDw].
          assert(Hn : n + S n0 -1 = n + n0) by omega;rewrite Hn in HDw;clear Hn.
          assert(|-- B;x ++ M1 ++ [G ** F]; (>> F0)).
          eapply HDw with (m:= n) (n1:= n0);try(omega)...
          change  (F0 :: x) with  ([F0]++x) in H0. 
          rewrite H0 in HM2.
          apply ForallAppInv2 in HM2...

          change  (F0 :: x) with  ([F0]++x) in H0. 
          rewrite H0 in isFM2.
          apply ForallAppInv2 in isFM2...

          rewrite H0 in isFM2.
          inversion isFM2...
          rewrite H0 in isFM2.
          inversion isFM2...
          inversion isFMT...
          apply TensorComm'.
          refine(exchangeLC _ H5);perm.
          refine(exchangeLC _ H5);perm.
        *
          destruct H0...
          change (F0 :: x) with ([F0] ++ x) in H0.
          apply app_eq_unit in H0.
          inversion H0...
          clear H0.

          assert(|-- B; (M1 ++ M2) ++ [F ** G]; (> [])).
          eapply tri_dec1' with (F0:= F ** G) (L'0:=M1++M2)...
          apply Remove_app_in'.
          eapply tri_tensor' with (N:=M2) (M:=M1) ...
          apply tri_rel';auto using AsyncRelease, AsIsPosRelease ...

          apply seqNtoSeq in HD1;assumption.
          rewrite app_nil_r in H2.
          rewrite <- H2 in H1.
          apply seqNtoSeq in H1;assumption.
          refine(exchangeLC _ H0);perm.
          ++ 
            assert(IH2 : RIndTensor(n + S n0)) by(  apply IH;auto);
              destruct IH2 as [HUp HDw].
            assert(Hn : n + S n0 -1 = n + n0) by omega;rewrite Hn in HDw;clear Hn.
            eapply tri_dec2' with (F1:=F0) ...
            assert(|-- B; M2 ++ M1 ++ [G ** F]; (>> F0)).
            eapply HDw with (m:= n) (n1:= n0);try(omega)...

            apply isFormulaIn in H0...
            inversion isFMT...
            assert(|-- B; (M1 ++ M2) ++ [F ** G]; (>> F0)).
            apply TensorComm'.
            refine(exchangeLC _ H2);perm.
            refine(exchangeLC _ H3);perm.
          ++ 
            assert(IH2 : RIndTensor(n + S n0)) by(  apply IH;auto);
              destruct IH2 as [HUp HDw].
            assert(Hn : n + S n0 -1 = n + n0) by omega;rewrite Hn in HDw;clear Hn.
            eapply tri_dec3' with (F1:=F0) ...
            assert(|-- B; M2 ++ M1 ++ [G ** F]; (>> F0)).
            eapply HDw with (m:= n) (n1:= n0);try(omega)...
            inversion isFMT...
            assert(|-- B; (M1 ++ M2) ++ [F ** G]; (>> F0)).
            apply TensorComm'.
            refine(exchangeLC _ H2);perm.
            refine(exchangeLC _ H3);perm.
    Qed.


    (* =============================================== *)
    (* PROOF OF RUP *)
    (* Case when both formulas are not Async *)
    (* =============================================== *)
    Lemma ITSyncSync : forall nm n m  B M1 M2 F G, ~ asynchronous F -> ~ asynchronous G ->  
                                                   (forall m : nat, m <= nm -> RIndTensor m) -> S nm = S n + S m -> 
                                                   isNotAsyncL M1 -> isNotAsyncL M2 -> 
                                                   isFormulaL B -> isFormulaL M1 -> isFormulaL M2 -> isFormula (F ** G) -> 
                                                   S n |--- B; M1 ; UP [F] -> S m |--- B; M2 ; UP [G] ->  |-- B; M1 ++ M2 ++ [F ** G]; UP [].
    Proof with subst;auto;solveF.
      intros nm n m  B M1 M2 F G AF AG IH Hnm HM1 HM2 isFB isFM1 isFM2 isFT HD1 HD2.
      apply NotAsynchronousPosAtoms' in AF; destruct AF as [AF | AF];
        apply NotAsynchronousPosAtoms' in AG; destruct AG as [AG | AG].
      + (* Both are positive *)
        eapply ITCaseAsyncAsync;eauto.
      + (* F is a positive atom *)
        assert(~asynchronous G).
        intro.
        inversion H;subst;inversion AG...
        assert(~asynchronous F) by auto using IsPositiveAtomNotAssync.
        inversion HD2;subst ...
        eapply ITAsyncSync with (nm:=nm) (n:= S n) (m:= m) ;eauto. omega.
      + (* G is a positive atom *)
        assert(~asynchronous G) by auto using IsPositiveAtomNotAssync.
        assert(~asynchronous F).
        intro.
        inversion H0;subst;inversion AF...
        inversion HD1;subst ...
        assert(|-- B; M2 ++ M1 ++ [G ** F]; (> [])).
        eapply ITAsyncSync with (nm:=nm) (n:= S m) (m:= n) ;eauto. omega.
        inversion isFT...
        assert(|-- B; (M1 ++ M2) ++ [F ** G]; (> [])).
        apply TensorComm'.
        refine (exchangeLC _ H1);perm.
        refine (exchangeLC _ H2);perm.
      +  (* F nor G can do release *)
        assert(~asynchronous G).
        intro.
        inversion H;subst;inversion AG...
        assert(~asynchronous F).
        intro.
        inversion H0;subst;inversion AF...
        inversion HD1;subst ...
        inversion HD2;subst ...

        inversion H7;subst;inversion H9;subst ...
        ++ (* DEC1 DEC1 *)
          apply Remove_Permute in H2;auto.
          apply PProp_perm_select' in H2.
          apply Remove_Permute in H5;auto.
          apply PProp_perm_select' in H5.

          do 3 destruct H2.
          do 3 destruct H5.

          assert(remove F1 (F1 :: x0) x0)...
          eapply Remove_Permutation_Ex2 with (M:=M2) in H13.
          do 2 destruct H13.

          assert (IH' : RIndTensor (S n + S (S n0))) by ( apply IH; omega).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n + S (S n0) - 1 = n + S (S n0)) by omega;rewrite Hn in HDw;clear Hn.
          eapply tri_dec1' with (F2:= F1) (L'1:= M1 ++ x1 ++ [F ** G])...
          do  2 rewrite app_assoc.
          apply Remove_app_tail.
          apply Remove_app_head...

          assert(|-- B; x1 ++ M1 ++ [G ** F]; (>> F1)).
          eapply  HDw with (n1:= n) (m:= S ( S n0))... 

          apply Remove_Permute in H13;auto.
          rewrite H13 in HM2.
          inversion HM2...
          apply Remove_Permute in H13;auto.
          rewrite H13 in isFM2.
          inversion isFM2...

          rewrite H5 in isFM2.
          inversion isFM2...
          rewrite H5 in isFM2.
          inversion isFM2...
          inversion isFT...
          rewrite <- H14 in H12.
          rewrite <- H12 in H10;auto.

          assert(|-- B; (x1 ++ M1) ++ [F ** G]; (>> F1)).
          apply TensorComm'.

          refine (exchangeLC _ H15);perm.
          refine (exchangeLC _ H16);perm.
          rewrite H5;perm.
          apply Permutation_unq in H5.
          change (F1 :: x0) with ([F1] ++ x0) in H5.
          apply app_eq_unit in H5.
          inversion H5...
          clear H5.

          assert(remove F0 (F0 :: x) x)...
          eapply Remove_Permutation_Ex2 with (M:=M1) in H5.
          do 2 destruct H5.

          eapply tri_dec1' with (F1:= F0) (L'1:=x0 ++ M2 ++ [F ** G])...
          do  2 rewrite app_assoc.
          apply Remove_app_tail.
          apply Remove_app_tail...

          assert (IH' : RIndTensor (S n0 + S (S n))) by ( apply IH; omega).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n0 + S (S n) - 1 = n0 + S (S n)) by omega;rewrite Hn in HDw;clear Hn.
          eapply  HDw with (n1:= n0) (m:= S ( S n))...
          apply Remove_Permute in H5;auto.
          rewrite H5 in HM1.
          inversion HM1...

          apply Remove_Permute in H5;auto.
          rewrite H5 in isFM1.
          inversion isFM1...
          rewrite H2 in isFM1.
          inversion isFM1...
          rewrite H2 in isFM1.
          inversion isFM1...
          rewrite <- H13 in H11.
          rewrite <- H11 in H3;auto.
          apply Permutation_sym;auto.

          do 3 destruct H5.
          apply Permutation_unq in H2.
          change (F0 :: x) with ([F0] ++ x) in H2.
          apply app_eq_unit in H2.
          inversion H2...
          clear H2.

          assert(remove F1 (F1 :: x0) x0)...
          eapply Remove_Permutation_Ex2 with (M:=M2) in H2.
          do 2 destruct H2...

          assert(|-- B; M2 ++ M1 ++ [G ** F]; (> [])).
          eapply tri_dec1' with (F0:= F1) (L'1:=x ++ M1 ++ [G ** F])...
          do  2 rewrite app_assoc.
          do 2 apply Remove_app_tail;auto.


          assert (IH' : RIndTensor (S n0 + S (S n))) by ( apply IH; omega).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n0 + S (S n) - 1 = n0 + S (S n)) by omega;rewrite Hn in HDw;clear Hn.
          eapply  HDw with (n1:= n) (m:= S ( S n0))... omega.
          apply Remove_Permute in H2;auto.
          rewrite H2 in HM2.
          inversion HM2...


          apply Remove_Permute in H2;auto.
          rewrite H2 in isFM2.
          inversion isFM2...


          rewrite H5 in isFM2.
          inversion isFM2...
          rewrite H5 in isFM2.
          inversion isFM2...
          inversion isFT...
          rewrite <- H13 in H12.
          rewrite <- H12 in H10;auto.
          assert(|-- B; (M1 ++ M2) ++ [F ** G]; (> [])).
          apply TensorComm'.
          refine(exchangeLC _ H14);perm.
          refine(exchangeLC _ H15);perm.
          apply Permutation_sym;auto.

          apply Permutation_unq in H2.
          change (F0 :: x) with ([F0] ++ x) in H2.
          apply app_eq_unit in H2.
          inversion H2...
          clear H2.


          change (F1 :: x0) with ([F1] ++ x0) in H5.
          apply app_eq_unit in H5.
          inversion H5...
          clear H5.

          eapply tri_dec1' with (F0:= F ** G) (L'1:=M1 ++ M2)...
          rewrite app_assoc.
          apply Remove_app_in'.
          eapply tri_tensor'.
          2:{ apply seqNtoSeq in H3. exact H3. }
          2:{ apply seqNtoSeq in H10. exact H10. }
          rewrite <- H11.
          rewrite <- H12.
          perm.
        ++  (* DEC 1 DEC 2 *)
          eapply tri_dec2' with (F2:=F1) ...
          assert (IH' : RIndTensor (S n + S (S n0))) by ( apply IH; omega).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n + S (S n0) - 1 = n + S (S n0)) by omega;rewrite Hn in HDw;clear Hn.
          assert(|-- B; M2 ++ M1 ++ [G ** F]; (>> F1)).
          eapply  HDw with (n1:= n) (m:= S ( S n0))...
          apply isFormulaIn in H5...

          inversion isFT...

          rewrite app_assoc.
          apply TensorComm'.
          refine(exchangeLC _ H11);perm.
        ++ (* DEC 1 DEC 3 *)
          eapply tri_dec3' with (F2:=F1) ...
          assert (IH' : RIndTensor (S n + S (S n0))) by ( apply IH; omega).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n + S (S n0) - 1 = n + S (S n0)) by omega;rewrite Hn in HDw;clear Hn.
          assert(|-- B; M2 ++ M1 ++ [G ** F]; (>> F1)).
          eapply  HDw with (n1:= n) (m:= S ( S n0))...
          inversion isFT...
          rewrite app_assoc.
          apply TensorComm'.
          refine(exchangeLC _ H11);perm.
        ++ (* DEC 2 DEC 1 *)
          eapply tri_dec2' with (F2:=F0) ...
          assert (IH' : RIndTensor (S n + S (S n0))) by ( apply IH; omega).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n + S (S n0) - 1 = n + S (S n0)) by omega;rewrite Hn in HDw;clear Hn.

          eapply  HDw with (n1:= n0) (m:= S ( S n))... omega.
          apply isFormulaIn  in H2...
        ++ (* DEC 2 DEC 2 *)
          eapply tri_dec2' with (F2:=F0) ...
          assert (IH' : RIndTensor (S n0 + S (S n))) by ( apply IH; omega).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n0 + S (S n) - 1 = n0 + S (S n)) by omega;rewrite Hn in HDw;clear Hn.
          eapply  HDw with (n1:= n0) (m:= S ( S n))... 
          apply isFormulaIn  in H2...
        ++ (* DEC 2 DEC 3 *)
          eapply tri_dec2' with (F2:=F0) ...
          assert (IH' : RIndTensor (S n0 + S (S n))) by ( apply IH; omega).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n0 + S (S n) - 1 = n0 + S (S n)) by omega;rewrite Hn in HDw;clear Hn.
          eapply  HDw with (n1:= n0) (m:= S ( S n))... 
          apply isFormulaIn  in H2...
        ++ (* DEC 3 DEC 1 *)  
          eapply tri_dec3' with (F2:=F0) ...
          assert (IH' : RIndTensor (S n0 + S (S n))) by ( apply IH; omega).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n0 + S (S n) - 1 = n0 + S (S n)) by omega;rewrite Hn in HDw;clear Hn.
          eapply  HDw with (n1:= n0) (m:= S ( S n))...
        ++ (* DEC 3 DEC 2 *)  
          eapply tri_dec3' with (F2:=F0) ...
          assert (IH' : RIndTensor (S n0 + S (S n))) by ( apply IH; omega).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n0 + S (S n) - 1 = n0 + S (S n)) by omega;rewrite Hn in HDw;clear Hn.
          eapply  HDw with (n1:= n0) (m:= S ( S n))...
        ++ (* DEC 3 DEC 3 *)  
          eapply tri_dec3' with (F2:=F0) ...
          assert (IH' : RIndTensor (S n0 + S (S n))) by ( apply IH; omega).
          destruct IH' as [HUp  HDw].
          assert(Hn : S n0 + S (S n) - 1 = n0 + S (S n)) by omega;rewrite Hn in HDw;clear Hn.
          eapply  HDw with (n1:= n0) (m:= S ( S n))...
    Qed.


    (* =============================================== *)
    (* PROOF OF RUP *)
    (* =============================================== *)
    Theorem InvTensorUP: forall  nm , (forall m : nat, m <= nm-> RIndTensor m) -> RUpTensor (S nm).
    Proof with subst;auto;solveF.
      intros nm IH.
      unfold RUpTensor; intros B L1  M1 L2 M2  F  G n' m' HNM HM1pos  HM2pos isFF isFG isFB isFM isFM' isFT HD1 HD2.
      destruct L1;destruct L2;simpl in *.
      + (* L1 and L2 are Empty *)   
        inversion HD1;inversion HD2;subst;
          try(
              match goal with
              | [ |- |-- ?B; ?M1 ++ ?M2 ++ [?F ** ?G]; UP [] ]
                => tryif (assert(HAFG : asynchronous F /\ asynchronous G) by (split;constructor;auto))
                then
                  eapply ITCaseAsyncAsync;eauto
                else idtac;eauto
              end)...

        eapply ITAsyncSync with  (nm := nm) (n:= n') (m:=n0) ;try omega;solveF;eauto.
        left;constructor.

        eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) ;try omega;solveF;eauto.
        left;constructor.

        eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) ;try omega;solveF;eauto.
        left;constructor.

        eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) ;try omega;solveF;eauto.
        left;constructor.

        eapply ITAsyncSync with  (nm := nm) (n:= S n) (m:=n0) ;try omega;solveF;eauto.
        left;constructor.

        assert(|-- B; M2 ++ M1 ++ [F ** top]; (> [])).
        rewrite app_assoc.
        apply TensorComm'.
        rewrite <- app_assoc.

        eapply ITAsyncSync with  (nm := nm) (n:= m') (m:=n) ;try omega;solveF;eauto.
        left;constructor.
        inversion isFT...

        refine(exchangeLC _ H);perm.

        assert(|-- B; M2 ++ M1 ++ [F ** bot]; (> [])).
        rewrite app_assoc.
        apply TensorComm'.
        rewrite <- app_assoc.

        eapply ITAsyncSync with  (nm := nm) (n:= S n0) (m:=n) ;try omega;solveF;eauto.
        left;constructor.
        inversion isFT...

        refine(exchangeLC _ H);perm.

        assert(|-- B; M2 ++ M1 ++ [F ** (F1 $ G0)]; (> [])).
        rewrite app_assoc.
        apply TensorComm'.
        rewrite <- app_assoc.

        eapply ITAsyncSync with  (nm := nm) (n:=S n0) (m:=n) ;try omega;solveF;eauto.
        left;constructor.
        inversion isFT...

        refine(exchangeLC _ H);perm.

        assert(|-- B; M2 ++ M1 ++ [F ** (F1 & G0)]; (> [])).
        rewrite app_assoc.
        apply TensorComm'.
        rewrite <- app_assoc.

        eapply ITAsyncSync with  (nm := nm) (n:=S n0) (m:=n) ;try omega;solveF;eauto.
        left;constructor.
        inversion isFT...

        refine(exchangeLC _ H);perm.

        assert(|-- B; M2 ++ M1 ++ [F ** (? F1)]; (> [])).
        rewrite app_assoc.
        apply TensorComm'.
        rewrite <- app_assoc.

        eapply ITAsyncSync with  (nm := nm) (n:=S n0) (m:=n) ;try omega;solveF;eauto.
        left;constructor.
        inversion isFT...

        refine(exchangeLC _ H);perm.

        (* both F and G are not asynchronous formulas *)
        eapply  ITSyncSync with (nm := nm) (n:=n) (m:=n0)...

        assert(|-- B; M2 ++ M1 ++ [F ** (F{ FX})]; (> [])).
        rewrite app_assoc.
        apply TensorComm'.
        rewrite <- app_assoc.

        eapply ITAsyncSync with  (nm := nm) (n:=S n0) (m:=n) ;try omega;solveF;eauto.
        left;constructor.
        inversion isFT...

        refine(exchangeLC _ H);perm.

        eapply ITAsyncSync with  (nm := nm) (n:=S n) (m:=n0) ;try omega;solveF;eauto.
        left;constructor.
      + (* L1 is empty and L2 is not empty *)
        eapply InvTensorConsNil with (nm:=nm) (n':=n') (m':=m') (L1 := [])...
        inversion isFF...
        inversion isFF...
      + (* L1 is not empty and L2 is empty *)
        assert( |-- B; M2 ++ M1 ++ [G ** F]; UP ([] ++ o :: L1 )).
        eapply InvTensorConsNil with (nm:=nm) (n':=m') (m':=n') ... omega.
        inversion isFT...
        inversion isFG...
        inversion isFG...

        rewrite app_nil_r.
        simpl in H.
        rewrite app_assoc.
        apply TensorComm'.
        refine(exchangeLC _ H);perm.
      +  (* L1 and L2 are not empty *)
        apply InvTensorConsNil with (nm:=nm) (n':=n') (m':=m') (L1 := o :: L1)...
        inversion isFF...
        inversion isFF...      
    Qed.

    (* =============================================== *)
    (* PROOF OF RDOWN *)
    (* =============================================== *)
    Theorem InvTensorDW: forall  n , (forall m : nat, m <= n -> RIndTensor m) -> RDownTensor (n).
    Proof with subst;auto;solveF.
      intros n IH.
      unfold RDownTensor; intros B M M'  H  F G n0 m Hnm  HM1pos HM2pos HPosF isFB isFM isFM' isFH isFT  HD1 HD2.
      inversion HD1...
      + 
        apply symmetry in H3.
        apply app_eq_unit in H3.
        inversion H3...
        inversion HPosF .
      + solveList.        
      + solveList. 
      +
        apply PProp_perm_sel in H1.
        destruct H1.
        ++ 
          destruct H...
          assert(HRI: RIndTensor (S m + n1)).  apply IH. omega. 
          destruct HRI as [HUp  HDown] ...
          simpl in HDown.
          rewrite Nat.sub_0_r in HDown.    
          eapply tri_tensor' with (N0:=N ) (M1:=x ++ M' ++ [F ** G])...
          rewrite <- H0. perm.
          eapply HDown with (n:=n1) (m0:=m)... omega.

          rewrite <- H0 in HM1pos.
          apply ForallAppInv1 in HM1pos...
          rewrite <- H0 in isFM.
          eapply ForallAppInv1 in isFM...
          inversion isFH...
          rewrite <- H;auto.
          apply seqNtoSeq in H6;auto.
        ++ 
          destruct H...
          assert(HRI: RIndTensor (S m + n1)).  apply IH. omega. 

          destruct HRI as [HUp  HDown] ...
          simpl in HDown.
          rewrite Nat.sub_0_r in HDown.    
          eapply tri_tensor' with (N0:=x ++ M' ++ [F ** G] ) (M1:=M0 )...
          rewrite <- H0. perm.
          apply seqNtoSeq in H2;auto.  
          eapply HDown with (n:=n1) (m0:=m)... omega.

          rewrite <- H0 in HM1pos.
          apply ForallAppInv2 in HM1pos...
          rewrite <- H0 in isFM.
          eapply ForallAppInv2 in isFM...
          inversion isFH...
          rewrite <- H;auto.
      +
        assert(HRI: RIndTensor (S m +n1)) by (apply IH ; omega).
        destruct HRI as [HUp  HDown] ...
        assert(Hn : S m + n1 -1 =  m + n1) by omega;rewrite Hn in HDown;clear Hn.
        apply tri_plus1'. 
        eapply HDown  with (n:=n1)... 
        3:{ exact HD2. }
        omega.
        inversion isFH...
      +
        assert(HRI: RIndTensor (S m +n1)) by (apply IH ; omega).
        destruct HRI as [HUp  HDown] ...
        assert(Hn : S m + n1 -1 =  m + n1) by omega;rewrite Hn in HDown;clear Hn.
        apply tri_plus2'. 
        eapply HDown  with (n:=n1)... 
        3:{ exact HD2. }
        omega.
        inversion isFH...
      + solveList.
      +
        apply UpExtension in H5 ...
        destruct H5.
        destruct H0.

        assert(HRI: RIndTensor (m + x)). apply IH. omega.
        eapply tri_rel' ...
        destruct HRI as [HUp  HDown]. clear HDown.
        assert(|-- B; M ++ M' ++ [F ** G]; UP ( [H] ++ [])).
        eapply HUp with (n:= x )(m0:= m) ... omega.
        rewrite app_nil_r in H3;auto.
        apply PosConc...
      +   
        assert(HRI: RIndTensor (m + S n1 )) by ( apply IH;omega).
        destruct HRI as [HUp  HDown] ...
        assert(Hn : m + S n1 -1 =  m + n1) by omega;rewrite Hn in HDown;clear Hn.
        eapply tri_ex'... exact H2.
        eapply HDown with (n:=n1) (m0:=m)...  
        omega.
        inversion isFH...
    Qed.


    Theorem InvTensorAux : forall n, RIndTensor n.
    Proof.
      intro n.
      induction n using strongind.
      + unfold RIndTensor.
        split; [apply RUpT0 | apply RDownT0].
      + unfold RIndTensor in *.
        split;[|simpl;  rewrite Nat.sub_0_r].
        apply InvTensorUP; assumption.
        apply InvTensorDW; assumption.
    Qed.

    (* =============================================== *)
    (* MAIN INVERTIBILITY THEOREM *)
    (* =============================================== *)

    Theorem InvTensor : forall B L L' F G  M M', 
        isNotAsyncL M  -> isNotAsyncL M' ->   isFormulaL B -> isFormulaL M -> isFormulaL M' -> isFormula (F ** G) ->
        isFormulaL L -> isFormulaL L' ->
        |-- B  ;M ; UP (F :: L) -> |-- B; M'; UP (G :: L') -> |-- B ; M ++ M' ++ [F ** G]  ; UP (L ++ L') .
    Proof.
      intros.
      apply EquivUpArrow2 with (L'0 := L ++ [F]) in H7 ;eauto.
      apply EquivUpArrow2 with (L'0 := L' ++ [G]) in H8 ;eauto.
      assert(HRn:  forall n, RUpTensor n) by (apply InvTensorAux).
      apply seqtoSeqN in H7.
      apply seqtoSeqN in H8.
      destruct H7.
      destruct H8.
      generalize (HRn (x + x0));intros.
      eapply H9;subst;auto.
      inversion H4...
      apply ForallApp;auto.
      perm.
      inversion H4...
      apply ForallApp;auto.
      perm. 
    Qed.

  End InvTensor.
End InvPosPhase.
