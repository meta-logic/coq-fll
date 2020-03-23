(** * Invertibility results for the negative phase

This file proves that exchange is admissible also in the list L in
[seq Gamma Delta (> L)]. For that, some invertibility lemmas are
needed.
 *)
Require Export FLL.Misc.Hybrid.
Require Export FLL.SL.FLLTactics.
Require Import Lia.
Require Import FLL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Hint Unfold isFormulaL : core.

Section InvNPhase .
  Context `{OLS: OLSig}.
  Hint Constructors isFormula  Remove seqN IsPositiveAtom : core .

  Variable theory : oo -> Prop .
  Notation " n '|---' B ';' L ';' X " := (seqN theory n B L X) (at level 80).
  Notation " '|--' B ';' L ';' X " := (seq theory B L X) (at level 80).

  Theorem exp_weight0LF : forall l L, 0%nat = complexity l + complexityL L -> False.
  Proof.
    intros.
    assert(complexity l > 0%nat) by (apply Complexity0).
    omega.
  Qed.
  
  Theorem EquivAuxBot :  forall CC LC M M',
      (|-- CC ; LC ; (> M ++ M') ) ->
      (|-- CC ;  LC ; (> M ++ Bot :: M') ) .
  Proof with solveF.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    solveLL' ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    destruct a; simpl in *; invTri' H0;solveLL';
      repeat rewrite app_comm_cons;
      try match goal with
          |  [ |- seq _ _ _ (> ?M ++ bot :: _) ] =>
             eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveF
          end.
    assert (Hvar : proper (VAR con 0)) by constructor.
    generalize (ComplexityUniformEq H5 properX Hvar);intro.
    omega.
  Qed.

  Theorem EquivAuxWith :  forall F G CC LC M M',
      (|-- CC ; LC ; (> M ++ [F] ++ M') ) ->
      (|-- CC ; LC ;(> M ++ [G] ++ M') ) ->
      (|-- CC ; LC ; (> M ++ (AAnd F G) :: M') ) .
  Proof with solveF.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    solveLL' ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct a; simpl in *; invTri' H0;solveLL';
      repeat rewrite app_comm_cons;
      try solve [
            match goal with
            |  [ |- seq _ _ _ (> ?M ++ (AAnd _ _) :: _) ] =>
               eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM;solveF;InvTriAll';auto
            end] .
    
    
    eapply H with (M:= o x:: M) (m:= complexityL (o x:: M));simpl in *; inversion HeqSizeM;solveF;InvTriAll';auto.
    generalize (ComplexityUniformEq H6 properX (proper_VAR con 0));intro...
  Qed.
  
  
  
  Theorem EquivAuxPar : forall F G CC LC M M',
      (|-- CC ; LC ; (> M ++ [F ; G] ++ M') ) ->
      (|-- CC ; LC ;(> M ++ (MOr F G) :: M') ) .
  Proof with solveF.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    solveLL' ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct a; simpl in *; invTri' H0;solveLL';
      repeat rewrite app_comm_cons;
      match goal with
      |  [ |- seq _ _ _ (> ?M ++ (MOr F G) :: _) ] =>
         eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveF
      end.
    generalize (ComplexityUniformEq H5 properX (proper_VAR con 0));intro...
  Qed.
  
  Theorem EquivAuxStore :
    forall F CC LC M M', ~ asynchronous  F ->
                         (|-- CC ; (LC ++ [F]) ;(> M ++ M') ) ->
                         (|-- CC ; LC ; (> M ++ F :: M') ) .
  Proof with solveF.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    apply tri_store'...

    
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct a; simpl in *; invTri' H1 ;solveLL';
      repeat rewrite app_comm_cons;
      try solve [eapply H0 with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveF;
                 try (rewrite <- Per_app_assoc_comm; rewrite app_assoc_reverse in H7;auto)].

    eapply H0 with (m:= complexityL (a1 :: M))...
    eapply H0 with (m:= complexityL (a2 :: M))...
    eapply H0 with (m:= complexityL (a1 :: a2 :: M))...

    eapply H0 with (m:= complexityL (o x :: M))...
    inversion HeqSizeM... 
    generalize (ComplexityUniformEq H6 properX (proper_VAR con 0));intro...
  Qed.
  
  
  Theorem EquivAuxQuest : forall F CC LC M M',
      (|-- (CC ++ [F]) ; LC ;(> M ++  M') ) ->
      (|-- CC ; LC ; (> M ++ [? F] ++ M') ) .
  Proof with solveF.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    solveLL' ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct a; simpl in *; invTri' H0;solveLL';
      repeat rewrite app_comm_cons;
      try solve [
            match goal with
            |  [ |- seq _ _ _ (> ?M ++ (? _) :: _) ] =>
               eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM;solveF;InvTriAll';auto
            end] .
    
    eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM;solveF;InvTriAll';auto.
    try (rewrite <- Per_app_assoc_comm; rewrite app_assoc_reverse in H4;auto).

    eapply H with (m:= complexityL (o x :: M));simpl in *; inversion HeqSizeM;solveF;InvTriAll';auto.
    generalize (ComplexityUniformEq H5 properX (proper_VAR con 0));intro...
  Qed.
  
  Theorem EquivAuxTop :  forall CC LC M M',
      isFormulaL M ->
      (|-- CC ; LC ; (> M ++ Top :: M') ) .
  Proof with solveF.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    solveLL' ...
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct a; simpl in *;solveLL';
      repeat rewrite app_comm_cons;
      try solve [
            match goal with
            |  [ |- seq _ _ _ (> ?M ++ top :: _) ] =>
               eapply H with (m:= complexityL M);simpl in *; inversion HeqSizeM; solveF; inversion H0;subst;auto
            end].
    
    eapply H with (m:= complexityL (a1 ::M));simpl in * ; inversion HeqSizeM; solveF; inversion H0;subst;auto.
    inversion H3;subst...
    eapply H with (m:= complexityL (a2 ::M));simpl in * ; inversion HeqSizeM; solveF; inversion H0;subst;auto.
    inversion H3;subst...
    eapply H with (m:= complexityL (a1 :: a2 ::M));simpl in * ; inversion HeqSizeM; solveF; inversion H0;subst;auto.
    inversion H3;subst...

    inversion H0... inversion H3...
    solveLL'.
    eapply H with (M:= o x :: M) (m:= complexityL (o x ::M));simpl in * ; inversion HeqSizeM; solveF; inversion H0;subst;auto.

    
    rewrite (ComplexityUniformEq  H2 properX (proper_VAR con 0));auto.
  Qed.

  Theorem EquivAuxForAll : forall FX CC LC M M' ,
      isFormulaL M -> uniform_oo FX ->
      (forall t, proper t ->  (|-- CC ; LC ; (> M ++ (FX t) ::M') )) ->
      (|--  CC ; LC ; (> M ++ F{ FX} :: M') ) .
  Proof with solveF.
    intros.
    remember (complexityL M) as SizeM.
    revert dependent CC.
    revert dependent LC.
    revert dependent M.
    revert dependent M'.
    induction SizeM using strongind;intros ...
    
    symmetry in HeqSizeM; apply ComplexityL0 in HeqSizeM ...
    solveLL'.
    
    destruct M as [ | a]; simpl in HeqSizeM.
    inversion HeqSizeM.
    
    destruct a; simpl in *;solveLL';
      try solve [eapply H with (m:= complexityL M);inversion HeqSizeM;subst;solveF;intros;solveLL'; inversion H1;subst;auto;
                 generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF].

    
    
    eapply H with (M:= a1 :: M)(m:= complexityL (a1 :: M));inversion HeqSizeM;subst;solveF;intros;solveLL'.
    inversion H1;subst;auto.  inversion H5;auto. generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF.

    eapply H with (M:= a2 :: M)(m:= complexityL (a2 :: M));inversion HeqSizeM;subst;solveF;intros;solveLL'.
    inversion H1;subst;auto.  inversion H5;auto. generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF.

    eapply H with (M:= a1 :: a2 :: M)(m:= complexityL (a1 :: a2 :: M));inversion HeqSizeM;subst;solveF;intros;solveLL'.
    inversion H1;subst;auto.  inversion H5;auto. generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF.

    inversion H1... inversion H5...
    solveLL'.
    eapply H with (M:=  o x :: M)(m:= complexityL (o x :: M));inversion HeqSizeM;subst;solveF;intros;solveLL'.
    inversion H1;subst;auto.  inversion H5;auto.
    generalize (ComplexityUniformEq H4 properX (proper_VAR con 0));intro...
    generalize (H2 _ H3);intros Hs;invTri' Hs ;solveF.
  Qed.
  

  Theorem EquivUpArrow : forall B L L' M n,
      isFormulaL L' ->
      (n |--- B ; M ; UP L) ->
      Permutation L L' ->
      |-- B ; M ;  UP L'.
  Proof.
    intros.
    remember (complexityL L) as w.
    generalize dependent n .
    generalize dependent L .
    generalize dependent L' .
    generalize dependent B .
    generalize dependent M .
    generalize dependent w .
    
    induction w as [| w' IH] using strongind;  intros ;  destruct L as [|l].
    +  apply Permutation_nil in H1;subst.
       apply seqNtoSeq in H0;auto.
    + inversion Heqw.
      apply exp_weight0LF in H3. contradiction.
    + inversion Heqw.
    +  destruct L' as [| l'].
       symmetry in H1.
       apply Permutation_nil in H1.
       inversion H1.
       assert
         ((l = l' /\ Permutation L L') \/
          (exists L1 L2 L1' L2', L = L1 ++ [l'] ++ L2 /\ L' = L1' ++ [l] ++ L2' /\ Permutation (L1 ++ L2) (L1' ++ L2') )) .
       *     
         
         apply PProp_perm_select in H1.
         intuition.
         right.
         destruct H2.  
         destruct H1.
         assert (exists T1 T2, L' = T1 ++ [l] ++ T2).   
         induction x.
    - do 2 eexists [].
      symmetry in H1.
      apply Permutation_unq in H1.
      simpl; auto.
    - assert (In l  L') as Hm.
      rewrite H1.
      apply in_eq.
      apply in_split;auto.
    -  
      assert (exists T1 T2, L = T1 ++ [l'] ++ T2).
      induction x.
      do 2 eexists [].
      symmetry in H2.
      apply Permutation_unq in H2.
      simpl; auto.
      assert (In l'  L) as Hm.
      rewrite H2.
      apply in_eq.
      apply in_split;auto.
      do 2 destruct H3. 
      do 2 destruct H4.
      
      eexists x2; eexists x3; eexists x0; eexists x1. 
      intuition.
      rewrite H3 in H1.
      simpl in H1.
      rewrite Permutation_midle in H1. 
      apply Permutation_cons_inv in H1.
      rewrite H4 in H2.
      simpl in H2.
      rewrite Permutation_midle in H2. 
      apply Permutation_cons_inv in H2.
      rewrite H1. rewrite H2. auto.
      
      *
        
        destruct H2 as [Heq | Heq].
        ++ destruct Heq;subst.
           inversion H0;subst;try(simpl in Heqw; inversion Heqw; subst;simpl;try(omega)).
           +++  (* top *)
             eapply tri_top'.
           +++ (* bottom *)
             eapply IH with (L' :=L') in H7;auto.
             
             apply tri_bot';auto.
             inversion H;subst;auto.
           +++ (* par *)
             eapply IH with (L' := F::G::L') in H7;auto.
             apply tri_par';auto.
             inversion H;subst.
             inversion H5;subst.
             change (F :: G :: L') with ([F] ++ [G] ++ L').
             apply ForallApp;auto.
             apply ForallApp;auto.
             
             simpl. omega.
           +++ (* with *)
             eapply IH with (m:= complexityL (F::L)) (L:= F ::L) (L' := F :: L') in H8;auto.
             eapply IH with (m:= complexityL (G::L)) (L := G :: L) (L' := G :: L') in H9;auto.
             apply tri_with';auto.
             simpl. omega.
             inversion H;subst.
             inversion H5;subst.
             change (G :: L') with ([G] ++ L').
             apply ForallApp;auto.
             simpl. omega.
             inversion H;subst.
             inversion H5;subst.
             change (F :: L') with ([F] ++ L').
             apply ForallApp;auto.           
           +++  (* quest *)
             eapply IH with (m:= complexityL L) (L' :=L') in H7;auto.
             apply tri_quest';auto.
             omega.
             inversion H;subst;auto.
           +++  (* store *)
             eapply IH with (m:= complexityL L) (L' :=L') in H9;auto.
             apply tri_store';auto.
             assert (complexity l' > 0) by (apply Complexity0).
             omega.
             inversion H;subst;auto.
           +++ (* forall *)
             eapply tri_fx';auto;intros.
             generalize (H9 x H2);intro.
             eapply IH with (m:= complexity (FX x) + complexityL L) (L' := FX x :: L') in H4;auto.
             assert(complexity (FX (VAR con 0)) = complexity (FX x) ).
             apply ComplexityUniformEq;auto.          
             constructor.
             lia.
             inversion H;subst.
             inversion H7;subst.
             change (FX x  :: L') with ([FX x ] ++ L').
             apply ForallApp;auto.
             
        ++
          destruct Heq as [L1 [L2 [L1' [L2' Heq]]]].
          destruct Heq as [Heq [Heq1 Heq2]];subst.
          
          inversion H0;subst.
          
          +++ (* top *)
            eapply EquivAuxTop with (M:= l' :: L1'). 
            inversion H;subst;auto.
            change (l' :: L1') with ([l'] ++ L1').
            apply ForallApp;auto.
            eapply ForallAppInv1. exact H5.
            
          +++ (* bottom *)
            eapply IH with (m:= complexityL (L1 ++ l' :: L2))(L:=L1 ++ l' :: L2) (L' := [l'] ++ L1' ++ L2') in H6 .
            simpl in H6. 
            apply EquivAuxBot with (M:= l' :: L1');auto.
            simpl in Heqw. inversion Heqw. auto.
            inversion H;subst;auto.
            
            apply ForallApp;auto.
            apply Forall_forall;intros.
            rewrite Forall_forall in H5.
            apply H5.
            apply in_or_app.
            apply in_app_or in H2.
            destruct H2;try intuition.

            rewrite Permutation_midle.
            apply Permutation_cons;auto. 
            auto.
            
          +++ (* par *)
            eapply IH with (m:= complexityL (F :: G :: L1 ++ l' :: L2))
                           (L:=F :: G :: L1 ++ l' :: L2)
                           (L' := [l'] ++ L1' ++ [F ; G] ++ L2') in H6.
            apply seqtoSeqN in H6. destruct H6.
            eapply EquivAuxPar with (M:= l' :: L1');simpl;simpl in H2;eauto using seqNtoSeq.
            simpl in Heqw. inversion Heqw. simpl.  lia.
            
            
            inversion H;subst;auto.

            apply ForallApp;auto.
            
            
            apply ForallApp;auto.
            apply ForallAppInv1 in H5;auto.
            apply ForallAppInv2 in H5;auto.
            inversion H5;subst;auto.
            apply ForallApp;auto.
            inversion H7;subst;auto.
            simpl.
            rewrite Permutation_midle. rewrite Permutation_midle.
            rewrite Permutation_midle. rewrite Heq2. perm.
            auto.


          +++ (* with *)
            eapply IH with (m:= complexityL (F :: L1 ++ l' :: L2))
                           (L:=F :: L1 ++ l' :: L2)
                           (L' := [l'] ++ L1' ++ [F ] ++ L2') in H7;auto .
            eapply IH with (m:= complexityL (G :: L1 ++ l' :: L2))
                           (L:=G :: L1 ++ l' :: L2)
                           (L' := [l'] ++ L1' ++ [G ] ++ L2') in H8;auto .
            
            apply EquivAuxWith with (M := l' :: L1'); simpl;auto.
            inversion Heqw. simpl. lia.
            
            inversion H;subst;auto.

            apply ForallApp;auto.
            
            
            apply ForallApp;auto.
            apply ForallAppInv1 in H5;auto.
            apply ForallAppInv2 in H5;auto.
            inversion H5;subst;auto.
            apply ForallApp;auto.
            inversion H6;subst;auto.
            
            simpl.
            
            rewrite Permutation_midle. rewrite Heq2. perm.
            inversion Heqw. simpl. lia.
            
            inversion H;subst;auto.

            apply ForallApp;auto.
            
            
            apply ForallApp;auto.
            apply ForallAppInv1 in H5;auto.
            apply ForallAppInv2 in H5;auto.
            inversion H5;subst;auto.
            apply ForallApp;auto.
            inversion H6;subst;auto.
            
            
            simpl.
            
            rewrite Permutation_midle. rewrite Heq2. perm.
            
          +++ (* quest *)
            eapply IH with (m:= complexityL (L1 ++ l' :: L2))(L:=L1 ++ l' :: L2) (L' := [l'] ++ L1' ++ L2') in H6;auto .
            apply seqtoSeqN in H6. destruct H6.   
            eapply EquivAuxQuest with (M := l' :: L1');simpl in H2;eauto using seqNtoSeq.
            
            inversion Heqw. simpl. lia.
            
            inversion H;subst;auto.

            apply ForallApp;auto.
            
            
            apply ForallApp;auto.
            apply ForallAppInv1 in H5;auto.
            apply ForallAppInv2 in H5;auto.
            inversion H5;subst;auto.
            
            
            rewrite Permutation_midle. rewrite Heq2. perm.

          +++ (* copy *)
            eapply IH with (m:= complexityL(L1 ++ l' :: L2))(L:=L1 ++ l' :: L2) (L' := [l'] ++ L1' ++ L2') in H8;auto .

            eapply EquivAuxStore with (M:=l' :: L1');eauto.
            inversion Heqw.
            assert (complexity l > 0) by (apply Complexity0).
            lia.
            
            inversion H;subst;auto.

            apply ForallApp;auto.
            
            
            apply ForallApp;auto.
            apply ForallAppInv1 in H5;auto.
            apply ForallAppInv2 in H5;auto.
            inversion H5;subst;auto.
            
            
            rewrite Permutation_midle. rewrite Heq2. perm.
          +++ (* forall *)
            
            
            assert(forall x, proper x -> |-- B; M; UP ((l' :: L1' ) ++ [FX x] ++ L2')).
            intros x pX.
            eapply IH with (m:= complexityL(FX x :: L1 ++ l' :: L2)) (L:=FX x :: L1 ++ l' :: L2)  ;auto.
            inversion Heqw.
            simpl. 
            assert(complexity (FX (VAR con 0)) = complexity (FX x) ).
            
            apply ComplexityUniformEq;auto. 
            constructor. lia.
            
            inversion H;subst;auto.
            change ((l' :: L1') ++ [FX x] ++ L2') with ([l'] ++ L1' ++ [FX x] ++ L2').
            apply ForallApp;auto.
            
            
            apply ForallApp;auto.
            apply ForallAppInv1 in H5;auto.
            
            apply ForallAppInv2 in H5;auto.
            inversion H5;subst.
            inversion H6;subst.

            apply ForallApp;auto.
            
            
            rewrite Permutation_midle. rewrite Heq2. perm.

            assert(forall B  L L' M   FX, 
                      isFormulaL L -> uniform_oo FX ->  (forall x, proper x -> |-- B ; M ; UP (L ++ [FX x]++ L')) ->  |-- B ; M ;  UP (L ++ [F{FX}] ++ L')).
            intros.
            eapply EquivAuxForAll;auto.
            
            apply H3 in H2;auto.
            inversion H;subst.
            change (l' :: L1') with ([l'] ++ L1').
            apply ForallApp;auto.   
            apply ForallAppInv1 in H9;auto. 
            
  Qed.

  Theorem EquivUpArrow2 : forall B L L' M ,
      isFormulaL L' ->
      (|-- B ; M ; UP L) -> Permutation L L' ->
      |-- B ; M ;  UP L'.
    intros.
    apply seqtoSeqN in H0.
    destruct H0.
    eapply EquivUpArrow in H0;eauto.
  Qed.



  Generalizable All Variables.
  Global Instance Forall_morph : 
    Proper ((@Permutation oo) ==> Basics.impl) (isNotAsyncL).
  Proof.
    unfold Proper; unfold respectful; unfold Basics.impl.
    intros.
    eapply Forall_Permute;eauto.
  Qed. 

  
  Lemma UpExtension: forall B M L F n,
      isNotAsyncL (M++[F]) ->
      (n |--- B; M ++ [F] ; UP L) ->
      exists m, m<= S n /\ m |--- B; M ; UP (L ++ [F]).
  Proof with subst;auto.
    intros.
    remember (complexityL L) as w.
    generalize dependent L .
    generalize dependent B .
    generalize dependent M .
    generalize dependent n .
    generalize dependent w .

    induction w as [| w' IH] using strongind .  intros n  M HPos B L HD Hw.
    + (* w = 0 *)
      destruct L. (* L must be empty. The second case is trivial *)
      exists ((S n)).
      split;auto.
      simpl.
      eapply tri_store;auto.
      apply ForallAppInv2 in HPos.
      inversion HPos... 
      simpl in Hw.
      apply exp_weight0LF in Hw;contradiction.
    + intros.
      destruct L. (* L cannot be empty *)
      inversion Heqw.
      inversion H0;auto;subst;inversion Heqw;subst.
      ++ (* top *)
        exists 0%nat;split;try lia.
        eapply tri_top.
      ++ (* bot *)
        apply IH with (m:= complexityL L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n');split;auto. omega. simpl. eapply tri_bot;auto.
      ++  (* PAR *)
        apply IH with (m:= complexity F0 + complexity  G + complexityL  L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n');split;auto. omega. simpl. eapply tri_par;auto.
        simpl. omega.
      ++ (* with *)
        apply IH with (m:= complexity  F0 + complexityL  L) in H6;try lia;auto.
        apply IH with (m:= complexity  G + complexityL L) in H7;try lia;auto.
        destruct H6 as [n'  [IHn IHd]].
        destruct H7 as [m'  [IHn' IHd']].
        simpl.
        
        exists (S (S n0));split;auto. 
        eapply tri_with;auto.
        eapply HeightGeq. exact IHd. 
        lia.
        eapply HeightGeq. exact IHd'. 
        lia.
        
      ++  (* quest *)
        apply IH with (m:= complexityL  L) in H5;auto.
        destruct H5 as [n'  [IHn IHd]].
        exists (S n');split;auto. omega. simpl; eauto.
        omega.
      ++ (* Store *)
        assert(exists m0 : nat, m0 <= S n0 /\ m0 |--- B; M ++ [o]; UP (L ++ [F])).
        apply IH with (m:= complexityL L);auto.
        assert (complexity o > 0) by (apply Complexity0);lia.
        
        apply ForallApp...
        apply ForallApp...
        apply ForallAppInv1 in H...
        apply ForallAppInv2 in H...

        eapply exchangeLCN;[|exact H7].
        perm.
        
        destruct H1 as [n'  [IHn IHd]].
        exists (S n');split;auto. omega. simpl;eauto.
        
      ++  (* FORALL *)
        assert(forall x, proper x -> exists m, m <= S n0 /\  m |--- B; M; UP ((FX x :: L)  ++ [F])).
        intros.
        generalize (H7 x H1);intro.
        eapply IH with (m:=complexity (FX x) + complexityL L);auto.
        assert(complexity (FX (VAR con 0)) = complexity (FX x) ).
        
        apply ComplexityUniformEq;auto. 
        
        constructor.
        lia.
        
        exists (S (S n0)). split.
        omega.
        simpl.
        eapply tri_fx;auto. intros.
        
        generalize (H1 _ H2);intro.
        
        destruct H3 as [n H3].
        destruct H3 as [H3 H3'].
        eapply HeightGeq.
        exact H3'.
        lia.
  Qed.
  
End InvNPhase.
