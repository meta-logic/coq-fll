(** Cut Elimination for Focused Linear Logic

This file proves cut-elimination for the triadic system of linear
logic. The proof uses 5 cut-rules dealing with the negative and
positive phase of proofs (see [CutElimBase]).

It is assumed that the theory only produces well formed LL formulas
(see [TheoryIsFormula]).
 *)


Require Export FLL.Misc.Hybrid.
Require Export FLL.SL.FLLTactics.
Require Import Lia.
Require Import FLL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.
Require Export FLL.SL.InvPositivePhase.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Section CutElimination.
  Context `{OLS: OLSig}.
  Hint Constructors isFormula  remove seqN IsPositiveAtom : core .


  
  Variable theory : oo -> Prop .
  Notation " n '|---' B ';' L ';' X " := (seqN theory n B L X) (at level 80).
  Notation " '|--' B ';' L ';' X " := (seq theory B L X) (at level 80).
  
  Theorem CutElimBase C dualC D dualD B L M N P: 
    dualC = dual C ->
    (0 |--- B; M++[C] ; DW P -> 
                        0  |--- B; N ; DW dualC -> 
                                       |-- B; M++N ; DW P)
    /\
    (0 |--- B; M++[C] ; UP L -> 
                        0 |--- B; N ; DW dualC -> 
                                      |-- B; M++N ; UP L)
    /\
    (0 |--- B; M ; UP (C::L) -> 
                   0 |--- B; N ; DW dualC -> 
                                 |-- B; M++N ; UP L) 
    /\
    (dualD = dual D -> dualC = (! dualD) -> 
     0 |--- B++[D]; M ; UP L -> 
                        0 |--- B; [] ; DW (! dualD) -> 
                                       |-- B; M ; UP L)
    /\
    (dualD = dual D  -> dualC = (! dualD) -> 
     ~ IsPositiveAtom D ->
     0 |--- B++[D]; M ; DW P -> 
                        0 |--- B; [] ; DW (! dualD) -> 
                                       |-- B; M ; DW P). 
  Proof with subst;auto.
    intros CDual.
    split;[intros
          |split;[intros
                 |split;[intros
                        |split;intros]]].
    * (** Dw Linear Cut *)
      inversion H...
      **
        symmetry in H4.
        apply app_eq_unit in H4.
        destruct H4.
    + inversion H1...
      inversion H3...
      clear H1 H3.
      apply seqNtoSeq in H0. 
      exact H0.
    + inversion H1...
      inversion H3.
      **
        symmetry in H1.
        apply app_eq_nil in H1.
        destruct H1.
        inversion H2.     
      **
        symmetry in H4.
        apply app_eq_nil in H4.
        destruct H4.
        inversion H2.        
      * (** Up Linear Cut *)
        inversion H...
        eapply tri_top'.
      * (** Up Cut *)
        inversion H...     
        inversion H0.
      * (** Up Classic Cut *)
        inversion H2.
      *
        inversion H3.
  Qed.
  
  Lemma AtomPerm0 j B F L P:
    IsPositiveAtom P -> j |--- B; []; (>> ! P ^) -> 0 |--- B ++ [P]; L; (>> F) -> |-- B; L; (> [F]).
  Proof with subst;auto;solveF.
    intros isPAP Hj H0.
    inversion isPAP...
    clear isPAP.
    inversion H0...
    +
      eapply tri_store'...
      eapply tri_dec1' with (F:=perp A0) (L':=[atom A0])...
      eapply tri_init1'.
    +
      apply in_app_or in H4.
      inversion H4...
      eapply tri_store'...
      eapply tri_dec1' with (F:=perp A0) (L':=[])...
      eapply tri_init2'...
      inversion Hj...
      
      apply seqNtoSeq in H5...
    +    
      eapply tri_store'...
      eapply tri_dec1' with (F:=one) (L':=[])...
      eapply tri_one'. 
  Qed.    

  Definition CutH (w h: nat) :=  
    forall m i j C dualC D dualD P M N L B, 
      m <= h ->
      m = i + j ->
      dualC = C ^ ->
      isFormula C -> isFormula dualC ->
      complexity C = S w ->
      isFormula P ->
      isNotAsyncL N ->
      isFormulaL N ->
      isNotAsyncL M ->
      isFormulaL M ->
      isFormulaL L ->
      isFormulaL B ->
      (i |--- B; M ++ [C]; (>> P) -> j |--- B; N; (>> dualC) -> |-- B; M ++ N; (>> P)) /\
      (i |--- B; M ++ [C]; (> L) -> j |--- B; N; (>> dualC) -> |-- B; M ++ N; (> L)) /\
      (i |--- B; M; (> C :: L) -> j |--- B; N; (>> dualC) -> |-- B; M ++ N; (> L)) /\
      (dualD = D ^ ->
       dualC = ! dualD ->
       i |--- B ++ [D]; M; (> L) -> j |--- B; []; (>> ! dualD) -> |-- B; M; (> L)) /\
      (dualD = D ^ ->
       dualC = ! dualD ->
       ~ IsPositiveAtom D ->
       i |--- B ++ [D]; M; (>> P) -> j |--- B; []; (>> ! dualD) -> |-- B; M; (>> P)).
  
  Hypothesis TheoryIsFormula: forall P, theory P -> isFormula P.  
  
  Theorem AtomPerm j n w h P F L B:
    CutH w h -> S h = S n + j -> complexity P = w ->
    isFormulaL B -> isFormulaL L -> isNotAsyncL L -> isFormula P -> isFormula F ->
    IsPositiveAtom P -> j |--- B; []; (>> ! P ^) -> n |--- B ++ [P]; L; (>> F) -> |-- B; L; (> [F]).
  Proof with subst;auto;solveF.
    intros HC Hh Hc isFB isFL isNL isFP isFF isPAP Hj Hn.
    inversion isPAP...
    clear isFP isPAP.
    revert dependent B.
    revert dependent L.
    revert dependent F.
    revert dependent j.
    
    induction n; intros.
    * eapply AtomPerm0 with (P:=atom A) (j:=j)...
    *
      inversion Hn... (* 9 Cases *)
      ** (* Case 1 *)
        eapply tri_store'...
        eapply tri_dec1' with (F:=perp A0) (L':=[atom A0])...
        eapply tri_init1'.
      ** (* Case 2 *)
        apply in_app_or in H3.
        inversion H3...
        eapply tri_store'...
        eapply tri_dec1' with (F:=perp A0) (L':=[])...
        eapply tri_init2'...
        inversion Hj...
        apply seqNtoSeq in H4...
      ** (* Case 3 *)
        eapply tri_store'...
        eapply tri_dec1' with (F:=one) (L':=[])...
        eapply tri_one'.
      ** (* Case 4 *)
        assert(|-- B; M; (> [F0])).
        eapply IHn with (j:=S j) ...
        lia.
        inversion isFF...
        rewrite H1 in isFL.
        eapply ForallAppInv1. 
        exact isFL. 
        rewrite H1 in isFL.
        rewrite H1 in isNL.
        apply ForallAppInv1 in isNL...
        eapply HeightGeq. exact Hj. lia. 
        
        assert(|-- B; N; (> [G])).
        eapply IHn with (j:=S j)...
        lia.
        inversion isFF...
        rewrite H1 in isFL.
        eapply ForallAppInv2 in isFL... 
        rewrite H1 in isFL.
        rewrite H1 in isNL.
        apply ForallAppInv2 in isNL...
        eapply HeightGeq. exact Hj. lia. 
        
        assert(|-- B; M++N++[F0 ** G]; UP ([]++[])).
        apply InvTensor...
        
        rewrite H1 in isNL.
        apply ForallAppInv1 in isNL...
        
        rewrite H1 in isNL.
        apply ForallAppInv2 in isNL...
        
        rewrite H1 in isFL.
        eapply ForallAppInv1 in isFL... 
        rewrite H1 in isFL.
        eapply ForallAppInv2 in isFL...
        eapply tri_store'...
        refine (exchangeLC _ H3 ). 
        rewrite H1. perm.
      ** (* Case 5 *)
        assert(|-- B; L; (> [F0])).
        eapply IHn with (j:=S j)...
        lia.
        inversion isFF...
        eapply HeightGeq. exact Hj. lia. 
        
        assert(|-- B; L++[F0 op G]; UP ([]++[])).
        apply InvPlus...
        inversion isFF...
        simpl in H0.
        eapply tri_store'...
      ** (* Case 6 *)
        assert(|-- B; L; (> [G])).
        eapply IHn with (j:=S j)...
        lia.
        inversion isFF...
        eapply HeightGeq. exact Hj. lia. 
        
        assert(|-- B; L++[F0 op G]; UP ([]++[])).
        apply InvPlusComm...
        inversion isFF...
        simpl in H0.
        eapply tri_store'...
      ** (* Case 7 *)
        assert(
            S n |--- B ++ [atom A]; []; (> [F0]) ->
                                        j |--- B; []; (>> ! perp A) -> |-- B; []; (> [F0])).
        eapply HC  with (C:=? atom A) (dualC:=! perp A) (N:=[])...
        inversion isFF...
        eapply tri_store'...
        eapply tri_dec1' with (F:=! F0) (L':=[])...
        apply tri_bang'...
        apply H...
        eapply HeightGeq. exact H3. lia.
      ** (* Case 8 *)
        assert(
            S n |--- B ++ [atom A]; L; (> [F]) ->
                                       j |--- B; []; (>> ! perp A) -> |-- B; L; (> [F])).
        eapply HC with (C:=? atom A) (dualC:=! perp A) (N:=L)...

        apply H...
        eapply HeightGeq. exact H4. lia.
      ** (* Case 9 *)
        assert(|-- B; L; (> [FX t])).
        eapply IHn with (j:=S j)...
        lia.
        inversion isFF... 
        eapply HeightGeq. exact Hj. lia. 
        
        assert(|-- B; L++[E{ FX}]; UP ([]++[])).
        eapply InvEx with (t0:=t)...
        inversion isFF...
        
        simpl in H0.
        eapply tri_store'...    
  Qed.   
  

  (*
      Ltac solveAsyncL :=
        repeat
          match goal with
          | [ H1: isNotAsyncL ?M1, H2: isNotAsyncL ?M2 |- isNotAsyncL (?M1 ++ ?M2)] => 
            apply LPosApp;auto
          | [ H1: isNotAsyncL ?M1, H2: isNotAsyncL ?M2 |- isNotAsyncL (?M2 ++ ?M1)] => 
            apply LPosApp;auto
                            
          | [ H1: Permutation (?X ++ ?N) ?M, H2: isNotAsyncL ?M |- isNotAsyncL ?X] => 
            symmetry in H1; eapply LPos2;eauto
          | [ H1: Permutation ?M (?X ++ ?N), H2: isNotAsyncL ?M |- isNotAsyncL ?X] => 
            eapply LPos2;eauto   
          | [ H1: Permutation (?N ++ ?X) ?M, H2: isNotAsyncL ?M |- isNotAsyncL ?X] => 
            symmetry in H1; eapply LPos3;eauto
          | [ H1: Permutation ?M (?N ++ ?X), H2: isNotAsyncL ?M |- isNotAsyncL ?X] => 
            eapply LPos2;eauto 
          | [ H1: ~ asynchronous ?F, H2: isNotAsyncL ?M |- isNotAsyncL (?M ++ [?F]) ] => 
            eapply LPos3 with (M1:=[]) (L:=F::M)
          | [ H1: ~ asynchronous ?F, H2: isNotAsyncL ?M |- isNotAsyncL (?F :: ?M) ] => 
            split;auto 
          | [  |- Permutation ?M1 ?M2 ] => 
            perm                 
          end.
   *)


  Ltac solveIsFormL :=
    repeat
      match goal with
      | [ H1: isFormulaL (?F :: ?M'), H2: isFormulaL ?M |- isFormulaL (?M ++ [?F]) ] => 
        assert(Hp: Permutation (M ++ [F]) (F :: M) ) by perm;
        rewrite Hp;inversion H1;subst;apply ForallCons;auto     
      | [ H1: isFormulaL (?F :: ?M') |- isFormula ?F ] => 
        inversion H1;subst;auto  
      | [ H1: isFormulaL (?F :: ?M) |- isFormulaL (?F'::?M) ] => 
        inversion H1;subst;apply ForallCons;auto  
      | [ H1: isFormula ?F, H2: isFormulaL ?M |- isFormulaL (?F::?M) ] => 
        apply ForallCons;auto          
      | [ H1: isFormulaL (?F :: ?M) |- isFormulaL ?M ] => 
        inversion H1;subst;auto 
      | [ H1: isFormulaL ?M, H2: Permutation ?M ?M' |- _ ] => 
        rewrite H2 in H1;clear H2
      | [ H1: isFormulaL ?M, H2: Permutation ?M' ?M |- _ ] => 
        rewrite <- H2 in H1;clear H2         
      | [ H1: isFormulaL (?M++?N) |- isFormulaL ?M ] => 
        eapply ForallAppInv1;eauto  
      | [ H1: isFormulaL (?M++?N) |- isFormulaL ?N ] => 
        eapply ForallAppInv2;eauto                      
      | [ H1: In ?F ?B |- isFormula ?F ] => 
        apply isFormulaIn in H1;auto     
      end.


  Ltac solveFormLL :=
    try constructor;
    match goal with
    | [ H1: isFormula (AAnd ?A1 ?A2) |- isFormula ?A1 ] => 
      inversion H1;subst;auto
    | [ H1: isFormula (AAnd ?A1 ?A2) |- isFormula ?A2 ] => 
      inversion H1;subst;auto
    | [ H1: isFormula (MAnd ?A1 ?A2) |- isFormula ?A1 ] => 
      inversion H1;subst;auto
    | [ H1: isFormula (MAnd ?A1 ?A2) |- isFormula ?A2 ] => 
      inversion H1;subst;auto
    | [ H1: isFormula (AOr ?A1 ?A2) |- isFormula ?A1 ] => 
      inversion H1;subst;auto
    | [ H1: isFormula (AOr ?A1 ?A2) |- isFormula ?A2 ] => 
      inversion H1;subst;auto
    | [ H1: isFormula (MOr ?A1 ?A2) |- isFormula ?A1 ] => 
      inversion H1;subst;auto
    | [ H1: isFormula (MOr ?A1 ?A2) |- isFormula ?A2 ] => 
      inversion H1;subst;auto 
    | [ H1: isFormula (Bang ?A) |- isFormula ?A ] => 
      inversion H1;subst;auto   
    | [ H1: isFormula (Quest ?A) |- isFormula ?A ] => 
      inversion H1;subst;auto                                                           
    | [ H1: isFormula (F{ ?FX}) |- isFormula (?FX ?x) ] => 
      inversion H1;subst;auto
    | [ H1: isFormula (All ?A) |- isFormula (?A ?x) ] => 
      inversion H1;subst;auto 
    | [ H1: isFormula (Some ?A) |- isFormula (?A ?x) ] => 
      inversion H1;subst;auto          
    end.



  
  Theorem CutElimination i j C dualC D dualD B L M N P: 
    dualC = dual C -> isFormula C -> isFormula dualC ->
    isNotAsyncL M -> isNotAsyncL N -> 
    isFormulaL B -> isFormulaL M -> isFormulaL N -> isFormulaL L -> 
    isFormula P -> 
    
    (
      i |--- B; M++[C] ; DW P -> 
                         j |--- B; N ; DW dualC -> 
                                       |-- B; M++N ; DW P)
    /\
    (
      i |--- B; M++[C] ; UP L -> 
                         j |--- B; N ; DW dualC -> 
                                       |-- B; M++N ; UP L)
    /\
    (
      i |--- B; M ; UP (C::L) -> 
                    j |--- B; N ; DW dualC -> 
                                  |-- B; M++N ; UP L) 
    /\   
    (dualD = dual D -> dualC = (! dualD) ->
     i |--- B++[D]; M ; UP L -> 
                        j |--- B; [] ; DW (! dualD) -> 
                                       |-- B; M ; UP L) 
    /\
    (dualD = dual D -> dualC = (! dualD) ->
     ~ IsPositiveAtom D ->
     i |--- B++[D]; M ; DW P -> 
                        j |--- B; [] ; DW (! dualD) -> 
                                       |-- B; M ; DW P). 
  
  Proof with subst;auto;solveF.
    assert(exists w, complexity C = w).
    eexists; auto.
    destruct H as [w H].
    revert H.
    revert i j C dualC D dualD P B L M N.
    
    induction w using strongind;intros.
    - assert(complexity C > 0) by apply Complexity0.
      rewrite H in H10. inversion H10.
    - remember (plus i j) as h.
      revert dependent B.
      revert dependent L.
      revert dependent M.
      revert dependent N.
      revert dependent P.
      revert dependent dualD.
      
      revert D.
      revert dependent C.
      revert dependent dualC.
      
      revert dependent i.
      revert j.
      dependent induction h using strongind; intros.
      +
        symmetry in Heqh.
        apply plus_is_O in Heqh.
        destruct Heqh;subst.
        apply CutElimBase...
        
      +  

        rename H into CutW.
        rename H0 into CutH.
        rename H1 into compC.
        rename H3 into isFDC.
        rename H4 into isFC.
        rename H5 into isNAN.
        rename H6 into isNAM.
        rename H7 into isFM.
        rename H8 into isFN.
        rename H9 into isFL.
        rename H10 into isFP.
        rename H11 into isFB.
        move B at top.
        move M at top.
        move N at top.
        move L at top.
        move C at top.
        move D at top.
        move dualC at top.
        move dualD at top.
        move P at top.
        
        
        subst.
        
        split;[intros 
              |split;[intros 
                     |split;[intros 
                            |split;intros]]].
        * (** Dw Linear Cut *)  
          clear CutW. 
          inversion H... (* 9 cases *)
          ** (* DLCUT CASE 1 *) 
            symmetry in H4.
            apply app_eq_unit in H4.
            destruct H4.
            ***
              inversion H1...
              apply seqNtoSeq in H0;auto.
            ***
              inversion H1...
          ** (* DLCUT CASE 2 *) 
            symmetry in H1.
            apply app_eq_nil in H1.
            destruct H1...
          ** (* DLCUT CASE 3 *) 
            symmetry in H4.
            apply app_eq_nil in H4.
            destruct H4...   
          ** (* DLCUT CASE 4 *) 
            apply PProp_perm_sel in H2. 
            destruct H2.
            ***
              do 2 destruct H1.
              assert(
                  n |--- B; x ++ [C]; (>> F) ->
                                      j  |--- B; N; (>> dual C) ->
                                                    |-- B; x ++ N; (>> F)) as DLCut.
              
              eapply CutH;eauto.
              solveFormLL.
              rewrite <- H2 in isNAM. 
              eapply ForallAppInv1 in isNAM...
              solveIsFormL.
              eapply DLCut in H0;auto.
              eapply tri_tensor'.
              3:{
                apply seqNtoSeq in H7.
                exact H7. }
              2:{ exact H0. }
              rewrite <- H2; perm.
              eapply exchangeLCN;eauto.
            ***
              do 2 destruct H1.
              assert( n |--- B; x ++ [C]; (>> G) ->
                                          j |--- B; N; (>> dual C) ->
                                                       |-- B; x ++ N; (>> G)) as DLCut.
              
              eapply CutH;eauto.
              solveFormLL.
              rewrite <- H2 in isNAM. 
              eapply ForallAppInv2 in isNAM...
              
              solveIsFormL. 
              
              eapply DLCut in H0;auto.          
              eapply tri_tensor'.
              3:{ exact H0. }
              2:{
                apply seqNtoSeq in H3.
                exact H3. }
              rewrite <- H2; perm.
              eapply exchangeLCN;eauto.          
          ** (* DLCUT CASE 5 *) 
            assert(
                n   |--- B; M ++ [C]; (>> F) ->
                                      j  |--- B; N; (>> dual C) ->
                                                    |-- B; M ++ N; (>> F)) as DLCut.
            
            eapply CutH;eauto.
            solveFormLL.
            eapply tri_plus1'...
          ** (* DLCUT CASE 6 *) 
            assert(
                n   |--- B; M ++ [C]; (>> G) ->
                                      j  |--- B; N; (>> dual C) ->
                                                    |-- B; M ++ N; (>> G)) as DLCut.
            
            eapply CutH;eauto.
            solveFormLL.

            eapply tri_plus2'...       
          ** (* DLCUT CASE 7 *) 
            symmetry in H1.
            apply app_eq_nil in H1.
            destruct H1...       
          ** (* DLCUT CASE 8 *) 
            assert(
                n   |--- B; M ++ [C]; (> [P]) ->
                                      j  |--- B; N; (>> dual C) ->
                                                    |-- B; M ++ N; (> [P])) as ULCut.
            
            eapply CutH;eauto.
            apply ULCut in H0;auto.  
            eapply tri_rel';auto.
          ** (* DLCUT CASE 9 *) 
            assert(
                n   |--- B; M ++ [C]; (>> FX t) ->
                                      j  |--- B; N; (>> dual C) ->
                                                    |-- B; M ++ N; (>> FX t)) as DLCut.
            
            eapply CutH;eauto.
            solveFormLL.
            eapply tri_ex'...
        * (** Up Linear Cut *)   
          clear CutW.    
          inversion H... (* 10 cases *)
          ** (* ULCUT CASE 1 *)
            eapply tri_top'.
          ** (* ULCUT CASE 2 *)
            assert(
                n |--- B; M ++ [C]; (> M0) ->
                                    j |--- B; N; (>> dual C) ->
                                                 |-- B; M ++ N; > M0) as ULCut.
            eapply CutH;eauto.
            inversion isFL...
            eapply tri_bot'...
          ** (* ULCUT CASE 3 *) 
            assert(
                n |--- B; M ++ [C]; (> F :: G :: M0) ->
                                    j |--- B; N; (>> dual C) ->
                                                 |-- B; M ++ N; > F :: G :: M0) as ULCut.
            eapply CutH;eauto.  
            
            change (F :: G :: M0) with ([F ; G] ++ M0).
            apply ForallApp;inversion isFL...
            inversion H3...
            
            eapply tri_par'...
          ** (* ULCUT CASE 4 *) 
            assert(
                n |--- B; M ++ [C]; (> F :: M0) ->
                                    j |--- B; N; (>> dual C) ->
                                                 |-- B; M ++ N; > F :: M0) as ULCutF.
            eapply CutH;eauto.
            solveIsFormL.
            solveFormLL.      
            
            assert(
                n |--- B; M ++ [C]; (> G :: M0) ->
                                    j |--- B; N; (>> dual C) ->
                                                 |-- B; M ++ N; > G :: M0) as ULCutG.
            eapply CutH;eauto.
            solveIsFormL.
            solveFormLL.      
            
            eapply tri_with'...  
          ** (* ULCUT CASE 5 *)  
            assert(
                n |--- B++[F]; M ++ [C]; (> M0) ->
                                         j |--- B++[F]; N; (>> dual C) ->
                                                           |-- B++[F]; M ++ N; > M0) as ULCut.
            eapply CutH;eauto.
            solveIsFormL.
            assert(Permutation (B ++ [F]) (F :: B) ) by perm.
            rewrite H1.
            inversion isFL...
            
            change (F :: B) with ([F] ++ B).
            apply ForallApp;inversion H4...
            
            apply ULCut in H5;auto.
            
            eapply tri_quest';auto. 
            eapply weakeningGenN_rev;auto.   
          ** (* ULCUT CASE 6 *) 
            assert(
                n |--- B; (M ++ [F]) ++ [C]; (> M0) ->
                                             j |--- B; N; (>> dual C) ->
                                                          |-- B ; (M ++ [F]) ++ N; > M0) as ULCut.
            eapply CutH;eauto.
            apply LexpPosConc...
            
            solveIsFormL.
            solveIsFormL.
            
            apply ULCut in H0;auto.
            eapply tri_store';auto. 
            
            refine (exchangeLC _ H0);perm.  
            refine (exchangeLCN _ H6);perm.
          ** (* ULCUT CASE 7 *)  
            assert(Permutation (M ++ [C]) (C::M)) by
                apply perm_takeit_3.
            
            (* just double hyp *)
            assert(remove F (M ++ [C]) L') by auto.
            eapply Remove_Permutation_Ex in H4;eauto.
            destruct H4.    
            apply Remove_inv_cons in H4.
            destruct H4.
            ***
              inversion H4...
              clear H1 H4.
              assert(positiveFormula C \/ release C) as PosOrRel.
              apply PositiveOrRelease;auto.
              
              destruct PosOrRel as [HCPos | HCRel].           
              ****
                eapply PositiveDualRelease in HCPos;eauto.
                inversion H0;subst;try solve
                                       
                                       [match goal with
                                        | [ H: _ = (C ^), H': release (C ^) |- _ ] => 
                                          rewrite <- H in H'; inversion H'
                                        end].
                
                assert(
                    n0 |--- B; N ; (> [dual C]) ->
                                   S  n  |--- B; x; (>> C) ->
                                                    |-- B; N ++ x; (> [])) as UCut.
                
                eapply CutH;eauto;try omega.
                
                rewrite DualComplexity .
                rewrite <- ng_involutive;auto.
                apply ng_involutive.
                
                apply UCut in H10;auto.
                refine (exchangeLC _ H10);perm.
                
                apply Remove_Permute in H3;auto.
                rewrite perm_takeit_3 in H3.
                simpl in H3.
                apply Permutation_cons_inv in H3.
                refine (HeightGeqEx _ H7 _);auto.
              ****
                inversion H7;subst;try solve [inversion HCRel].
                
                assert(
                    S n0 |--- B; x ; (> [C]) ->
                                     j  |--- B; N; (>> dual C) ->
                                                   |-- B; x ++ N; (> [])) as UCut.
                
                eapply CutH;eauto.
                apply UCut in H0;auto.
                refine (HeightGeqEx _ H10 _); auto.
                
                apply Remove_Permute in H3;auto.
                rewrite perm_takeit_3 in H3.
                simpl in H3.
                apply Permutation_cons_inv in H3;auto.
            ***
              destruct H4.
              inversion H4...
              clear H1 H4.
              
              assert(
                  n |--- B; x0++[C] ; (>> F) ->
                                      j |--- B; N; (>> dual C) ->
                                                   |-- B; x0 ++ N; >> F) as DLCut.
              eapply CutH;eauto.
              
              apply Remove_Permute in H5;auto.

              solveIsFormL.
              apply Remove_Permute in H5;auto.
              
              change (F :: x0) with ([F] ++ x0) in H5.
              rewrite H5 in isNAM.
              apply ForallAppInv2 in isNAM... 
              apply Remove_Permute in H5;auto.
              
              solveIsFormL.
              
              apply DLCut in H0;auto.
              eapply tri_dec1' with (F0:=F);auto.
              2:{ exact H0. }
              apply Remove_app_tail;auto.

              apply Remove_Permute in H3;auto.
              apply Remove_Permute in H6;auto.
              
              eapply exchangeLCN;[ |exact H7]. 
              rewrite H6 in H3.
              replace (F :: x0) with ([F] ++ x0) in H3;auto.
              rewrite  app_normalize_1 in H3.
              apply Permutation_cons_inv in H3.
              exact (symmetry H3).
          ** (* ULCUT CASE 8 *)  
            assert(
                n |--- B; M ++ [C];  (>> F) ->
                                     j |--- B; N; (>> dual C) ->
                                                  |-- B; M ++ N; (>> F)) as DLCut.
            eapply CutH;eauto.
            
            solveIsFormL.
            
            apply DLCut in H0;auto.
            eapply tri_dec2' with (F0:=F);auto.
          ** (* ULCUT CASE 9 *) 
            assert(
                n |--- B; M ++ [C];  (>> F) ->
                                     j |--- B; N; (>> dual C) ->
                                                  |-- B; M ++ N; (>> F)) as DLCut.
            eapply CutH;eauto.
            
            apply DLCut in H0;auto.
            eapply tri_dec3' with (F0:=F);auto.
          ** (* ULCUT CASE 10 *)  
            apply tri_fx';auto;intros.
            assert(
                n |--- B; M ++ [C];  (> FX x :: M0) ->
                                     j |--- B; N; (>> dual C) ->
                                                  |-- B; M ++ N; (> FX x :: M0)) as DLCut.
            eapply CutH;eauto.
            
            solveIsFormL.
            solveFormLL.

            apply DLCut in H0;auto. 
            
        * (** Up Cut *)   
          inversion H... (* 7 cases *)
          ** (* UCUT CASE 1 *) 
            inversion H0...
          ** (* UCUT CASE 2 *) 
            inversion H0...
            ***
              rewrite app_nil_r.
              apply seqNtoSeq  in H5;auto.
            ***
              inversion H2.
          ** (* UCUT CASE 3 *) 
            
            inversion H0...
            ***
              inversion compC.
              remember(complexity F).
              assert(
                  n  |--- B; M; (> F :: G :: L) -> 
                                n0 |--- B; M0; (>> F ^) -> 
                                               |-- B; M ++ M0; (> G :: L)) as HcutF.
              
              eapply CutW with (m:=n1);eauto; try omega.
              
              solveFormLL.
              inversion isFDC...
              rewrite H3 in isNAN.
              apply ForallAppInv1 in isNAN...
              
              solveIsFormL.
              inversion isFC...
              
              apply HcutF in H5;auto.
              apply seqtoSeqN in H5.
              destruct H5.
              
              remember(complexity G).
              assert(
                  x |--- B; M ++ M0; (> G :: L) -> 
                                     n0 |--- B; N0; (>> G ^) -> 
                                                    |-- B; (M ++ M0) ++ N0; > L) as HcutG.

              eapply CutW with (m:=n2);auto;try omega.
              solveFormLL.
              inversion isFDC...
              rewrite H3 in isNAN.
              apply ForallAppInv1 in isNAN...
              apply ForallApp...
              rewrite H3 in isNAN.
              apply ForallAppInv2 in isNAN...
              
              rewrite H3 in isFN.
              apply ForallApp...
              eapply ForallAppInv1. exact isFN.
              rewrite H3 in isFN.
              eapply ForallAppInv2. exact isFN.
              
              apply HcutG in H1;auto.
              eapply exchangeLC;[ |exact H1].
              rewrite H3; perm.
              
          ** (* UCUT CASE 4 *) 
            inversion H0...
            ***     
              inversion compC.
              remember(complexity F).
              assert(
                  n  |--- B; M; (> F :: L) -> 
                                n0 |--- B; N; (>> F ^) -> 
                                              |-- B; M ++ N; (> L)) as HcutF.
              
              eapply CutW with (m:=n1);auto; try omega.
              solveFormLL.
              inversion isFDC...
              apply HcutF in H6;auto.
            ***  
              inversion compC.
              remember(complexity G).       
              assert(
                  n  |--- B; M; (> G :: L) -> 
                                n0 |--- B; N; (>> G ^) -> 
                                              |-- B; M ++ N; (> L)) as HcutG.
              
              eapply CutW with (m:=n1);auto; try omega.
              solveFormLL.
              inversion isFDC... 
              apply HcutG in H7;auto.
          ** (* UCUT CASE 5 *) 
            
            inversion H0...
            assert(
                n  |--- B++ [F]; M ; (> L) -> 
                                     S n0 |--- B; []; (>> ! F ^) -> 
                                                      |-- B; M ; (> L)) as UCCut.
            
            eapply CutH with (m:=h) (C:=? F) (dualC:=! F^);eauto. 
            
            apply UCCut in H5;auto.
            rewrite app_nil_r...
          **
            assert(
                n  |--- B; M ++ [C]; (> L) -> 
                                     j |--- B; N; (>> dual C) -> 
                                                  |-- B; M ++ N; (> L)) as ULCut.
            
            eapply CutH... 
            

            apply ULCut in H7;auto.
          **
            
            inversion H0...
            inversion isFC .
            inversion isFDC .
            inversion compC.
            assert(
                n  |--- B; M; (> (FX t :: L)) -> 
                              n0 |--- B; N; (>> (FX t) ^) -> 
                                            |-- B; M++N; (> L)) as HCut.
            
            eapply CutW with (m:=w);eauto.
            remember (VAR con 0).
            assert(proper e).
            rewrite Heqe. auto with Ext_Eq. 
            constructor.
            rewrite <- H13.
            eapply ComplexityUniformEq...
            
            apply HCut;auto. 
        * (** Up Classic Cut *)   
          inversion H1... (* 10 Cases *)  
          ** (* UCCUT CASE 1 *) 
            eapply tri_top'.
          ** (* UCCUT CASE 2 *)          
            assert(
                n |--- B ++ [D]; M ; (> M0) -> 
                                     j |--- B; []; (>> ! dual D) ->
                                                   |-- B; M ; > M0) as UCCut.
            eapply CutH with (C:=C) (dualC:=dual C) ;eauto.
            solveIsFormL.
            eapply tri_bot'...
          ** (* UCCUT CASE 3 *)           
            assert(
                n |--- B ++ [D]; M ; (> F :: G :: M0) -> 
                                     j |--- B; []; (>> ! dual D) ->
                                                   |-- B; M ; > F :: G :: M0) as UCCut.
            eapply CutH with (C:=C) (dualC:=dual C);eauto. 
            inversion isFL...
            inversion H4...
            eapply tri_par'...     
          ** (* UCCUT CASE 4 *)           
            assert(
                n |--- B ++ [D]; M ; (> F :: M0) -> 
                                     j |--- B; []; (>> ! dual D) ->
                                                   |-- B; M ; > F :: M0) as UCCutF.
            eapply CutH with (C:=C) (dualC:=dual C);eauto. 
            inversion isFL...
            inversion H5...
            assert(
                n |--- B ++ [D]; M ; (> G :: M0) -> 
                                     j |--- B; []; (>> ! dual D) ->
                                                   |-- B; M ; > G :: M0) as UCCutG.
            eapply CutH with (C:=C) (dualC:=dual C);eauto.  
            inversion isFL...
            inversion H5...
            eapply tri_with'...   
          ** (* UCCUT CASE 5 *)           
            assert(
                n |--- (B ++ [F]) ++ [D]; M ; (> M0) -> 
                                              j |--- B ++ [F]; []; (>> ! dual D) ->
                                                                   |-- B ++ [F]; M ; > M0) as UCCut.
            eapply CutH with (C:=C) (dualC:=dual C);eauto. 
            solveIsFormL.
            inversion isFL...
            inversion H4...
            apply ForallApp...
            assert(n |--- (B ++ [F]) ++ [D]; M; (> M0)).
            refine (exchangeCCN _ H7);perm. 
            
            apply UCCut in H;auto.
            eapply tri_quest';auto.
            eapply weakeningGenN_rev;auto.   
          ** (* UCCUT CASE 6 *)          
            assert(
                n |--- B ++ [D]; M ++ [F] ; (> M0) -> 
                                            j |--- B ; []; (>> ! dual D) ->
                                                           |-- B ; M ++ [F] ; > M0) as UCCut.
            eapply CutH with (C:=C) (dualC:=dual C);eauto.
            apply LexpPosConc...
            inversion isFL...
            
            apply ForallApp...
            inversion isFL...
            eapply tri_store'...
          ** (* UCCUT CASE 7 *) 
            destruct(PositiveAtomDec D).
            inversion H...
            assert(isFormulaL(F :: L')).
            
            
            apply Remove_Permute in H5;auto.
            rewrite <- H5;auto.
            inversion H3...
            assert(isNotAsyncL L').
            apply Remove_Permute in H5;auto.
            rewrite H5 in isNAM.
            inversion isNAM...
            
            (** Atomic Permutation *)
            assert(|-- B; L'; (> [F])).
            
            eapply AtomPerm with (P:=atom A) (j:=j) (n:=n) (h:=h) (w:=1)...
            unfold CutElimination.CutH; intros.   
            eapply CutH with (m:=m);try assumption.
            
            rewrite DualComplexity  in compC.
            rewrite H0 in compC.
            inversion compC... 
            
            destruct(PositiveOrRelease F).
            inversion H7;subst;try solve [inversion H11].
            apply Remove_Permute in H5...
            eapply exchangeLC.
            2:{ exact H17. }
            rewrite H5. perm.
            
            assert
              (
                n |--- B ++ [atom A]; L'; (> [F]) ->
                                          j |--- B; []; (>> ! perp A) -> |-- B; L'; (> [F])).
            eapply CutH with (C:=C) (dualC:=dual C) (N:=L')...
            solveIsFormL.
            
            eapply tri_dec1' with (F0:=F).
            exact H4. exact H5.
            eapply tri_rel'...
            
            
            
            assert
              (
                n |--- B ++ [D]; L'; (>> F) ->
                                     j |--- B; []; (>> ! dual D) -> |-- B; L'; (>> F)).
            eapply CutH with (C:=C) (dualC:=dual C);eauto...
            apply Remove_Permute in H5;auto.
            solveIsFormL.
            apply Remove_Permute in H5;auto.
            rewrite H5 in isNAM.
            inversion isNAM...
            apply Remove_Permute in H5;auto.
            solveIsFormL.
            eapply tri_dec1' with (F0:=F)...
            
          ** apply in_app_or in H5.
             inversion H5...
             
             destruct(PositiveAtomDec D).
             inversion H3...
             
             clear H3 H5.
             (** Atomic Permutation *)
             assert(|-- B; M; (> [F])).
             eapply AtomPerm with (P:=atom A) (j:=j) (n:=n) (h:=h) (w:=1)...
             unfold CutElimination.CutH; intros.   
             eapply CutH with (m:=m);try assumption.
             
             rewrite DualComplexity  in compC.
             rewrite H0 in compC.
             inversion compC...
             solveIsFormL.
             eapply @AbsorptionClassic with (F:=F)...
             apply isFormulaIn in H;auto.
             ---
               assert
                 (
                   n |--- B ++ [D]; M; (>> F) ->
                                       j |--- B; []; (>> ! dual D) -> |-- B; M; (>> F)).
               eapply CutH with (C:=C) (dualC:=dual C);eauto...
               apply isFormulaIn in H;auto.
               solveIsFormL.
               eapply tri_dec2' with (F0:=F)...
             ---
               subst.
               inversion H2...
               assert(
                   n |--- B ++ [F]; M ; (>> F) -> 
                                        S n0 |--- B ; []; (>> ! dual F) ->
                                                          |-- B ; M ; >> F) as DCCut.
               eapply CutH with (C:=C) (dualC:=dual C);eauto.
               
               rewrite H0 in isFDC.
               inversion isFDC...
               assert((? F) ^ = ! F ^).
               simpl. reflexivity.
               assert(C = ? F). 
               rewrite ng_involutive.
               
               rewrite H.
               rewrite <- H0.
               rewrite <- ng_involutive;auto.
               
               rewrite H6 in isFC.
               inversion isFC...

               assert (|-- B; M; (>> F)). 
               apply DCCut...
               apply seqtoSeqN in H.
               destruct H.
               assert(
                   n0 |--- B; [] ; (> [dual F]) -> 
                                   x |--- B ; M; (>> F) ->
                                                 |-- B ; M ; > []) as UCut.
               eapply CutW;eauto... 
               
               assert((? F) ^ = ! F ^).
               simpl. reflexivity.
               assert(C = ? F). 
               rewrite ng_involutive.
               
               rewrite H3.
               rewrite <- H0.
               rewrite <- ng_involutive;auto.
               
               
               rewrite H6 in compC.
               inversion compC...
               symmetry.
               apply DualComplexity.
               
               apply ng_involutive.
               
               
               rewrite H0 in isFDC.
               inversion isFDC...
               assert((? F) ^ = ! F ^).
               simpl. reflexivity.
               assert(C = ? F). 
               rewrite ng_involutive.
               
               rewrite H3.
               rewrite <- H0.
               rewrite <- ng_involutive;auto.
               
               rewrite H6 in isFC.
               inversion isFC...
               apply Forall_forall;intros y Hy; inversion Hy.
               apply UCut...
               
               
          **
            destruct(PositiveAtomDec D).
            inversion H...
            
            clear H.
            (** Atomic Permutation *)
            assert(|-- B; M; (> [F])).
            eapply AtomPerm with (P:=atom A) (j:=j) (n:=n) (h:=h) (w:=1)...
            unfold CutElimination.CutH; intros.   
            eapply CutH with (m:=m);try assumption.
            
            rewrite DualComplexity  in compC.
            rewrite H0 in compC.
            inversion compC... 
            

            ***
              destruct(NegativeAtomDec F).
              2:{ eapply AbsorptionTheory;eauto.
              }
              
              inversion H3...
              inversion H9...
              eapply tri_dec3'.
              exact H4. exact H5.
              eapply tri_init1'.
              apply in_app_or in H11.
              
              inversion H11...
              eapply tri_dec3'.
              exact H4. exact H5.
              eapply tri_init2'...
              inversion H...

              apply seqtoSeqN in H14.
              destruct H14.
              apply AbsorptionAtom in H6...
              apply seqNtoSeq in H6...
            ***
              assert
                (
                  n |--- B ++ [D]; M; (>> F) ->
                                      j |--- B; []; (>> ! dual D) -> |-- B; M; (>> F)).
              eapply CutH with (C:=C) (dualC:=dual C);eauto...
              eapply tri_dec3' with (F0:=F)...
          **
            eapply tri_fx';auto;intros.
            assert(
                n |--- B ++ [D]; M ; (> FX x :: M0) -> 
                                     j |--- B ; []; (>> ! dual D) ->
                                                    |-- B; M; (> FX x :: M0)) as DCCut.
            eapply CutH with (C:=C) (dualC:=dual C);eauto...
            inversion isFL...
            inversion H6...
            solveIsFormL.
            apply DCCut... 
        * (** Dw Classic Cut *)   
          inversion H2... (* 9 Cases *)  
          **
            apply tri_init1'.
          **
            apply in_app_or in H8. 
            inversion H8...
            apply tri_init2'...
            subst.
            assert(IsPositiveAtom (atom A)) by constructor.
            contradiction. 
          **
            eapply tri_one'.
          **
            clear CutW.
            assert(
                n |--- B ++ [D]; M0; (>> F) -> 
                                     j |--- B; []; (>> ! dual D) ->
                                                   |-- B; M0 ; >> F) as DCCutF.
            eapply CutH with (C:=C) (dualC:=dual C) ;eauto... 
            solveFormLL.
            rewrite H5 in isNAM.
            apply ForallAppInv1 in isNAM...
            solveIsFormL.
            
            assert(
                n |--- B ++ [D]; N0; (>> G) -> 
                                     j |--- B; []; (>> ! dual D) ->
                                                   |-- B; N0 ; >> G) as DCCutG.
            eapply CutH with (C:=C) (dualC:=dual C) ;eauto... 
            solveFormLL.
            rewrite H5 in isNAM.
            apply ForallAppInv2 in isNAM...
            
            solveIsFormL.
            apply DCCutF in H6;auto.
            apply DCCutG in H10;auto.
            
            refine(tri_tensor' H5 H6 H10). 
            
          **          
            assert(
                n |--- B ++ [D]; M; (>> F) -> 
                                    j |--- B; []; (>> ! dual D) ->
                                                  |-- B; M ; >> F) as DCCut.
            eapply CutH with (C:=C) (dualC:=dual C) ;eauto.
            solveFormLL.
            eapply tri_plus1'...    
          **          
            assert(
                n |--- B ++ [D]; M; (>> G) -> 
                                    j |--- B; []; (>> ! dual D) ->
                                                  |-- B; M ; >> G) as DCCut.
            eapply CutH with (C:=C) (dualC:=dual C) ;eauto. 
            solveFormLL.
            eapply tri_plus2'...  
          **          
            assert(
                n |--- B ++ [D]; []; (> [F]) -> 
                                     j |--- B; []; (>> ! dual D) ->
                                                   |-- B; [] ; > [F]) as UCCut.
            
            eapply CutH with (C:=C) (dualC:=dual C) ;eauto.
            inversion isFP... 
            solveIsFormL. 
            
            eapply tri_bang'...  
          **         
            assert(
                n |--- B ++ [D]; M; (> [P]) -> 
                                    j |--- B; []; (>> ! dual D) ->
                                                  |-- B; M ; > [P]) as UCCut.
            
            eapply CutH with (C:=C) (dualC:=dual C) ;eauto.
            eapply tri_rel'...  
          **
            
            assert(
                n |--- B ++ [D]; M ; (>> FX t) -> 
                                     j |--- B ; []; (>> ! dual D) ->
                                                    |-- B ; M ; (>> FX t)) as DCCut.
            eapply CutH with (C:=C) (dualC:=dual C);eauto.
            inversion isFP...
            
            
            eapply tri_ex'...

  Qed.        
  
  Theorem GeneralCut i j C dualC B L M N: 
    dualC = dual C -> isFormula C -> isFormula (dualC) ->
    isNotAsyncL M -> isNotAsyncL N -> 
    isFormulaL B -> isFormulaL M -> isFormulaL N -> isFormulaL L -> 
    (i |--- B; M ; UP (C::L) -> 
                   j |--- B; N ; DW dualC -> 
                                 |-- B; M++N ; UP L).
  Proof with subst;auto.
    intros. 
    assert(exists w, complexity C = w). 
    eexists; auto.
    destruct H10 as [w H10].
    specialize CutElimination;intros.
    assert((i |--- B; M ; UP (C::L) -> 
                          j |--- B; N ; DW dualC -> 
                                        |-- B; M++N ; UP L)) as CUT.
    eapply H11;eauto.
    apply CUT;auto.
  Qed.
  
  Theorem GeneralCut' :   
    forall (C dualC : oo) (B L M N : list oo),
      dualC = C ^ ->
      isFormula C ->
      isFormula dualC ->
      isNotAsyncL M ->
      isNotAsyncL N ->
      isFormulaL B ->
      isFormulaL M ->
      isFormulaL N -> isFormulaL L ->
      (|-- B ; M ; (> C :: L)) ->
      (|-- B ; N ;  (>> dualC)) ->
      |-- B ;  (M ++ N) ; (> L).
    intros.
    apply seqtoSeqN in H8.
    apply seqtoSeqN in H9.
    CleanContext.
    eapply GeneralCut with (C:= C) (dualC := C ^);eauto.
  Qed.



  Theorem CutAndreoli i j C dualC B M N: 
    dualC = dual C -> isFormula C -> isFormula (dualC) ->
    isNotAsyncL M -> isNotAsyncL N -> 
    isFormulaL B -> isFormulaL M -> isFormulaL N ->     
    (i |--- B; M ; DW C -> 
                   j |--- B; N ; DW dualC -> 
                                 |-- B; M++N ; UP []).
  Proof with subst;auto.
    intros.
    assert(exists w, complexity C = w). 
    eexists; auto.
    destruct H9 as [w H9].
    
    destruct(PositiveOrRelease C).  
    -
      eapply PositiveDualRelease in H10;eauto.
      rewrite H in H8.
      inversion H8;subst;
        try solve[
              match goal with
              | [H : _ = C ^ |- _] => rewrite <- H in H10;inversion H10
              end].
      eapply exchangeLC with (LC:=N++M). perm.  
      eapply GeneralCut; try assumption.
      2:{ exact H1. }
      2:{ exact H0. }
      apply ng_involutive.
      
      apply Forall_forall;intros x Hx. 
      inversion Hx... 
      exact H16.
      exact H7.
    -
      inversion H7;subst; try solve [inversion H10].
      eapply GeneralCut; try assumption.
      2:{ exact H0. }
      2:{ exact H1. }
      reflexivity.
      apply Forall_forall;intros x Hx. 
      inversion Hx... 
      exact H16.
      exact H8.
  Qed.
End CutElimination.
