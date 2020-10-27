(** * System LM: Natural deduction and sequent calculus

In this file we encode the logical rules of natural deduction and
sequent calculus for minimal logic. Then, using the
cut-elimination theorem of LL we prove the relative completeness of
these systems
 *)

Require Import FLL.SL.CutElimination.
Require Export FLL.OL.OLCutElimTheoremPOS.
Require Export FLL.OL.OLDefinitions.
Require Import Coq.Init.Nat.
Require Import FLL.Misc.Permutations.


Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
Hint Resolve proper_APP uniform_proper : hybrid.
Hint Unfold proper: hybrid.
Hint Rewrite ext_eq_eta : hybrid.
Hint Resolve uniform_id uniform_con uniform_app : hybrid.
(* Hint Resolve proper_Var : hybrid. *)
Hint Resolve lbindEq exprInhabited : hybrid.



(** ** Syntax *)
(* No constants *)
Inductive Constants := .
(* Only implication *)
Inductive Connectives := IMPL | CONJ  .
(* Universal quantifier *)
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


(** Definition for Elimination and introduction rules of implication,
conjunction and universal quantification in natural deduction *)
Definition IMP_ELIMINATION F G:= ((perp (up G)) ** (! atom (up F)) ** (! atom (up (t_bin IMPL F G))) ).
Definition IMP_INTRO F G := ( ( perp ( up  ( t_bin IMPL F G))) ** ( ! (atom (up F)) -o (atom (up G )) )).
Definition CONJ_ELIMINATION F G :=  ( (perp (up F)) op  (perp (up G)) ) ** (! atom (up (t_bin CONJ F G))) .
Definition CONJ_INTRO F G := (perp (up (t_bin CONJ F G))) ** (  (atom (up F)) & (atom (up G))) .
Definition ALL_ELIMINATION FX := E{ fun t => (perp ( up (FX t))) ** (! atom (up( t_quant ALL FX)))}.
Definition ALL_INTRO FX  := (perp (up ( t_quant ALL FX))) ** F{ fun t => atom (up (FX t))}.

(** Natural deduction system *)
Inductive NM : oo -> Prop :=
| IMP_I : forall F G, isOLFormula F -> isOLFormula G ->
                      NM (IMP_INTRO F G)
| IMP_E : forall F G, isOLFormula F -> isOLFormula G ->
                      NM (IMP_ELIMINATION F G)
| CONJ_I : forall F G, isOLFormula F -> isOLFormula G ->
                       NM (CONJ_INTRO F G)
| CONJ_E : forall F G, isOLFormula F -> isOLFormula G ->
                       NM (CONJ_ELIMINATION F G)
| ALL_I : forall FX, uniform FX -> (forall t, proper t -> isOLFormula (FX t)) ->
                     NM (ALL_INTRO FX)
| ALL_E : forall FX , uniform FX -> (forall t, proper t -> isOLFormula (FX t)) ->
                      NM (ALL_ELIMINATION FX ).


(** Right and left rules for implication, conjunction 
and universal quantification  in sequent calculus *)

Definition IMP_RIGHT F G :=  (perp (up (t_bin IMPL F G))) ** ( (? atom (down F)) $ (atom (up G))).
Definition IMP_LEFT F G := ( (perp (down (t_bin IMPL F G))) ** ( ! (atom (up F)) ** (? atom (down G)) )).
Definition CONJ_RIGHT F G := (perp (up (t_bin CONJ F G)))  ** ( (atom (up F)) & (atom (up G)) ).
Definition CONJ_LEFT F G := (perp (down (t_bin CONJ F G))) **  ( ?(atom (down F)) op ?(atom (down G)) ).
Definition ALL_RIGHT FX := (perp (up (t_quant ALL FX))) ** F{ fun t => atom (up (FX t))}.
Definition ALL_LEFT FX := (perp (down (t_quant ALL FX))) ** E{ fun t => ? atom (down (FX t))}.

Inductive SEQ : oo -> Prop :=
| IMP_R : forall F G, isOLFormula F -> isOLFormula G ->
                      SEQ (IMP_RIGHT F G)
| IMP_L : forall F G, isOLFormula F -> isOLFormula G ->
                      SEQ (IMP_LEFT F G)
| CONJ_R : forall F G, isOLFormula F -> isOLFormula G ->
                       SEQ (CONJ_RIGHT F G)
| CONJ_L : forall F G, isOLFormula F -> isOLFormula G ->
                       SEQ (CONJ_LEFT F G)
| ALL_R : forall FX, uniform FX-> (forall t, proper t -> isOLFormula (FX t)) ->
                     SEQ (ALL_RIGHT FX)
| ALL_L : forall FX, uniform FX -> (forall t, proper t -> isOLFormula (FX t)) ->
                     SEQ (ALL_LEFT FX)
.

(** Sequent and natural deduction systems with the structural rules *)
Inductive NMSTR : oo -> Prop :=
| nm_rl : forall F, NM F -> NMSTR F
| nm_str: forall F, StrRulesPos F -> NMSTR F.

Inductive SEQSTR : oo -> Prop :=
| sq_rl : forall F, SEQ F -> SEQSTR F
| sq_str: forall F, StrRulesPos F -> SEQSTR F.

(*!! MOVE THIS *)
Inductive StrRulesPOS : oo -> Prop :=
| stp_cut : forall F, isOLFormula F -> StrRulesPOS (RCUTPOS F)
| stp_init : forall F, isOLFormula F -> StrRulesPOS (RINIT F)
.


Inductive NMSTRPOS : oo -> Prop :=
| nm_rlP : forall F, NM F -> NMSTRPOS F
| np_cutP : forall F, StrRulesPOS F ->   NMSTRPOS F
.

Inductive SEQSTRPOS : oo -> Prop :=
| sq_rlP : forall F, SEQ F -> SEQSTRPOS F
| sq_cutP : forall F, StrRulesPOS F -> SEQSTRPOS F
.
                                    
Hint Constructors StrRulesPos NM SEQ NMSTR SEQSTR  : core.
Hint Constructors NMSTRPOS SEQSTRPOS : core.
Hint Unfold IMP_ELIMINATION IMP_INTRO  IMP_RIGHT IMP_LEFT POS RCUT RINIT CONJ_ELIMINATION CONJ_INTRO  CONJ_RIGHT CONJ_LEFT : core .
Hint Unfold ALL_ELIMINATION ALL_INTRO  ALL_RIGHT ALL_LEFT  : core.

Hint Constructors StrRulesPOS.
Definition down' : uexp -> atm := down.
Definition up' : uexp -> atm := up.
Hint Unfold down' up' : core .

Hint Constructors isFormula : core.

Theorem UniformElim : forall FX, uniform FX -> uniform (fun _ : uexp => APP (CON (oo_q ALL)) (lambda FX)).
  intros.
  apply uniform_app.
  apply uniform_con.
  apply proper_uniform.
  apply uniform_proper; auto.
Qed.

Ltac SolveIsFormulas' := SolveIsFormulas ; solveUniform ; eauto using UniformElim.

Theorem NMStrRulesFormulas : forall F,  NMSTR F -> isFormula F.
  intros.
  inversion H;subst;auto.
  inversion H0;subst;SolveIsFormulas'.
  inversion H0;subst;SolveIsFormulas'.
Qed.

Theorem SeqStrRulesFormulas : forall F,  SEQSTR F -> isFormula F.
  intros.
  inversion H;subst;auto.
  inversion H0;subst ;SolveIsFormulas'.
  inversion H0;subst;SolveIsFormulas.
Qed.

(** Proving dualities beween Left (resp. right) introduction rules in 
sequent calculus and Elimination (resp. Introduction) rules in 
Natural Deduction *)
Hint Unfold POS.
Theorem ImplLeftElimination1 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPos [] [] (> [ (IMP_LEFT F G) ^ ; (IMP_ELIMINATION F G)])).
Proof with SolveIsFormulas;solveF.
  intros F G isF isG; autounfold;simpl;solveLL'.
  ExchangeFront' 3.
  decide3' (POS ( t_bin IMPL F G))...
  tensor' [d| t_bin IMPL F G | ] [(u^| G | ** (! u| F |)) ** (! u| t_bin IMPL F G |);  ! d^| G |] .
  simpl.
  decide3' (RCUT G).
  tensor'  [(u^| G | ** (! u| F |)) ** (! u| t_bin IMPL F G |) ] [! d^| G |].
  decide1' ((u^| G | ** (! u| F |)) ** (! u| t_bin IMPL F G |)).
  tensor' [u| G |] (@nil oo).
  tensor' [u| G |] (@nil oo).
  decide2' (u^| F |).
  decide3' (RINIT ( t_bin IMPL F G)).
  tensor' [u| t_bin IMPL F G |] (@nil oo)...

  decide3' (POS G).
  tensor' [d| G |] [! d^| G |]. simpl.
  decide1' (! d^| G|).
  solveLL'...
  decide1' (d^| G|)...
  solveLL'...
Qed.

Theorem ImplLeftElimination2 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPOS [] [] (> [ (IMP_ELIMINATION F G) ^ ; (IMP_LEFT F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL'.
  decide3' (RCUTPOS (t_bin IMPL F G))...
  tensor'   [u| G |; d^| t_bin IMPL F G | ** ((! u| F |) ** (? d| G |))] (@nil oo);simpl.
  decide1' (d^| t_bin IMPL F G | ** ((! u| F |) ** (? d| G |))).
  tensor' (@nil oo) [u| G |].
  right...
  tensor' (@nil oo) [u| G |].
  decide2' (u^|F|).
  simpl.
  decide3'( RINIT (G))...
  tensor'  [u| G |] (@nil oo).
  right ...
  decide2' (u^| t_bin IMPL F G |).
Qed.



Theorem ImplRightIntroduction1 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPos [] [] (> [ (IMP_RIGHT F G) ^ ; (IMP_INTRO F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL'.
  decide1' (u^| t_bin IMPL F G | ** ((? u^| F |) $ u| G |))...
  tensor' [u| t_bin IMPL F G |] [ (! d^| F |) ** u^| G |].
  decide1' ((! d^| F |) ** u^| G |).
  tensor' (@nil oo) [u| G |].
  decide3' (RCUT F).
  tensor' (@nil oo) [d^| F |].
  decide2' (u^| F |).
Qed.

Theorem ImplRightIntroduction2 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPOS [] [] (> [ (IMP_INTRO F G) ^ ; (IMP_RIGHT F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL'.
  decide1' (u^| t_bin IMPL F G | ** ((? d| F |) $ u| G |)).
  tensor'  [u| t_bin IMPL F G |][ (! u| F |) ** u^| G |].
  decide1' ((! u| F |) ** u^| G |).
  tensor' (@nil oo)  [u| G |].
  decide3' (RINIT F).
  tensor'  [u| F |] (@nil oo) ...
Qed.


Theorem ConjLeftElimination1 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPos [] [] (> [ (CONJ_LEFT F G) ^ ; (CONJ_ELIMINATION F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL'.
  + decide3' (RCUT F).
    tensor'  [d| t_bin CONJ F G |; (u^| F | op u^| G |) ** (! u| t_bin CONJ F G |)] [! d^| F |].
    decide3' (POS (t_bin CONJ F G)).
    tensor' [d| t_bin CONJ F G |][ (u^| F | op u^| G |) ** (! u| t_bin CONJ F G |); u| F |] ...
    decide1' ((u^| F | op u^| G |) ** (! u| t_bin CONJ F G |)).
    tensor' [ u| F |]  (@nil oo).
    decide3' (RINIT (t_bin CONJ F G)).
    tensor' [u| t_bin CONJ F G |] (@nil oo)...
    decide3' (POS F).
    tensor' [ d| F |][! d^| F |]...
    decide1' (! d^| F |)...
    solveLL'.
    decide1' ( d^| F |);solveLL'...
  + decide3' (POS (t_bin CONJ F G)).
    tensor'  [d| t_bin CONJ F G |][ ! d^| G |; (u^| F | op u^| G |) ** (! u| t_bin CONJ F G |)]...
    decide3' (RCUT G).
    tensor' [(u^| F | op u^| G |) ** (! u| t_bin CONJ F G |)] [! d^| G |].
    decide1' ((u^| F | op u^| G |) ** (! u| t_bin CONJ F G |)).
    tensor' [u| G |] (@nil oo).
    decide3' (RINIT (t_bin CONJ F G)).
    tensor' [u| t_bin CONJ F G |] (@nil oo)...
    decide3' (POS G).
    tensor' [d| G |] [! d^| G |]...
    decide1' (! d^| G |)...
    solveLL'.
    decide1' ( d^| G |)...
    solveLL'...
Qed.

Theorem ConjLeftElimination2 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPOS [] [] (> [ (CONJ_ELIMINATION F G) ^ ; (CONJ_LEFT F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL'.
  + decide3' (RCUTPOS ( t_bin CONJ F G)).
    tensor'  [u| F |; d^| t_bin CONJ F G | ** ((? d| F |) op (? d| G |))] (@nil oo)...
    decide1' (d^| t_bin CONJ F G | ** ((? d| F |) op (? d| G |))).
    tensor' (@nil oo) [u| F |]...
    oplus1'...
    decide3' (RINIT F).
    tensor' ([u| F |]) (@nil oo)...
    decide2' (u^| t_bin CONJ F G |).
  +  decide3' (RCUTPOS ( t_bin CONJ F G)).
     tensor' [u| G |; d^| t_bin CONJ F G | ** ((? d| F |) op (? d| G |))] (@nil oo)...
     decide1' (d^| t_bin CONJ F G | ** ((? d| F |) op (? d| G |))).
     tensor' (@nil oo) [u| G |]...
     oplus2'...
     decide3' (RINIT G).
    tensor' ([u| G |]) (@nil oo)...
    decide2' (u^| t_bin CONJ F G |).
Qed.


Theorem ConjRightIntroduction1 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPos [] [] (> [ (CONJ_RIGHT F G) ^ ; (CONJ_INTRO F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL'.
  decide1' (perp (up (t_bin CONJ F G)) ** (atom (up F) & atom (up G))).
  tensor' [atom (up (t_bin CONJ F G)) ] [perp (up F) op perp (up G)].
  decide1' (perp (up F) op perp (up G)).
  decide1' (perp (up F) op perp (up G)).
Qed.

Theorem ConjRightIntroduction2 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPOS [] [] (> [ (CONJ_INTRO F G) ^ ; (CONJ_RIGHT F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL'.
  decide1' ( u^| t_bin CONJ F G | ** (u| F | & u| G |)).
  tensor' [u| t_bin CONJ F G |][ u^| F | op u^| G |].
  decide1' (u^| F | op u^| G |).
  decide1' (u^| F | op u^| G |).
Qed.


Theorem AllLeftElimination1 : forall FX, uniform FX ->  (forall x, proper x -> isOLFormula( FX x)) ->
                                         (seq StrRulesPos [] [] (> [ (ALL_LEFT FX) ^ ; (ALL_ELIMINATION FX)])).
Proof with SolveIsFormulas'.
  intros FX  isFX isFXt; autounfold;simpl;solveLL'.
  decide3' (POS ( t_quant ALL FX)).
  tensor' [d| t_quant ALL FX |][ ! d^| FX x |; E{ fun t  => u^| FX t | ** (! u| t_quant ALL FX |)}]...
  decide3' (RCUT (FX x)).
  tensor' [ E{ fun t  => u^| FX t | ** (! u| t_quant ALL FX |)}] [! d^| FX x |]...
  decide1' (E{ fun t => u^| FX t | ** (! u| t_quant ALL FX |)}).
  existential' x...
  tensor'  [u| FX x |] (@nil oo).
  decide3' (RINIT (t_quant ALL FX)).
  tensor'  [u| t_quant ALL FX |] (@nil oo)...
  decide3' (POS (FX x)).
  tensor' [ d| FX x |] [! d^| FX x |]...
  decide1' (! d^| FX x |)...
  solveLL'.
  decide1' (d^| FX x |)...
  solveLL'...
Qed. 
  

Theorem AllLeftElimination2 : forall FX, uniform FX ->  (forall x, proper x -> isOLFormula( FX x)) ->
                                         (seq StrRulesPOS [] [] (> [ (ALL_ELIMINATION FX) ^ ; (ALL_LEFT FX)])).
Proof with SolveIsFormulas'.
  intros FX  isFX isFXt; autounfold;simpl.
  apply tri_fx'...
  intros.
  solveLL'.
  decide3'( RCUTPOS ( t_quant ALL FX)).
  tensor' [u| FX x |; d^| t_quant ALL FX | ** E{ fun t => ? d| FX t |}] (@nil oo) ...
  decide1' (d^| t_quant ALL FX | ** E{ fun t => ? d| FX t |}).
  tensor' (@nil oo)  [u| FX x |]...
  existential' x...
  decide3' (RINIT (FX x))...
  tensor'  [u| FX x |] (@nil oo)...
  decide2' (u^| t_quant ALL FX |).
Qed.

Theorem AllRightIntroduction1 : forall FX, uniform FX ->  (forall x, proper x -> isOLFormula( FX x)) ->
                                           (seq StrRulesPos [] [] (> [ (ALL_RIGHT FX) ^ ; (ALL_INTRO FX)])).
Proof with SolveIsFormulas.
  intros FX  isFX isFXt; autounfold;simpl.
  solveLL'.
  decide1' (perp (up (t_quant ALL FX)) ** F{ fun t=> atom (up (FX t))}).
  tensor'  [atom (up (t_quant ALL FX))] [E{ fun x => perp (up (FX x))}].
  solveLL'.
  decide1' (E{ fun x0 => perp (up (FX x0))}).
  existential' x.
Qed.

Theorem AllRightIntroduction2 : forall FX, uniform FX ->  (forall x, proper x -> isOLFormula( FX x)) ->
                                           (seq StrRulesPOS [] [] (> [ (ALL_INTRO FX) ^ ; (ALL_RIGHT FX)])).
Proof with SolveIsFormulas.
  intros FX  isFX isFXt; autounfold;simpl.
  solveLL'.
  decide1' (perp (up (t_quant ALL FX)) ** F{ fun t => atom (up (FX t))}).
  tensor' [atom (up (t_quant ALL FX))] [E{ fun x => perp (up (FX x))}].
  solveLL'.
  decide1' (E{ fun x0 => perp (up (FX x0))}).
  existential' x.
Qed.

(******************************)


Theorem NMNMCUTPOS : forall n B M X,
    isFormulaL B -> isFormulaL M -> isNotAsyncL M -> isArrow X -> 
    (seqN NMSTR n B M X ) ->
    (seq NM B M X ).
  Proof with solveF;SolveIsFormulas.
    induction n using strongind; intros B M arrow isB isM isNoatAsyncM isArr Hseq.
    inversion Hseq...
    inversion Hseq;solveF;simpl in isArr;
    try solve [inversion isArr ; solveF; try(apply H in H1);solveF;SolveIsFormulas ].
    inversion isArr...
    apply H in H2...
    apply H in H3...
    tensor' M0 N.

    apply H in H2...
    inversion isArr...
    inversion H3...
    apply H in H1...

    inversion isArr... inversion H4...
    apply H in H1...
    apply H in H2...

    admit.
    admit.

    decide1' F...
    eauto...
    apply H in H3...
    
    decide2' F...
    apply H in H3...
    admit.

    
    { (* from the theory *)
      apply H in H3...
      inversion H1...
      (* from the rules *)
      decide3' (F)...
      (* structural rules *)
      inversion H0...
      admit.
      admit.
      admit.
      admit.
    }

    existential' t...
    inversion isArr...
    apply H in H3...

    inversion isArr...
    inversion H4...
    solveLL'.
    specialize (H2 x properX).
    apply H in H2...
  Admitted.
    
  

Theorem SEQtoNM: forall n B M X , isFormulaL B -> isFormulaL M -> isNotAsyncL M -> isArrow X -> 
                                  (seqN SEQSTR n B M X ) ->
                                  (seq NMSTR B M X ).
Proof with solveF;SolveIsFormulas.
  induction n using strongind; intros B M arrow isB isM isNoatAsyncM isArr Hseq.
  inversion Hseq...
  
  inversion Hseq;solveF;simpl in isArr;
    try solve [inversion isArr ; solveF; apply H in H1;solveF;SolveIsFormulas
              ].
  

  inversion isArr...
  apply H in H2...
  apply H in H3...
  tensor' M0 N.

  apply H in H2...

  inversion isArr... inversion H3...
  apply H in H1...
  
  inversion isArr... inversion H4...
  apply H in H1...
  apply H in H2...

  inversion isArr... inversion H3...
  apply H in H1... 

  
  inversion isArr...
  apply H in H2...
  
  apply H in H3...
  decide1' F;eauto.
  
  
  decide2' F...
  apply H in H3...
  eapply Forall_forall with (l:=B);eauto.

  { (* decide 3 case *)
    inversion H1...
    { 
      inversion H0...
      + (* implication right *)
        apply H in H3...
        assert(Cut: seq NMSTR B ([] ++M) ( > [(IMP_INTRO F0 G)])).
        apply GeneralCut' with (C:= (IMP_RIGHT F0 G) ^) (dualC := IMP_RIGHT F0 G)...
        apply NMStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPos  ) .
        apply nm_str.
        generalize( ImplRightIntroduction1 H4 H5);intro HCut;simpl in HCut...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        simpl in Cut.
        apply AbsorptionTheory with (F:= (IMP_INTRO F0 G))...
      + (* implication left*)
        apply H in H3...
        assert(Cut: seq NMSTR B ([] ++M) ( > [(IMP_ELIMINATION F0 G)])).
        apply GeneralCut' with (C:= (IMP_LEFT F0 G) ^) (dualC := IMP_LEFT F0 G)...
        apply NMStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPos  ) .
        apply nm_str. 
        generalize( ImplLeftElimination1 H4 H5);intro HCut;simpl in HCut...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        simpl in Cut.
        apply AbsorptionTheory with (F:= (IMP_ELIMINATION F0 G))...
      + (* Conjunction *)
        apply H in H3...
        assert(Cut: seq NMSTR B ([] ++M) ( > [(CONJ_INTRO F0 G)])).
        apply GeneralCut' with (C:= (CONJ_RIGHT F0 G) ^) (dualC := CONJ_RIGHT F0 G)...
        apply NMStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPos  ) .
        apply nm_str.
        generalize( ConjRightIntroduction1 H4 H5);intro HCut;simpl in HCut...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        simpl in Cut.
        apply AbsorptionTheory with (F:= (CONJ_INTRO F0 G))...
      + (* conjunction *)
        apply H in H3...
        assert(Cut: seq NMSTR B ([] ++M) ( > [(CONJ_ELIMINATION F0 G)])).
        apply GeneralCut' with (C:= (CONJ_LEFT F0 G) ^) (dualC := CONJ_LEFT F0 G)...
        apply NMStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPos  ) .
        apply nm_str. 
        generalize( ConjLeftElimination1 H4 H5);intro HCut;simpl in HCut...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        simpl in Cut.
        apply AbsorptionTheory with (F:= (CONJ_ELIMINATION F0 G))...
      + (* all *)
        apply H in H3;solveF...
        assert(Cut: seq NMSTR B ([] ++M) ( > [(ALL_INTRO FX)])).
        apply GeneralCut' with (C:= (ALL_RIGHT FX) ^) (dualC := ALL_RIGHT FX);solveF;SolveIsFormulas'.
        apply NMStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPos  ) .
        apply nm_str.
        generalize( AllRightIntroduction1 H4 H5);intro HCut;simpl in HCut.
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        apply AbsorptionTheory with (F:= (ALL_INTRO FX));solveF;SolveIsFormulas'.
        SolveIsFormulas'.
      + (* all *) 
        apply H in H3...
        assert(Cut: seq NMSTR B ([] ++M) ( > [(ALL_ELIMINATION FX)])).
        apply GeneralCut' with (C:= (ALL_LEFT FX) ^) (dualC := ALL_LEFT FX);SolveIsFormulas'.
        apply NMStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPos  ) .
        apply nm_str.
        generalize( AllLeftElimination1 H4 H5);intro HCut;simpl in HCut.
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        apply AbsorptionTheory with (F:= (ALL_ELIMINATION FX));SolveIsFormulas'.
        SolveIsFormulas'.
    } 
    apply H in H3...
    decide3' F...
    apply StrRulesPosFormulas...
  }

  inversion isArr...
  apply H in H3...
  existential' t.

  inversion isArr...
  solveLL'.
  apply H2 in properX. apply H in properX...
  inversion H4...
Qed.

Theorem NMtoSeq: forall n B M X , isFormulaL B -> isFormulaL M -> isNotAsyncL M -> isArrow X -> 
                                  (seqN NMSTR n B M X ) ->
                                  (seq  SEQSTR B M X ).
Proof with solveF;SolveIsFormulas.
  induction n using strongind; intros B M arrow isB isM isNoatAsyncM isArr Hseq.
  inversion Hseq...
  
  inversion Hseq;solveF;simpl in isArr;
    try solve [inversion isArr ; solveF; apply H in H1;solveF;SolveIsFormulas
              ].
  

  inversion isArr...
  apply H in H2...
  apply H in H3...
  tensor' M0 N.
  
  apply H in H2...

  inversion isArr... inversion H3...
  apply H in H1...
  
  inversion isArr... inversion H4...
  apply H in H1...
  apply H in H2...

  inversion isArr... inversion H3...
  apply H in H1... 

  
  inversion isArr...
  apply H in H2...
  
  apply H in H3...
  decide1' F;eauto.
  
  
  decide2' F;eauto.
  apply H in H3...
  eapply Forall_forall with (l:=B);eauto.

  { (* decide 3 case *)
    inversion H1...
    { 
      inversion H0...
      + (* implication right *)
        apply H in H3...
        assert(Cut: seq SEQSTR B ([] ++M) ( > [(IMP_RIGHT F0 G)])).
        apply GeneralCut' with (C:= (IMP_INTRO F0 G) ^) (dualC := IMP_INTRO F0 G)...
        apply SeqStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPos  ) .
        apply sq_str.
        generalize( ImplRightIntroduction2 H4 H5);intro HCut;simpl in HCut...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        simpl in Cut.
        apply AbsorptionTheory with (F:= (IMP_RIGHT F0 G))...
      + (* implication left*)
        apply H in H3...
        assert(Cut: seq SEQSTR B ([] ++M) ( > [(IMP_LEFT F0 G)])).
        apply GeneralCut' with (C:= (IMP_ELIMINATION F0 G) ^) (dualC := IMP_ELIMINATION F0 G)...
        apply SeqStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPos  ) .
        apply sq_str. 
        generalize( ImplLeftElimination2 H4 H5);intro HCut;simpl in HCut...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        simpl in Cut.
        apply AbsorptionTheory with (F:= (IMP_LEFT F0 G))...
      + (* Conjunction right *)
        apply H in H3...
        assert(Cut: seq SEQSTR B ([] ++M) ( > [(CONJ_RIGHT F0 G)])).
        apply GeneralCut' with (C:= (CONJ_INTRO F0 G) ^) (dualC := CONJ_INTRO F0 G)...
        apply SeqStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPos  ) .
        apply sq_str.
        generalize( ConjRightIntroduction2 H4 H5);intro HCut;simpl in HCut...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        simpl in Cut.
        apply AbsorptionTheory with (F:= (CONJ_RIGHT F0 G))...
      + (* implication left*)
        apply H in H3...
        assert(Cut: seq SEQSTR B ([] ++M) ( > [(CONJ_LEFT F0 G)])).
        apply GeneralCut' with (C:= (CONJ_ELIMINATION F0 G) ^) (dualC := CONJ_ELIMINATION F0 G)...
        apply SeqStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPos  ) .
        apply sq_str. 
        generalize( ConjLeftElimination2 H4 H5);intro HCut;simpl in HCut...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        simpl in Cut.
        apply AbsorptionTheory with (F:= (CONJ_LEFT F0 G))...
      + (* all *)
        apply H in H3...
        assert(Cut: seq SEQSTR B ([] ++M) ( > [(ALL_RIGHT FX)])).
        apply GeneralCut' with (C:= (ALL_INTRO FX) ^) (dualC := ALL_INTRO FX);SolveIsFormulas'.
        apply SeqStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPos  ) .
        apply sq_str.
        generalize( AllRightIntroduction2 H4 H5);intro HCut;simpl in HCut.
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        apply AbsorptionTheory with (F:= (ALL_RIGHT FX));SolveIsFormulas'.
        SolveIsFormulas'.
      + (* all *)
        apply H in H3...
        assert(Cut: seq SEQSTR B ([] ++M) ( > [(ALL_LEFT FX)])).
        apply GeneralCut' with (C:= (ALL_ELIMINATION FX) ^) (dualC := ALL_ELIMINATION FX);SolveIsFormulas'.
        apply SeqStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPos  ) .
        apply sq_str.
        generalize( AllLeftElimination2 H4 H5);intro HCut;simpl in HCut.
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut;SolveIsFormulas'.
        apply AbsorptionTheory with (F:= (ALL_LEFT FX));SolveIsFormulas'.
        SolveIsFormulas'.
    }
    apply H in H3...
    decide3' F...
    apply StrRulesPosFormulas...
  }
  inversion isArr...
  apply H in H3...
  existential' t.

  inversion isArr...
  solveLL'.
  apply H2 in properX. apply H in properX...
  inversion H4...
Qed.

(** Mutual relative completeness of natural deduction and sequent calculus.  *)
Theorem Adequacy: forall F, isOLFormula F -> 
                            (seq SEQSTR  [] [ atom (up F) ] (> [ ]))  <->
                            (seq NMSTR  [] [ atom (up F) ]  (> [ ])).
Proof with solveF;SolveIsFormulas.
  intros.
  split;intro.
  apply seqtoSeqN in H0;CleanContext.
  eapply SEQtoNM... eauto.
  apply seqtoSeqN in H0;CleanContext.
  eapply NMtoSeq... eauto.
Qed.
