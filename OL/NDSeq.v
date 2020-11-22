(** * System LM: Natural deduction and sequent calculus

In this file we encode the logical rules of natural deduction and
sequent calculus for minimal logic. Then, using the
cut-elimination theorem of LL we prove the relative completeness of
these systems
 *)

Require Import FLL.SL.CutElimination.
Require Export FLL.OL.LM.

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


(** Definition for Elimination and introduction rules of implication,
conjunction and universal quantification in natural deduction *)
Definition IMP_ELIMINATION F G:= ((perp (up G)) ** (! atom (up F)) ** (! atom (up (t_bin IMP F G))) ).
Definition IMP_INTRO F G := ( ( perp ( up  ( t_bin IMP F G))) ** ( ? (atom (down F)) $ (atom (up G )) )).
Definition CONJ_ELIMINATION F G :=  ( (perp (up F)) op  (perp (up G)) ) ** (! atom (up (t_bin AND F G))) .
Definition CONJ_INTRO F G := (perp (up (t_bin AND F G))) ** (  (atom (up F)) & (atom (up G))) .
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

(* A Theory including TH + INIT + CUT + CUTi *)
Inductive StrRulesPOS : oo -> Prop :=
| stp_cutP : forall F, isOLFormula F -> StrRulesPOS (RCUTPOS F)
| stp_cut : forall F, isOLFormula F -> StrRulesPOS (RCUT F)
| stp_pos : forall F, isOLFormula F -> StrRulesPOS (POS F)
| stp_init : forall F, isOLFormula F -> StrRulesPOS (RINIT F)
.

Theorem StrRulesPOSFormulas : forall F,  StrRulesPOS F -> isFormula F.
  intros.
  inversion H;subst;auto;
  constructor;auto.
Qed.

(** Sequent and natural deduction systems with the structural rules *)
Inductive NMSTR : oo -> Prop :=
| nm_rl : forall F, NM F -> NMSTR F
| nm_str: forall F, StrRulesPOS F -> NMSTR F.

Inductive SEQSTR : oo -> Prop :=
| sq_rl : forall F, buildTheory F -> SEQSTR F
| sq_str: forall F, StrRulesPOS F -> SEQSTR F.

Hint Constructors StrRulesPOS NM LMSeq NMSTR SEQSTR  : core.
Hint Constructors NMSTR SEQSTR : core.
Hint Unfold IMP_ELIMINATION IMP_INTRO   POS RCUT RINIT CONJ_ELIMINATION CONJ_INTRO  : core .
Hint Unfold ALL_ELIMINATION ALL_INTRO    : core.

Hint Constructors StrRulesPos : core .
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
  inversion H0;subst; destruct C;subst;SolveIsFormulas'.
  inversion H0;subst;SolveIsFormulas.
Qed.

(** Proving dualities beween Left (resp. right) introduction rules in 
sequent calculus and Elimination (resp. Introduction) rules in 
Natural Deduction *)
Hint Unfold POS : core .
 
Theorem ImplLeftElimination1 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPOS [] [] (> [ (makeRuleBin IMP Left F G)  ^ ; (IMP_ELIMINATION F G)])).
Proof with SolveIsFormulas;solveF.
  intros F G isF isG; autounfold;simpl;solveLL.
  ExchangeFront' 3.
  decide3 (POS ( t_bin IMP F G))...
  tensor [d| t_bin IMP F G | ] [(u^| G | ** (! u| F |)) ** (! u| t_bin IMP F G |);  ! d^| G |] .
  simpl.
  decide3 (RCUT G).
  tensor  [(u^| G | ** (! u| F |)) ** (! u| t_bin IMP F G |) ] [! d^| G |].
  decide1 ((u^| G | ** (! u| F |)) ** (! u| t_bin IMP F G |)).
  tensor [u| G |] (@nil oo).
  tensor [u| G |] (@nil oo).
  decide2 (u^| F |).
  decide3 (RINIT ( t_bin IMP F G)).
  tensor [u| t_bin IMP F G |] (@nil oo)...

  decide3 (POS G).
  tensor [d| G |] [! d^| G |]. simpl.
  decide1 (! d^| G|).
  solveLL...
  decide1 (d^| G|)...
Qed.


Theorem ImplLeftElimination2 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPOS [] [] (> [ (IMP_ELIMINATION F G) ^ ; (makeRuleBin IMP Left F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL.
  decide3 (RCUTPOS (t_bin IMP F G))...
  tensor   [u| G |; d^| t_bin IMP F G | ** ((! u| F |) ** (? d| G |))] (@nil oo);simpl.
  decide1 (d^| t_bin IMP F G | ** ((! u| F |) ** (? d| G |))).
  tensor (@nil oo) [u| G |].
  right...
  tensor (@nil oo) [u| G |].
  decide2 (u^|F|).
  simpl.
  decide3( RINIT (G))...
  tensor  [u| G |] (@nil oo).
  right ...
  decide2 (u^| t_bin IMP F G |).
Qed.

Theorem ImplRightIntroduction1 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPOS [] [] (> [ (makeRuleBin IMP Right F G) ^ ; (IMP_INTRO F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL.
  decide1 (u^| t_bin IMP F G | ** ((? d| F |) $ u| G |)).
  tensor [u| t_bin IMP F G |] [(! d^| F |) ** u^| G |].
  decide1 ((! d^| F |) ** u^| G |).
  tensor (@nil oo) [u| G |].
  decide1 (d^| F |).
Qed.

Theorem ImplRightIntroduction2 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPOS [] [] (> [ (IMP_INTRO F G) ^ ; (makeRuleBin IMP Right F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL.
  decide1 (  u^| t_bin IMP F G | ** ((? d| F |) $ u| G |)).
  tensor [u| t_bin IMP F G |] [(! d^| F |) ** u^| G |].
  decide1 ((! d^| F |) ** u^| G |).
  tensor (@nil oo)  [u| G |].
  decide1 (d^| F |).
Qed.


Theorem ConjLeftElimination1 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPOS [] [] (> [ (makeRuleBin AND Left F G) ^ ; (CONJ_ELIMINATION F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL.
  + decide3 (RCUT F).
    tensor  [d| t_bin AND F G |; (u^| F | op u^| G |) ** (! u| t_bin AND F G |)] [! d^| F |].
    decide3 (POS (t_bin AND F G)).
    tensor [d| t_bin AND F G |][ (u^| F | op u^| G |) ** (! u| t_bin AND F G |); u| F |] ...
    decide1 ((u^| F | op u^| G |) ** (! u| t_bin AND F G |)).
    tensor [ u| F |]  (@nil oo).
    decide3 (RINIT (t_bin AND F G)).
    tensor [u| t_bin AND F G |] (@nil oo)...
    decide3 (POS F).
    tensor [ d| F |][! d^| F |]...
    decide1 (! d^| F |)...
    solveLL.
    decide1 ( d^| F |);solveLL...
  + decide3 (POS (t_bin AND F G)).
    tensor  [d| t_bin AND F G |][ ! d^| G |; (u^| F | op u^| G |) ** (! u| t_bin AND F G |)]...
    decide3 (RCUT G).
    tensor [(u^| F | op u^| G |) ** (! u| t_bin AND F G |)] [! d^| G |].
    decide1 ((u^| F | op u^| G |) ** (! u| t_bin AND F G |)).
    tensor [u| G |] (@nil oo).
    decide3 (RINIT (t_bin AND F G)).
    tensor [u| t_bin AND F G |] (@nil oo)...
    decide3 (POS G).
    tensor [d| G |] [! d^| G |]...
    decide1 (! d^| G |)...
    solveLL.
    decide1 ( d^| G |)...
Qed.

Theorem ConjLeftElimination2 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPOS [] [] (> [ (CONJ_ELIMINATION F G) ^ ; (makeRuleBin AND Left F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL.
  + decide3 (RCUTPOS ( t_bin AND F G)).
    tensor  [u| F |; d^| t_bin AND F G | ** ((? d| F |) op (? d| G |))] (@nil oo)...
    decide1 (d^| t_bin AND F G | ** ((? d| F |) op (? d| G |))).
    tensor (@nil oo) [u| F |]...
    oplus1...
    decide3 (RINIT F).
    tensor ([u| F |]) (@nil oo)...
    decide2 (u^| t_bin AND F G |).
  +  decide3 (RCUTPOS ( t_bin AND F G)).
     tensor [u| G |; d^| t_bin AND F G | ** ((? d| F |) op (? d| G |))] (@nil oo)...
     decide1 (d^| t_bin AND F G | ** ((? d| F |) op (? d| G |))).
     tensor (@nil oo) [u| G |]...
     oplus2...
     decide3 (RINIT G).
    tensor ([u| G |]) (@nil oo)...
    decide2 (u^| t_bin AND F G |).
Qed.


Theorem ConjRightIntroduction1 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPOS [] [] (> [ (makeRuleBin AND Right F G) ^ ; (CONJ_INTRO F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL.
  decide1 (perp (up (t_bin AND F G)) ** (atom (up F) & atom (up G))).
  tensor [atom (up (t_bin AND F G)) ] [perp (up F) op perp (up G)].
  decide1 (perp (up F) op perp (up G)).
  decide1 (perp (up F) op perp (up G)).
Qed.

Theorem ConjRightIntroduction2 :
  forall F G, isOLFormula F -> isOLFormula G ->
              (seq StrRulesPOS [] [] (> [ (CONJ_INTRO F G) ^ ; (makeRuleBin AND Right F G)])).
Proof with SolveIsFormulas.
  intros F G isF isG; autounfold;simpl;solveLL.
  decide1 ( u^| t_bin AND F G | ** (u| F | & u| G |)).
  tensor [u| t_bin AND F G |][ u^| F | op u^| G |].
  decide1 (u^| F | op u^| G |).
  decide1 (u^| F | op u^| G |).
Qed.


Theorem AllLeftElimination1 : forall FX, uniform FX ->  (forall x, proper x -> isOLFormula( FX x)) ->
                                         (seq StrRulesPOS [] [] (> [ (makeRuleQ ALL Left FX) ^ ; (ALL_ELIMINATION FX)])).
Proof with SolveIsFormulas'.
  intros FX  isFX isFXt; autounfold;simpl;solveLL.
  decide3 (POS ( t_quant ALL FX)).
  tensor [d| t_quant ALL FX |][ ! d^| FX x |; E{ fun t  => u^| FX t | ** (! u| t_quant ALL FX |)}]...
  decide3 (RCUT (FX x)).
  tensor [ E{ fun t  => u^| FX t | ** (! u| t_quant ALL FX |)}] [! d^| FX x |]...
  decide1 (E{ fun t => u^| FX t | ** (! u| t_quant ALL FX |)}).
  existential x...
  tensor  [u| FX x |] (@nil oo).
  decide3 (RINIT (t_quant ALL FX)).
  tensor  [u| t_quant ALL FX |] (@nil oo)...
  decide3 (POS (FX x)).
  tensor [ d| FX x |] [! d^| FX x |]...
  decide1 (! d^| FX x |)...
  solveLL.
  decide1 (d^| FX x |)...
Qed. 
  

Theorem AllLeftElimination2 : forall FX, uniform FX ->  (forall x, proper x -> isOLFormula( FX x)) ->
                                         (seq StrRulesPOS [] [] (> [ (ALL_ELIMINATION FX) ^ ; (makeRuleQ ALL Left FX)])).
Proof with SolveIsFormulas'.
  intros FX  isFX isFXt; autounfold;simpl.
  apply tri_fx'...
  intros.
  solveLL.
  decide3( RCUTPOS ( t_quant ALL FX)).
  tensor [u| FX x |; d^| t_quant ALL FX | ** E{ fun t => ? d| FX t |}] (@nil oo) ...
  decide1 (d^| t_quant ALL FX | ** E{ fun t => ? d| FX t |}).
  tensor (@nil oo)  [u| FX x |]...
  existential x...
  decide3 (RINIT (FX x))...
  tensor  [u| FX x |] (@nil oo)...
  decide2 (u^| t_quant ALL FX |).
Qed.

Theorem AllRightIntroduction1 : forall FX, uniform FX ->  (forall x, proper x -> isOLFormula( FX x)) ->
                                           (seq StrRulesPOS [] [] (> [(makeRuleQ ALL Right FX) ^ ; (ALL_INTRO FX)])).
Proof with SolveIsFormulas.
  intros FX  isFX isFXt; autounfold;simpl.
  solveLL.
  decide1 (perp (up (t_quant ALL FX)) ** F{ fun t=> atom (up (FX t))}).
  tensor  [atom (up (t_quant ALL FX))] [E{ fun x => perp (up (FX x))}].
  solveLL.
  decide1 (E{ fun x0 => perp (up (FX x0))}).
  existential x.
Qed.

Theorem AllRightIntroduction2 : forall FX, uniform FX ->  (forall x, proper x -> isOLFormula( FX x)) ->
                                           (seq StrRulesPOS [] [] (> [ (ALL_INTRO FX) ^ ; (makeRuleQ ALL Right FX)])).
Proof with SolveIsFormulas.
  intros FX  isFX isFXt; autounfold;simpl.
  solveLL.
  decide1 (perp (up (t_quant ALL FX)) ** F{ fun t => atom (up (FX t))}).
  tensor [atom (up (t_quant ALL FX))] [E{ fun x => perp (up (FX x))}].
  solveLL.
  decide1 (E{ fun x0 => perp (up (FX x0))}).
  existential x.
Qed.

Definition AND' : connectives := AND .
Definition IMP' : connectives := IMP .
Definition ALL' : quantifiers := ALL .

Theorem SEQtoNM: forall n B M X , isFormulaL B -> isFormulaL M -> isNotAsyncL M -> isArrow X -> 
                                  (seqN SEQSTR n B M X ) ->
                                  (seq NMSTR B M X ).
Proof with solveF;SolveIsFormulas;SolveIS.
  induction n using strongind; intros B M arrow isB isM isNoatAsyncM isArr Hseq.
  inversion Hseq...
  
  inversion Hseq;solveF;simpl in isArr;
    try solve [inversion isArr ; solveF; apply H in H1;solveF;SolveIsFormulas
              ].
  

  inversion isArr...
  apply H in H2...
  apply H in H3...
  tensor M0 N.

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
  decide1 F;eauto.
  
  
  decide2 F...
  apply H in H3...
  eapply Forall_forall with (l:=B);eauto.

  { (* decide 3 case *)
    inversion H1...
    { 
      inversion H0...
      destruct C. (* no constants *)
      destruct C. (* no constants *)
      + (* Right rule *)
        destruct C...
        { (* AND *)
          inversion H4...
          apply H in H3...
          assert(Cut: seq NMSTR B ([] ++M) ( > [(CONJ_INTRO F0 G)])).
          apply GeneralCut' with (C:= (makeRuleBin AND' Right F0 G) ^) (dualC := (makeRuleBin AND' Right F0 G))...
          apply NMStrRulesFormulas.
          eapply WeakTheory with (theory:=  StrRulesPOS  ) .
          apply nm_str.
          generalize( ConjRightIntroduction1 H7 H9);intro HCut;simpl in HCut...
          apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
          unfold AND'...  
          apply AbsorptionTheory with (F:= (CONJ_INTRO F0 G))...
        }
        { (* Implication *)
          inversion H4...
          apply H in H3...
          assert(Cut: seq NMSTR B ([] ++M) ( > [(IMP_INTRO F0 G)])).
          apply GeneralCut' with (C:= (makeRuleBin IMP' Right F0 G) ^) (dualC := (makeRuleBin IMP' Right F0 G))...
          apply NMStrRulesFormulas.
          eapply WeakTheory with (theory:=  StrRulesPOS  ) .
          apply nm_str.
          generalize( ImplRightIntroduction1 H7 H9);intro HCut;simpl in HCut...
          unfold IMP'...  
          apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
          simpl in Cut.
          apply AbsorptionTheory with (F:= (IMP_INTRO F0 G))...
        }
      + (* Left rule *)
        destruct C...
        { (* AND *)
          inversion H4...
          apply H in H3...
          assert(Cut: seq NMSTR B ([] ++M) ( > [(CONJ_ELIMINATION F0 G)])).
          apply GeneralCut' with (C:= (makeRuleBin AND' Left F0 G) ^) (dualC := (makeRuleBin AND' Left F0 G))...
          apply NMStrRulesFormulas.
          eapply WeakTheory with (theory:=  StrRulesPOS  ) .
          apply nm_str. 
          generalize( ConjLeftElimination1 H7 H9);intro HCut;simpl in HCut...
          unfold AND'.
          apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
          simpl in Cut.
          apply AbsorptionTheory with (F:= (CONJ_ELIMINATION F0 G))...
        }
        { (* IMP *)
          inversion H4...
          apply H in H3...
          assert(Cut: seq NMSTR B ([] ++M) ( > [(IMP_ELIMINATION F0 G)])).
          apply GeneralCut' with (C:= (makeRuleBin IMP' Left F0 G) ^) (dualC := (makeRuleBin IMP' Left F0 G))...
          apply NMStrRulesFormulas.
          eapply WeakTheory with (theory:=  StrRulesPOS).
          apply nm_str. 
          generalize( ImplLeftElimination1 H7 H9);intro HCut;simpl in HCut...
          unfold IMP'.
          apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
          simpl in Cut.
          apply AbsorptionTheory with (F:= (IMP_ELIMINATION F0 G))...
        }
      + (* Quantifier Right *)
        destruct C...
        inversion H5;SolveIS...
        apply lbindEq in H7...
        assert (HIs: forall t, proper t -> isOLFormula (FX t)).
        intros...
        apply H in H3;solveF...
        assert(Cut: seq NMSTR B ([] ++M) ( > [(ALL_INTRO FX)])).
        apply GeneralCut' with (C:=  (makeRuleQ ALL' Right FX) ^) (dualC := (makeRuleQ ALL' Right FX));solveF;SolveIsFormulas'.
        apply NMStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPOS).
        apply nm_str.
        generalize( AllRightIntroduction1 H4 HIs);intro HCut;simpl in HCut.
        unfold ALL'...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        apply AbsorptionTheory with (F:= (ALL_INTRO FX));solveF;SolveIsFormulas'.
        SolveIsFormulas'.
      + (* Quantifier Left *)
        destruct C...
        inversion H5;SolveIS...
        apply lbindEq in H7...
        assert (HIs: forall t, proper t -> isOLFormula (FX t)).
        intros...
        apply H in H3...
        assert(Cut: seq NMSTR B ([] ++M) ( > [(ALL_ELIMINATION FX)])).
        apply GeneralCut' with (C:= (makeRuleQ ALL' Left FX) ^) (dualC := (makeRuleQ ALL' Left FX));SolveIsFormulas'.
        apply NMStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPOS).
        apply nm_str.
        generalize( AllLeftElimination1 H4 HIs);intro HCut;simpl in HCut.
        unfold ALL'...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        apply AbsorptionTheory with (F:= (ALL_ELIMINATION FX));SolveIsFormulas'.
        SolveIsFormulas'.
    } 
    apply H in H3...
    decide3 F...
    apply StrRulesPOSFormulas...
  }

  inversion isArr...
  apply H in H3...
  existential t.

  inversion isArr...
  solveLL.
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
  tensor M0 N.
  
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
  decide1 F;eauto.
  
  
  decide2 F;eauto.
  apply H in H3...
  eapply Forall_forall with (l:=B);eauto.

  { (* decide 3 case *)
    inversion H1...
    { 
      inversion H0...
      + (* implication right *)
        apply H in H3...
        assert(Cut: seq SEQSTR B ([] ++M) ( > [(makeRuleBin IMP Right F0 G)])).
        apply GeneralCut' with (C:= (IMP_INTRO F0 G) ^) (dualC := IMP_INTRO F0 G)...
        apply SeqStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPOS).
        apply sq_str.
        generalize( ImplRightIntroduction2 H4 H5);intro HCut;simpl in HCut...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        simpl in Cut.
        apply AbsorptionTheory with (F:= (makeRuleBin IMP' Right F0 G)) ...
        unfold IMP'...
        do 2 constructor. eapply isFBin...
      + (* implication left*)
        apply H in H3...
        assert(Cut: seq SEQSTR B ([] ++M) ( > [(makeRuleBin IMP Left F0 G)])).
        apply GeneralCut' with (C:= (IMP_ELIMINATION F0 G) ^) (dualC := IMP_ELIMINATION F0 G)...
        apply SeqStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPOS).
        apply sq_str. 
        generalize( ImplLeftElimination2 H4 H5);intro HCut;simpl in HCut...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        apply AbsorptionTheory with (F:= (makeRuleBin IMP' Left F0 G))...
        unfold IMP'... do 2 constructor. eapply isFBin...
      + (* Conjunction right *)
        apply H in H3...
        assert(Cut: seq SEQSTR B ([] ++M) ( > [(makeRuleBin AND Right F0 G)])).
        apply GeneralCut' with (C:= (CONJ_INTRO F0 G) ^) (dualC := CONJ_INTRO F0 G)...
        apply SeqStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPOS).
        apply sq_str.
        generalize( ConjRightIntroduction2 H4 H5);intro HCut;simpl in HCut...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        apply AbsorptionTheory with (F:= (makeRuleBin AND' Right F0 G))...
        unfold IMP'... do 2 constructor. eapply isFBin...
      + (* conjunction left *)
        apply H in H3...
        assert(Cut: seq SEQSTR B ([] ++M) ( > [(makeRuleBin AND Left F0 G)])).
        apply GeneralCut' with (C:= (CONJ_ELIMINATION F0 G) ^) (dualC := CONJ_ELIMINATION F0 G)...
        apply SeqStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPOS).
        apply sq_str. 
        generalize( ConjLeftElimination2 H4 H5);intro HCut;simpl in HCut...
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        apply AbsorptionTheory with (F:= (makeRuleBin AND' Left F0 G))...
        unfold AND'... do 2 constructor. eapply isFBin...
      + (* all *)
        apply H in H3...
        assert(Cut: seq SEQSTR B ([] ++M) ( > [(makeRuleQ ALL Right FX)])).
        apply GeneralCut' with (C:= (ALL_INTRO FX) ^) (dualC := ALL_INTRO FX);SolveIsFormulas'.
        apply SeqStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPOS).
        apply sq_str.
        generalize( AllRightIntroduction2 H4 H5);intro HCut;simpl in HCut.
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut...
        apply AbsorptionTheory with (F:= (makeRuleQ ALL' Right FX));SolveIsFormulas'.
        unfold ALL'...
        do 2 constructor...
        SolveIsFormulas'.
      + (* all *)
        apply H in H3...
        assert(Cut: seq SEQSTR B ([] ++M) ( > [(makeRuleQ ALL Left FX)])).
        apply GeneralCut' with (C:= (ALL_ELIMINATION FX) ^) (dualC := ALL_ELIMINATION FX);SolveIsFormulas'.
        apply SeqStrRulesFormulas.
        eapply WeakTheory with (theory:=  StrRulesPOS).
        apply sq_str.
        generalize( AllLeftElimination2 H4 H5);intro HCut;simpl in HCut.
        apply weakeningGen with (CC' := B) in HCut. rewrite app_nil_r in HCut;SolveIsFormulas'.
        apply AbsorptionTheory with (F:= (makeRuleQ ALL' Left FX));SolveIsFormulas'.
        unfold ALL'...
        do 2 constructor...
        SolveIsFormulas'.
    }
    apply H in H3...
    decide3 F...
    apply StrRulesPOSFormulas...
  }
  inversion isArr...
  apply H in H3...
  existential t.

  inversion isArr...
  solveLL.
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


