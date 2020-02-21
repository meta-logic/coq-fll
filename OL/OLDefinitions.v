(** * Definitions for the OL Cut-Elimination Theorem  *)

(** This file contains some useful definitions and tactics for the
proof of the cut-elimination theorem of Object Logics *)


Require Export FLL.Misc.Hybrid.
Require Export FLL.OL.OLSyntax.
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



Section PositiveAtoms.
  Context `{OL: OLSyntax}.

  
  (** Positive atoms are only [down] and [up] atoms. The linear and
  the classical context of the encoding must contain only formulas of
  this kind *)
  Inductive IsPositiveAtomFormula : oo -> Prop :=
  | IsFPA_dw : forall A, isOLFormula A -> IsPositiveAtomFormula (atom (down (A)))
  | IsFPA_up : forall A, isOLFormula A -> IsPositiveAtomFormula (atom (up (A))).
  Hint Constructors IsPositiveAtomFormula : core .

  
  Definition IsPositiveAtomFormulaL L : Prop := Forall IsPositiveAtomFormula L.
  Hint Unfold IsPositiveAtomFormulaL : core. 

  (** Some auxiliar results that help automation *)
  Lemma IsPositiveAtomFormulaLApp :
    forall M N, IsPositiveAtomFormulaL M ->
                IsPositiveAtomFormulaL N ->
                IsPositiveAtomFormulaL (M ++ N ).
    intros;eapply ForallApp;auto.
  Qed.

  Lemma IsPositiveAtomFormulaLConsInv :
    forall M N F, Permutation N (F :: M) ->
                  IsPositiveAtomFormulaL N ->
                  IsPositiveAtomFormulaL M.
    intros.
    
    generalize (PermuteMap H0 H);intro.
    inversion H1;auto.
  Qed.


  Lemma IsPositiveConsInv :
    forall M N A, isOLAtom A ->
                  Permutation N ( (atom (up A) ) :: M) ->
                  IsPositiveAtomFormulaL M ->
                  IsPositiveAtomFormulaL N.
  Proof with solveF.
    intros.
    assert (IsPositiveAtomFormulaL ((atom (up A) ) :: M)).
    constructor;auto.
    constructor.
    inversion H;auto. 
    apply Permutation_sym in H0.
    generalize (PermuteMap H2 H0) ;auto.
  Qed.

  Lemma IsPositiveConsInvF :
    forall M N A, isOLFormula A ->
                  Permutation N ( (atom (up A) ) :: M) ->
                  IsPositiveAtomFormulaL M ->
                  IsPositiveAtomFormulaL N.
  Proof with solveF.
    intros.
    assert (IsPositiveAtomFormulaL ( (atom (up A) ) :: M)).
    constructor;auto.
    apply Permutation_sym in H0.
    generalize (PermuteMap H2 H0) ;auto.
  Qed.
  
  Lemma IsPosL0 :
    forall A N M G  L L',
      isOLFormula A ->
      IsPositiveAtomFormulaL N ->
      Permutation ((atom (up A) ) :: M) ((( atom (up A) ) :: L) ++ L') ->
      Permutation N (G :: M) ->
      IsPositiveAtomFormulaL L.
  Proof with subst;auto.
    intros.
    generalize (PermuteMap H0 H2);intro.
    inversion H3 ...
    assert( IsPositiveAtomFormulaL ((atom (up A) ) :: M))...
    generalize (PermuteMap H4 H1);intro.
    apply ForallAppInv1 in H5.
    inversion H5...
  Qed.

  

  Lemma IsPosL1 :
    forall M F L A X, IsPositiveAtomFormulaL M ->
                      Permutation M (F :: L) ->
                      IsPositiveAtomFormula A ->
                      Permutation X  ( A   :: L) ->
                      IsPositiveAtomFormulaL X.
    intros.
    Proof with subst;auto. 
      generalize (PermuteMap H H0);intro.
      inversion H3...
      apply Forall_cons with (x:= A) in H7 ...
      apply Permutation_sym in H2.
      eauto using PermuteMap.
    Qed.
    
    Lemma isPosL2 :
      forall N MN' M N0, IsPositiveAtomFormulaL N ->
                         Permutation N MN' ->
                         Permutation MN' (M ++ N0) ->
                         IsPositiveAtomFormulaL M.
      intros.
      generalize (PermuteMap H H0);intro.
      generalize (PermuteMap H2 H1);intro.
      eauto using ForallAppInv1.
    Qed.
    Lemma isPosL3 :
      forall N MN' M N0, IsPositiveAtomFormulaL N ->
                         Permutation N MN' ->
                         Permutation MN' (M ++ N0) ->
                         IsPositiveAtomFormulaL N0.
      intros.
      generalize (PermuteMap H H0);intro.
      generalize (PermuteMap H2 H1);intro.
      eauto using ForallAppInv2.
    Qed.

    Lemma isPosL4 :
      forall A N M A1 A2,  IsPositiveAtomFormula A ->
                           IsPositiveAtomFormulaL N ->
                           Permutation (A :: N) (A1 :: A2 :: M) ->
                           IsPositiveAtomFormulaL M.
      intros.
      apply Permutation_sym in H1.
      assert (H' : forall F, In F M ->  In F (A :: N)).
      intros FF H''; apply Permutation_in with (x:= FF) in H1;auto;do 2 eapply in_cons in H'';eauto.
      assert (H''' : IsPositiveAtomFormulaL (A :: N)) by auto.
      apply Forall_forall;intros.
      unfold IsPositiveAtomFormulaL in H'''.
      rewrite Forall_forall in H''';auto.
    Qed.

    Lemma IsPositiveAtomNotAsync :
      forall N, IsPositiveAtomFormulaL N ->  isNotAsyncL  N.
      
      induction N;simpl;auto;intros.
      apply Forall_forall; intros x Hx; inversion Hx.
      inversion H;subst.
      change  (a :: N) with ( [a] ++ N).
      apply ForallApp;auto.
      2:{ apply IHN;auto. }
      
      inversion H2;subst;auto.
      apply Forall_forall; intros x Hx;inversion Hx;subst;auto.
      intro Hc;inversion Hc.
      inversion H1.
      apply Forall_forall; intros x Hx;inversion Hx;subst;auto.
      intro Hc;inversion Hc.
      inversion H1.
    Qed.

    Lemma IsPositiveIsFormula :
      forall N, IsPositiveAtomFormulaL N ->  isFormulaL  N.
      intros.
      induction H.
      constructor.
      inversion H;subst.
      constructor;auto.
      constructor;auto.
    Qed.

    Lemma PermIsFormula :
      forall N M, Permutation N M -> IsPositiveAtomFormulaL N ->
                  IsPositiveAtomFormulaL M.
      intros.
      eauto using PermuteMap.
    Qed.

    
    Lemma PermIsFormula' :
      forall N M, Permutation M N -> IsPositiveAtomFormulaL N ->
                  IsPositiveAtomFormulaL M.
      intros.
      apply Permutation_sym in H.
      eauto using PermuteMap.
    Qed.
    
    
    
End PositiveAtoms.

Ltac SolveIsFormulas :=
  let lab := fresh "lab" in
  let F1 := fresh "F1" in
  let G1 := fresh "G1" in
  let Ht := fresh "H" in
  
  repeat
    match goal with
      [ |- isNotAsyncL [_]] => constructor
    | [ |- ~ asynchronous (_)] => let Ha := fresh in solve  [intro Ha;inversion Ha]
    | [ |- isNotAsyncL []] => constructor
    | [ |- isFormulaL _ ] => constructor;SolveIsFormulas
    | [ |- Forall isFormula []] => solveF
    | [ |- Forall isFormula [_]] => constructor
    | [ |- ~ asynchronous _ /\ _ ] => split;[ solveF | SolveIsFormulas]
    | [ |- IsPositiveAtomFormula (atom _)] => constructor;auto
    | [ |- forall (_:_), _ ] => solve[intro lab;destruct lab;simpl]
    | [ |- forall (_:_) (_:_), _ ] => solve[intros lab F1;destruct lab;simpl]
    | [ |- forall (_:_) (_ _ :_), _ ] => solve[intros lab F1 G1;destruct lab;simpl]
    | [ |- _ /\ _] => split
    | [ |- isFormula _] => constructor
    | [ |- Notasynchronous _] => solve [intro Ht; inversion Ht]
    | [ |- ~ IsNegativeAtom _] => solve [intro Ht; inversion Ht]
    | [ |- isNotAsyncL _ ] => constructor
    | [ |- Forall Notasynchronous _ ] => constructor;SolveIsFormulas
    | [ Hp : Permutation ?M (?M0 ++ ?N) |-  isFormulaL ?M0] =>
      solve[ apply PermuteMap with (f:= isFormula) in Hp;solveF;
             apply ForallAppInv1 in Hp;solveF ]
    | [ Hp : Permutation ?M (?M0 ++ ?N) |-  isNotAsyncL ?M0] =>
      solve [apply PermuteMap with (f:= Notasynchronous) in Hp;solveF;
             apply ForallAppInv1 in Hp;solveF ]
    | [ Hp : Permutation ?M (?M0 ++ ?N) |-  isFormulaL ?N] =>
      solve [apply PermuteMap with (f:= isFormula) in Hp;solveF;
             apply ForallAppInv2 in Hp;solveF ]
    | [ Hp : Permutation ?M (?M0 ++ ?N) |-  isNotAsyncL ?N] =>
      solve [apply PermuteMap with (f:= Notasynchronous) in Hp;solveF;
             apply ForallAppInv2 in Hp;solveF ]
    | [ |- isFormulaL [_] ] => constructor;auto
    | [ |- isFormulaL(_ :: _)] => constructor;SolveIsFormulas;auto
    | [ |- isFormulaL (_ ++ _)] => apply ForallApp; SolveIsFormulas
    | [ |- isNotAsyncL (_ ++ _)] => apply ForallApp; SolveIsFormulas
    | [ Hp : Utils.remove _ _ _  |- isFormulaL _] => apply Remove_Permute in Hp;solveF;
                                                     apply PermuteMap with (f:= isFormula) in Hp;inversion Hp;solveF
    | [ Hp : Utils.remove _ _ _  |- isFormula _] => apply Remove_Permute in Hp;solveF;
                                                    apply PermuteMap with (f:= isFormula) in Hp;inversion Hp;solveF
    | [ Hp : Utils.remove _ _ _  |-  isNotAsyncL _] => apply Remove_Permute in Hp;solveF;
                                                       apply PermuteMap with (f:= Notasynchronous) in Hp;inversion Hp;solveF
    | [ |- isFormula _ ] => constructor;auto
                                          
    end;
  solveF.




(** This tactic solves most of the [IsPositiveLSolve] goals *)
Ltac IsPositiveLSolve :=
  match goal with
  | [ |- IsPositiveAtomFormulaL []] => constructor
  | [ |- IsPositiveAtomFormulaL (_ ++ _)] => solve [ apply IsPositiveAtomFormulaLApp;eauto  using Forall_Permute]
  | [ |- IsPositiveAtomFormulaL [_] ] => constructor ;solveF
  | [ |- IsPositiveAtomFormulaL (_ :: ?M)] => constructor ;solveF; fold (IsPositiveAtomFormulaL M);  IsPositiveLSolve
  | [ |- IsPositiveAtomFormulaL (?M ++ ?N) ] => apply IsPositiveAtomFormulaLApp;auto; try IsPositiveLSolve
  | [ H : Permutation ?N (_ :: ?M) , H':  IsPositiveAtomFormulaL ?M |-  IsPositiveAtomFormulaL ?N] => solve [eapply IsPositiveConsInv;eauto | eapply IsPositiveConsInvF;eauto ]
  | [ H : Permutation ?N (_ :: ?M) , H':  IsPositiveAtomFormulaL ?N |-  IsPositiveAtomFormulaL ?M] => generalize(IsPositiveAtomFormulaLConsInv H H');auto

  | [ H : IsPositiveAtomFormulaL ?N, H1 : Permutation ?N (?M1 ++ ?M2) |- IsPositiveAtomFormulaL ?M1] => exact ( ForallAppInv1 (PermuteMap H H1))
  | [ H : IsPositiveAtomFormulaL ?N, H1 : Permutation ?N (?M1 ++ ?M2) |- IsPositiveAtomFormulaL ?M2] => exact ( ForallAppInv2 (PermuteMap H H1))
  | [ H : Permutation ?x3 ( _ :: ?M0) , H' : Permutation ?N (_ :: ?M0) |- IsPositiveAtomFormulaL ?x3] =>
    apply IsPositiveAtomFormulaLConsInv in H';auto;IsPositiveLSolve
  | [H: Permutation ?N (_ :: ?M0), H' : Permutation ?M0 (?x7 ++ _) |- IsPositiveAtomFormulaL ?x7] =>
    apply IsPositiveAtomFormulaLConsInv in H;auto;IsPositiveLSolve
  | [H: Permutation ?N (_ :: ?M0), H' : Permutation ?M0 (_ ++ ?x7) |- IsPositiveAtomFormulaL ?x7] =>
    apply IsPositiveAtomFormulaLConsInv in H;auto;IsPositiveLSolve
  | [ |- Forall IsPositiveAtomFormula ?M] => fold  (IsPositiveAtomFormulaL M)
  |  [ H :isOLAtom ?A  |- IsPositiveAtomFormulaL ((atom (down ?A) ) :: ?M) ] =>
     constructor;inversion H;subst;auto;IsPositiveLSolve
  | [H : Permutation ?N (_ :: ?x ++ ?x0), H': IsPositiveAtomFormulaL ?N |- IsPositiveAtomFormulaL ?x0] =>
    apply  IsPositiveAtomFormulaLConsInv in H;auto; eapply ForallAppInv2;eauto
  | [H : Permutation ?N (_ :: ?x ++ ?x0), H': IsPositiveAtomFormulaL ?N |- IsPositiveAtomFormulaL ?x] =>
    apply  IsPositiveAtomFormulaLConsInv in H;auto; eapply ForallAppInv1;eauto
  | [ H : Forall IsPositiveAtomFormula ?M |- _ ]  => fold  (IsPositiveAtomFormulaL M) in H
  | [H:  Permutation (?A :: ?N) (_ :: (atom _ ) :: ?M0) |- IsPositiveAtomFormulaL ?M0]
    =>  eapply isPosL4;eauto
  | [ H : IsPositiveAtomFormulaL ?N,
          H': Permutation ((atom (up ?A) ) :: ?M) (((atom (up ?A) ) :: ?x7) ++ ?x0),
              H'': Permutation ?N (?G' :: ?M) |- IsPositiveAtomFormulaL ?x7] =>
    eapply IsPosL0 with (N:=N) (L':= x0) (G:= G')  (F:=A);eauto
  | [ H : IsPositiveAtomFormulaL ?N,
          H': Permutation ((atom (up ?A) ) :: ?M) (?x0 ++ ( atom (up ?A) ) :: ?x7 ),
              H'': Permutation ?N (?G' :: ?M) |- IsPositiveAtomFormulaL ?x7] =>
    rewrite Permutation_app_comm in H';IsPositiveLSolve
  | [ H : Permutation (?A :: ?N) ( (?A :: ?M) ++ _) |- IsPositiveAtomFormulaL ?M]=>
    simpl in H;apply Permutation_cons_inv in H;IsPositiveLSolve
  |  [ H : Permutation (?A :: ?N) ( _ ++ ?A :: ?M) |- IsPositiveAtomFormulaL ?M]=>
     rewrite <- Permutation_middle in H;apply Permutation_cons_inv in H;IsPositiveLSolve
  | [ H : Permutation ?N (_ :: ?M0), H' :   Permutation ?x3 ((atom _) :: ?M0) |-  IsPositiveAtomFormulaL ?x3] =>
    eauto using IsPosL1
  | [ H : IsPositiveAtomFormulaL ?N, H1: Permutation ?N ?MN', H2: Permutation ?MN' (?M ++ ?N0) |- IsPositiveAtomFormulaL ?M  ] => eapply  isPosL2;eauto
  | [H : IsPositiveAtomFormulaL ?N, H1:  Permutation ?N ?MN',  H3 : Permutation ?MN' (?M ++ ?N0) |- IsPositiveAtomFormulaL ?N0] => eapply  isPosL3;eauto
  end.


(** ** Rules of the encoded proof system *)
Section OLInferenceRules.
  Context `{OL: OLSyntax}.
  
  
  Inductive Side := Left | Right .

  (** Encoding of inference rules for units *)
  Record ruleCte :=
    {
      rc_rightBody : oo ; (* body of the right rule *)
      rc_leftBody : oo  (* body of the left rule *)
    } .

  (** Encoding of inference rules for unary connectives *)
  Record ruleUnary := 
    {
      ru_rightBody : uexp -> oo; 
      ru_leftBody : uexp ->  oo 
    }.
  
  (** Encoding of inference rules for binary connectives *)
  Record ruleBin := 
    {
      rb_rightBody : uexp -> uexp -> oo; 
      rb_leftBody : uexp -> uexp -> oo 
    }.

  (** Encoding of inference rules for quantifiers *)
  Record ruleQ := 
    {
      rq_rightBody : (uexp -> uexp) -> oo; (* body of the right rule *)
      rq_leftBody :  (uexp -> uexp) -> oo (* body of the left rule *)
    }.

  
  (** We assume an external definition mapping each
    connective/quantifier with a left and right rule *) 
  Class OORules :=
    {
      rulesCte : constants -> ruleCte ;
      rulesUnary : uconnectives -> ruleUnary;
      rulesBin : connectives -> ruleBin;
      rulesQ :   quantifiers -> ruleQ
    }.
  
End OLInferenceRules.

(** Building the inference rules (bipoles)  cut-coherence and well-formedness conditions *)
Section Bipoles.
  Context `{OLR: OORules}.
  
  (** Building the bipoles of the rules out of the user definitions  *)
  Definition makeLRuleConstant (lab : constants) :=
    ( perp ( down  ( t_cons lab) )) ** (rulesCte lab).(rc_leftBody) .
  Definition makeRRuleConstant (lab : constants) :=
    ( perp ( up  ( t_cons lab))) ** (rulesCte lab).(rc_rightBody) .

  Definition makeLRuleUnary (lab : uconnectives) :=
    fun (F:uexp) => (perp ( down  ( t_ucon lab F)) ) ** (rulesUnary lab).(ru_leftBody)  F .
  Definition makeRRuleUnary (lab : uconnectives) :=
    fun (F:uexp) => (perp ( up  ( t_ucon lab F)) ) ** (rulesUnary lab).(ru_rightBody)  F.
  
  Definition makeLRuleBin (lab : connectives) :=
    fun (F G :uexp) => (perp ( down  ( t_bin lab F G)) ) ** (rulesBin lab).(rb_leftBody)  F G.
  Definition makeRRuleBin (lab : connectives) :=
    fun (F G :uexp) => (perp ( up  ( t_bin lab F G)) ) ** (rulesBin lab).(rb_rightBody)  F G.

  Definition makeLRuleQ (lab : quantifiers) :=
    fun FX => ( perp ( down  ( t_quant lab FX))) ** (rulesQ lab).(rq_leftBody) FX.

  Definition makeRRuleQ (lab : quantifiers) :=
    fun FX => ( perp ( up  ( t_quant lab FX))) ** (rulesQ lab).(rq_rightBody) FX.
  
  (** *** Bipoles *)
  (** We give a general definition of the bipoles that may appear
      in the specification of object logics. Left and right
      introduction rules are considered as well as one/two premises
      rules. *)
  

  
  Hint Unfold makeLRuleConstant makeRRuleConstant makeLRuleUnary makeRRuleUnary makeLRuleBin makeRRuleBin makeLRuleQ makeRRuleQ : core.

  (** This is the FLL logical theory including the right and left
    rules for the connectives and the quantifiers *)
  Inductive buildTheory  : oo ->  Prop :=
  | bcteR : forall C, isOLFormula (t_cons C) -> buildTheory (makeRRuleConstant C)
  | bcteL : forall C, isOLFormula (t_cons C) -> buildTheory (makeLRuleConstant C)
  | buconnR : forall C F, isOLFormula ( t_ucon C F) -> buildTheory  (makeRRuleUnary C F)
  | buconnL : forall C F, isOLFormula ( t_ucon C F) -> buildTheory  (makeLRuleUnary C F)
  | bconnR : forall C F G, isOLFormula ( t_bin C F G) -> buildTheory  (makeRRuleBin C F G)
  | bconnL : forall C F G, isOLFormula ( t_bin C F G) -> buildTheory  (makeLRuleBin C F G)
  | bQconnR : forall C FX, isOLFormula  (t_quant C FX)  -> buildTheory  (makeRRuleQ C FX)
  | bQconnL : forall C FX, isOLFormula  (t_quant C FX)  -> buildTheory  (makeLRuleQ C FX) .

  Section Bipoles.
    Variable theory : oo -> Prop.
    Variable Gamma : multiset oo. (* classical context *)
    Variable Delta : multiset oo. (* linear context *)
    
    (** The following definition determines the possible shapes of
    derivation when a bipole is focused on. We consider four cases:

- [GenericBiPoleFail] when the sequent is not provable (e.g., this is
  useful when encoding the rule for falsity on the left (no rule)
- [GenericBiPoleAxiom] when the sequent must finish immediately (e..g,
  when the falsity-left rule is encoded
- [GenericBiPole1P] when the derivation must produce a unique premise
- [GenericBiPole2PM] when the bipole produces two premises and the
  context is split (multiplicative case )
- [GenericBiPole2PA] when the bipole produces two premises and the
  context is shared (additive case )
     *)
    

    (** Case No Provable *)
    Definition GenericBiPoleFail
               (connective : uexp) (* connective applied to the argument *)
               (Rule :  oo)
               (predicate : uexp -> atm) : Prop :=
      forall n,
        seqN theory n Gamma Delta ( >> Rule) -> False .

    (** Case of 0 premise *)
    Definition GenericBiPoleAxiom
               (connective : uexp) (* connective applied to the argument *)
               (Rule :  oo)
               (RBody : oo)
               (predicate : uexp -> atm) : Prop :=
      forall n,
        seqN theory n Gamma Delta ( >> Rule) ->
        isOLFormula connective ->
        ( (* case the atom is taken from the linear context *)
          (
            exists D1,
              Permutation Delta ( atom (predicate connective ) :: D1) /\
              (seq theory  Gamma D1 ( >> RBody)) /\
              forall Delta1 Gamma1 (theory' : oo -> Prop),
                (theory'  (Rule)) ->
                (seq theory' Gamma1  ( atom (predicate ((connective)) ) :: Delta1) (> [])))
          \/
          ( (* case the atom is taken from the classical context *)
            In (atom ( predicate connective )) Gamma /\
            (seq theory  Gamma Delta ( >> RBody)) /\
            forall Delta1 Gamma1 (theory' : oo -> Prop),
              (theory'  Rule) ->
              In ( atom (predicate (connective) )) Gamma1 ->
              (seq theory' Gamma1 Delta1 (> [])))
        ).

    
    (** Case of 1 premise *)
    Definition GenericBiPole1P
               (connective : uexp) (* connective applied to the argument *)
               (Rule :  oo)
               (RBody : oo)
               (predicate : uexp -> atm) : Prop :=
      forall n,
        seqN theory n Gamma Delta ( >> Rule) ->
        isOLFormula connective ->
        exists D1' B1' n' n'',    
          IsPositiveAtomFormulaL D1' /\ (* extra atoms added by the rule *)
          IsPositiveAtomFormulaL B1' /\ (* extra atoms added by the rule *)
          ( (* case the atom is taken from the linear context *)
            (
              exists D1,
                Permutation Delta ( (atom (predicate connective )) :: D1) /\
                (seq theory  Gamma D1 ( >> RBody)) /\
                (seqN theory n' (Gamma ++ B1') (D1 ++ D1') ( > []))  /\
                n'' > 0 /\
                n = plus n' n'' /\
                forall Delta1 Gamma1 (theory' : oo -> Prop),
                  (theory'  (Rule)) ->
                  (seq theory' (Gamma1 ++ B1') (Delta1 ++ D1') (> [])) ->
                  (seq theory' (Gamma1 ) ( (atom (predicate ((connective)) )) :: Delta1) (> [])))
            \/
            ( (* case the atom is taken from the classical context *)
              In (atom (predicate (connective) )) Gamma /\
              (seq theory  Gamma Delta ( >> RBody)) /\
              (seqN theory n' (Gamma ++ B1') (Delta ++ D1') ( > []))  /\
              n'' > 0 /\
              n = plus n'  n'' /\
              forall Delta1 Gamma1 (theory' : oo -> Prop),
                (theory'  Rule) ->
                In (atom (predicate (connective) )) Gamma1 ->
                (seq theory' (Gamma1 ++ B1') (Delta1 ++ D1') (> [])) ->
                (seq theory' Gamma1 Delta1 (> [])))
          ).
    
    
    (** Case of 2 premises (multiplicative case) *)
    Definition GenericBiPole2PM
               (connective : uexp)
               (Rule : oo)
               (RBody : oo)
               (predicate : uexp -> atm) : Prop :=
      forall n,
        seqN theory n Gamma Delta ( >> Rule) ->
        isOLFormula connective ->
        exists D1 D2 D1' D2' B1' B2'  n' n'',
          IsPositiveAtomFormulaL D1' /\
          IsPositiveAtomFormulaL D2' /\
          IsPositiveAtomFormulaL B1' /\
          IsPositiveAtomFormulaL B2' /\
          ( (* Atom taken from the linear context *)
            (
              Permutation Delta ( atom ((predicate connective )) :: (D1 ++ D2)) /\
              (seq theory  Gamma (D1 ++ D2) ( >> RBody)) /\
              (seqN theory n' (Gamma ++ B1') (D1 ++ D1') ( > [])) /\
              (seqN theory n' (Gamma ++ B2') (D2 ++ D2') ( > [])) /\
              n'' > 0 /\
              n = plus n' n'' /\
              forall Delta1 Delta2 Gamma1 (theory' : oo -> Prop),
                (theory'  (Rule)) ->
                (seq theory' (Gamma1 ++ B1') (Delta1 ++ D1') (> [])) ->
                (seq theory' (Gamma1 ++ B2') (Delta2 ++ D2') (> [])) ->
                (seq theory' Gamma1 ( atom ((predicate ( connective) )) :: Delta1 ++ Delta2) (> []))
            )
            \/
            ( (* atom taken from the classical context *)
              In (atom (predicate (connective) )) Gamma  /\
              Permutation Delta (D1 ++ D2) /\
              (seq theory  Gamma (D1 ++ D2) ( >> RBody)) /\
              (seqN theory n' (Gamma ++ B1') (D1 ++ D1') ( > [])) /\
              (seqN theory n' (Gamma ++ B2') (D2 ++ D2') ( > [])) /\
              n'' > 0 /\
              n = plus n' n'' /\
              forall Delta1 Delta2 Gamma1 (theory' : oo -> Prop),
                (theory'  Rule) ->
                In (atom (predicate (connective) )) Gamma1 ->
                (seq theory' (Gamma1 ++ B1') (Delta1 ++ D1') (> [])) ->
                (seq theory' (Gamma1 ++ B2') (Delta2 ++ D2') (> [])) ->
                (seq theory' Gamma1 (Delta1 ++ Delta2) (> []))
          )).

    (** Case of 2 premises (additive case) *)
    Definition GenericBiPole2PA
               (connective : uexp)
               (Rule : oo)
               (RBody : oo)
               (predicate : uexp -> atm) : Prop :=
      forall n,
        seqN theory n Gamma Delta ( >> Rule) ->
        isOLFormula connective ->
        exists D12 D1' D2' B1' B2'  n' n'',
          IsPositiveAtomFormulaL D1' /\
          IsPositiveAtomFormulaL D2' /\
          IsPositiveAtomFormulaL B1' /\
          IsPositiveAtomFormulaL B2' /\
          ( (* Atom taken from the linear context *)
            (
              Permutation Delta ( atom ((predicate connective )) :: D12) /\
              (seq theory  Gamma D12 ( >> RBody)) /\
              (seqN theory n' (Gamma ++ B1') (D12 ++ D1') ( > [])) /\
              (seqN theory n' (Gamma ++ B2') (D12 ++ D2') ( > [])) /\
              n'' > 0 /\
              n = plus n' n'' /\
              forall Delta12 Gamma1 (theory' : oo -> Prop),
                (theory'  (Rule)) ->
                (seq theory' (Gamma1 ++ B1') (Delta12 ++ D1') (> [])) ->
                (seq theory' (Gamma1 ++ B2') (Delta12 ++ D2') (> [])) ->
                (seq theory' Gamma1 ( atom ((predicate ( connective) )) :: Delta12) (> []))
            )
            \/
            ( (* atom taken from the classical context *)
              In (atom (predicate (connective) )) Gamma  /\
              Permutation Delta D12 /\
              (seq theory  Gamma D12 ( >> RBody)) /\
              (seqN theory n' (Gamma ++ B1') (D12 ++ D1') ( > [])) /\
              (seqN theory n' (Gamma ++ B2') (D12 ++ D2') ( > [])) /\
              n'' > 0 /\
              n = plus n' n'' /\
              forall Delta12 Gamma1 (theory' : oo -> Prop),
                (theory'  Rule) ->
                In (atom (predicate (connective) )) Gamma1 ->
                (seq theory' (Gamma1 ++ B1') (Delta12 ++ D1') (> [])) ->
                (seq theory' (Gamma1 ++ B2') (Delta12 ++ D2') (> [])) ->
                (seq theory' Gamma1 Delta12 (> []))
          )).
    

    
    Inductive BipoleEnum :=  BOneP | BTwoPM | BTwoPA .
    Inductive BipoleEnumCte :=  BCFail | BCAxiom | BCOneP .

    Definition sideConstant (s:Side) :=
      match s with
      | Left => (makeLRuleConstant,  rc_leftBody, down)
      | Right => (makeRRuleConstant, rc_rightBody, up)
      end.
    
    Definition sideUnary (s:Side) :=
      match s with
      | Left => (makeLRuleUnary,  ru_leftBody, down)
      | Right => (makeRRuleUnary, ru_rightBody, up)
      end.

    Definition sideBinary (s:Side) :=
      match s with
      | Left => (makeLRuleBin, rb_leftBody, down)
      | Right => (makeRRuleBin, rb_rightBody, up)
      end.

    Definition sideQuantifier (s:Side) :=
      match s with
      | Left => (makeLRuleQ, rq_leftBody, down)
      | Right => (makeRRuleQ, rq_rightBody, up)
      end.

    Definition BiPoleCte (lab: constants) (s:Side) (t : BipoleEnumCte): Prop :=
      match (sideConstant s) with
      | (rule, body, pred) =>
        match t with
        | BCFail => GenericBiPoleFail (t_cons lab) (rule lab)  pred
        | BCAxiom => GenericBiPoleAxiom  (t_cons lab) (rule lab) ((rulesCte lab).(body)) pred
        | BCOneP => GenericBiPole1P (t_cons lab) (rule lab) ( (rulesCte lab).(body) ) pred
        end
      end.
    
    Definition BiPoleUnary (lab: uconnectives) (s:Side) (t : BipoleEnum): Prop :=
      match (sideUnary s) with
      | (rule, body, pred) =>
        match t with
        | BOneP => forall Fo1, GenericBiPole1P (t_ucon lab Fo1) (rule lab Fo1) ( (rulesUnary lab).(body) Fo1) pred
        | BTwoPM => forall Fo1, GenericBiPole2PM (t_ucon lab Fo1) (rule lab Fo1) ( (rulesUnary lab).(body) Fo1) pred
        | BTwoPA => forall Fo1, GenericBiPole2PA (t_ucon lab Fo1) (rule lab Fo1) ( (rulesUnary lab).(body) Fo1) pred
        end
      end.
    
    

    Definition BiPoleBinary (lab: connectives) (s:Side) (t : BipoleEnum): Prop :=
      match (sideBinary s) with
      | (rule, body, pred) =>
        match t with
        | BOneP => forall Fo1 Go1, GenericBiPole1P (t_bin lab Fo1 Go1) (rule lab Fo1 Go1) ( (rulesBin lab).(body) Fo1 Go1) pred
        | BTwoPM => forall Fo1 Go1, GenericBiPole2PM (t_bin lab Fo1 Go1) (rule lab Fo1 Go1) ( (rulesBin lab).(body) Fo1 Go1) pred
        | BTwoPA => forall Fo1 Go1, GenericBiPole2PA (t_bin lab Fo1 Go1) (rule lab Fo1 Go1) ( (rulesBin lab).(body) Fo1 Go1) pred
        end
      end.

    Definition BiPoleQuantifier (lab: quantifiers) (s:Side) (t : BipoleEnum): Prop :=
      match (sideQuantifier s) with
      | (rule, body, pred) =>
        match t with
        | BOneP => forall FX, uniform FX /\ GenericBiPole1P (t_quant lab FX) (rule lab FX) ( (rulesQ lab).(body) FX) pred
        | BTwoPM => forall FX, uniform FX /\ GenericBiPole2PM (t_quant lab FX) (rule lab FX) ( (rulesQ lab).(body) FX) pred
        | BTwoPA => forall FX, uniform FX /\ GenericBiPole2PA (t_quant lab FX) (rule lab FX) ( (rulesQ lab).(body) FX) pred
        end
      end. 
  End Bipoles.

  Hint Unfold BiPoleCte BiPoleUnary BiPoleBinary BiPoleQuantifier : core .

  
  (** INIT and CUT rules *)
  Definition RINIT (F:uexp) : oo := (perp (up  F) )  ** (perp (down F) ) .
  Definition RCUT  (F:uexp) : oo := (atom (up  F) )  ** (atom (down F) ).
  (** Allowing contraction and weakening on the left side of the sequent *)
  Definition POS F := ((perp (down F)) ** ? atom (down F)).
  (** Allowing contraction and weakening on the right side of the sequent *)
  Definition NEG F := ((perp (up F)) ** ? atom (up F)).
  
  Hint Unfold RINIT RCUT : core.

  (** Structural rules *)
  Inductive StrRules : oo -> Prop :=
  | str_cut : forall F, isOLFormula F -> StrRules (RCUT F)
  | str_init : forall F, isOLFormula F -> StrRules (RINIT F)
  .

  Inductive StrRulesPos : oo -> Prop :=
  | stp_cut : forall F, isOLFormula F -> StrRulesPos (RCUT F)
  | stp_init : forall F, isOLFormula F -> StrRulesPos (RINIT F)
  | stp_pos : forall F, isOLFormula F -> StrRulesPos (POS F)
  .

  (** The theory with INIT and CUT *)
  Inductive theoryInitCut : oo -> Prop :=
  | prIC_init : forall (F: uexp) , isOLFormula F -> theoryInitCut (RINIT F)
  | prIC_cut : forall (F: uexp) , isOLFormula F -> theoryInitCut (RCUT F) .

  (** A theory including only [RCUT] *)
  Inductive theoryCut : oo -> Prop :=
  | prC_cut : forall (F: uexp) , isOLFormula F -> theoryCut (RCUT F) .

  Hint Constructors StrRulesPos StrRules theoryInitCut theoryCut : core.
  
  Theorem StrStrPoEmb : forall F, StrRules F -> StrRulesPos F.
    intros.
    inversion H;subst;auto.
  Qed.

  Theorem StrRulesFormulas : forall F,  StrRules F -> isFormula F.
    intros.
    inversion H;subst;auto.
    constructor;auto.
    constructor;auto.
  Qed.

  Theorem StrRulesPosFormulas : forall F,  StrRulesPos F -> isFormula F.
    intros.
    inversion H;subst;auto.
    constructor;auto.
    constructor;auto.
    constructor;auto.
  Qed.

  (** [up] and [down] can be proved to be dual using the rules [RINIT] and [RCUT] *)
  Section Dualities.

    Definition down' : uexp -> atm := down.
    Definition up' : uexp -> atm := up.
    Hint Unfold down' up' : core .


    (* Cut and Init proves The dualities *)
    Theorem UpDownDuality1 : forall (th : oo -> Prop)  F,
        isOLFormula F -> (th (RINIT F)) -> (th (RCUT F)) ->
        (seq th [] [] (> [ perp (up F) ; perp (down F) ])).
    Proof with solveF.
      intros th F isF HInit HCut.
      solveLL'.
      bipole' (RCUT F).
    Qed.

    Theorem UpDownDuality1' : forall  F G, isOLFormula F -> 
                                           (seq StrRulesPos G [ perp (up F) ; perp (down F) ] (> [] )).
    Proof with solveF.
      intros.
      assert (seq StrRulesPos G [] (> [ perp (up F) ; perp (down F) ] )).
      assert (seq StrRulesPos [] [] (> [perp (up F); perp (down F)])). apply UpDownDuality1;auto.
      change G with ([] ++ G).
      rewrite Permutation_app_comm.
      eapply weakeningGen;auto.
      InvTriAll';auto.
    Qed.

    Theorem UpDownDuality2 : forall (th : oo -> Prop)  F, isOLFormula F -> (th (RINIT F)) -> (th (RCUT F)) ->
                                                          (seq th [] [] (> [ atom (up F) ; atom (down F) ])).
    Proof with solveF.
      intros th F isF HInit HCut.
      solveLL'.
      bipole' (RINIT F).
    Qed.

    Theorem UpDownDuality2' : forall (th : oo -> Prop)  F, isOLFormula F -> (th (RINIT F)) -> (th (RCUT F)) ->
                                                           (seq th [] [ atom (up F) ; atom (down F) ] (> [])).
    Proof with solveF.
      intros th F isF HInit HCut.
      solveLL'.
      bipole' (RINIT F).
    Qed.

    (** Some theorems allowing us to change from [atom (up F)] to
    [perp (down F)] and vice-versa *)
    Theorem DualityCut1 : forall  G D F,
        isOLFormula F -> isFormulaL G -> isFormulaL D -> isNotAsyncL D ->
        (seq StrRulesPos G ( (atom (up F)) :: D) (> [])) ->
        (seq StrRulesPos G ( (perp (down F)) :: D) (> [])).
    Proof with solveF.
      intros G D F isF isG isD isNotAsyncD HSeq.
      change down with down'.
      change (perp (down' F) :: D) with ( [ perp (down' F)] ++  D).
      eapply GeneralCut' with (dualC:= atom (up' F) ) (C:=  perp (up' F)) ; SolveIsFormulas.
      eauto using StrRulesPosFormulas, IsPositiveAtomNotAsync, IsPositiveIsFormula.
      solveLL'.
      rewrite perm_swap.
      apply UpDownDuality1';auto.
      solveLL'.
      rewrite <- Permutation_cons_append;auto.
    Qed.

    Theorem DualityCut2 : forall  G D F,
        isOLFormula F -> isFormulaL G -> isFormulaL D -> isNotAsyncL D ->
        (seq StrRulesPos G ( (perp (down F)) :: D) (> [])) ->
        (seq StrRulesPos G ( (atom (up F)) :: D) (> [])).
    Proof with solveF.
      intros G D F isF isG isD isNotAsyncD HSeq.
      change up with up'.
      change (atom (up' F) :: D) with ( [ atom (up' F)] ++  D).
      rewrite <- Permutation_app_comm;auto.
      eapply GeneralCut' with (dualC:= atom (down' F) ) (C:=  perp (down' F)) ; SolveIsFormulas.
      eauto using StrRulesPosFormulas, IsPositiveAtomNotAsync, IsPositiveIsFormula.
      solveLL'.
      rewrite <- Permutation_cons_append;auto.
      solveLL'.
      change G with ([] ++ G).
      rewrite Permutation_app_comm.
      eapply weakeningGen;auto.
      apply UpDownDuality2';auto.
    Qed.

    Theorem DualityCut3 : forall  G D F,
        isOLFormula F -> isFormulaL G -> isFormulaL D -> isNotAsyncL D ->
        (seq StrRulesPos G ( (perp (up F)) :: D) (> [])) ->
        (seq StrRulesPos G ( (atom (down F)) :: D) (> [])).
    Proof with solveF.
      intros G D F isF isG isD isNotAsyncD HSeq.
      change down with down'.
      change (atom (down' F) :: D) with ( [ atom (down' F)] ++  D).
      rewrite Permutation_app_comm.
      eapply GeneralCut' with (dualC:= atom (up' F) ) (C:=  perp (up' F)) ; SolveIsFormulas.
      eauto using StrRulesPosFormulas, IsPositiveAtomNotAsync, IsPositiveIsFormula.
      solveLL'.
      rewrite Permutation_app_comm...
      solveLL'.
      ExchangeFront' 2.
      change G with ([] ++ G).
      rewrite Permutation_app_comm.
      eapply weakeningGen;auto.
      apply UpDownDuality2'...
    Qed.

    Theorem DualityCut4 : forall  G D F,
        isOLFormula F -> isFormulaL G -> isFormulaL D -> isNotAsyncL D ->
        (seq StrRulesPos G ( (atom (down F)) :: D) (> [])) ->
        (seq StrRulesPos G ( (perp (up F)) :: D) (> [])).
    Proof with solveF.
      intros G D F isF isG isD isNotAsyncD HSeq.
      change up with up'.
      change (perp(up' F) :: D) with ( [perp (up' F)] ++  D).
      eapply GeneralCut' with (dualC:= atom (down' F) ) (C:=  perp (down' F)) ; SolveIsFormulas.
      eauto using StrRulesPosFormulas, IsPositiveAtomNotAsync, IsPositiveIsFormula.
      solveLL'.
      apply UpDownDuality1'...
      solveLL'.
      rewrite Permutation_app_comm...
    Qed.


    Theorem DualityCut4C : forall  G D F,
        isOLFormula F -> isFormulaL G -> isFormulaL D -> isNotAsyncL D ->
        (seq StrRulesPos ((atom (down F)) :: G) D (> [])) ->
        (seq StrRulesPos ((perp (up F)) :: G)  D (> [])).
    Proof with solveF.
      intros G D F isF isG isD isNotAsyncD HSeq.
      change D with ([] ++ D).
      rewrite Permutation_app_comm.
      eapply GeneralCut' with (C:= ? (atom (down' F)) ) (dualC:=  ! (perp (down' F))) ; SolveIsFormulas.
      eauto using StrRulesPosFormulas, IsPositiveAtomNotAsync, IsPositiveIsFormula.
      solveLL'.
      simpl.
      apply weakening.
      rewrite Permutation_app_comm...
      solveLL'.
      apply DualityCut1;SolveIsFormulas.
      decide2' (perp (up F)) .
    Qed.

  End Dualities. 

  
  
  (** The cut rule applied on object level terms of a given size  *)
  Inductive CutRuleN (n:nat) : oo -> Prop :=
  | ctn : forall (F:uexp) m , isOLFormula F ->
                              lengthUexp F m -> m <= n ->
                              CutRuleN n (RCUT F). 
  Hint Constructors CutRuleN : core.

  Lemma CuteRuleNBound : forall h n B L X ,  seqN (CutRuleN n) h B L X ->
                                             forall m, n<=m -> seq (CutRuleN m) B L X .
  Proof with solveF.
    induction h using strongind ; intros.
    inversion H ...
    inversion H0;solveF;
      repeat match goal with
             | [ Hs : seqN (CutRuleN n) h ?B1 ?N1 ?X1 |- _] =>
               let Hs1 := fresh in
               assert (Hs1 : seq (CutRuleN m) B1 N1 X1) by
                   (
                     eapply H  with (m:= h) (n:= n)  (m0:=m) (B:= B1);solveF 
                   );clear Hs
             end;solveLL';auto.

    rewrite H3. tensor' M N...
    decide1' F;eauto ...
    decide2' F;eauto ...
    decide3' F;eauto ...
    inversion H3...
    apply ctn with (m:= m0)...
    existential' t.
    apply H4 in properX.
    eapply H with (m0:=m) in properX... 
  Qed.

  Lemma CuteRuleNBound' : forall n B L X ,
      seq (CutRuleN n)  B L X ->
      forall m, n<=m -> seq (CutRuleN m) B L X .
    intros.
    apply seqtoSeqN in H. destruct H.
    eapply CuteRuleNBound;eauto.
  Qed.
  

  (** There are no (object logic) formulas of size 0 *)
  Lemma CuteRuleN0 : forall F, ~ (CutRuleN 0 F).
  Proof with solveF.
    intros F Hn.
    inversion Hn...
    generalize (LengthFormula H H0); intro. omega.
  Qed.
  
  
  (** CUT-Coherence bounded with the size of the cut *)

  Definition CutCoherenceCte (R: ruleCte) :=
    seq EmptyTheory [] [] (> [dual ( R.(rc_rightBody) ) ; dual (R.(rc_leftBody)  )]).
  
  Definition CutCoherenceUnary (R: ruleUnary) :=
    forall F n,  lengthUexp F n ->
                 isOLFormula F ->
                 seq (CutRuleN n) [] [] (> [dual ( R.(ru_rightBody) F ) ; dual (R.(ru_leftBody) F )]).
  
  Definition CutCoherenceBin (R: ruleBin) :=
    forall F G n m,  lengthUexp F n ->
                     lengthUexp G m ->
                     isOLFormula F -> isOLFormula G->
                     seq (CutRuleN (max n m)) [] [] (> [dual ( R.(rb_rightBody) F G) ; dual (R.(rb_leftBody) F G)]).

  (** CUT-Coherence for quantifiers *)
  Definition CutCoherenceQ (R: ruleQ) :=
    forall FX FX' n ,  uniform FX -> uniform FX' ->
                       ext_eq FX FX' ->
                       lengthUexp (FX (Var 0))  n ->
                       (forall t, proper t -> isOLFormula (FX t)) -> 
                       seq (CutRuleN n) [] [] (> [ dual(R.(rq_rightBody) FX) ; dual(R.(rq_leftBody) FX') ]) .

  
  (** CUT-Coherence for the wholse Object logic *)
  Definition CutCoherence  : Prop :=
    (forall (lab : constants), CutCoherenceCte (rulesCte lab)) /\
    (forall (lab : uconnectives), CutCoherenceUnary (rulesUnary lab)) /\
    (forall (lab : connectives), CutCoherenceBin (rulesBin lab)) /\
    (forall (lab : quantifiers), CutCoherenceQ (rulesQ lab)).
  


  (** A well-formed theory consists of rules that are cut-coherent
    and each rule is either a one-premise or a two-premises rule that
    satisfy the predicates [BiPole] *)

  Definition wellFormedCte :Prop :=
    forall Theory Gamma Delta (lab: constants) (s:Side),
    exists (t: BipoleEnumCte), BiPoleCte Theory Gamma Delta lab s t.
  Definition wellFormedUnary: Prop :=
    forall Theory Gamma Delta (lab: uconnectives) (s:Side),
    exists (t : BipoleEnum),  BiPoleUnary Theory Gamma Delta lab s t.

  Definition wellFormedBinary: Prop :=
    forall Theory Gamma Delta (lab: connectives) (s:Side),
    exists (t : BipoleEnum),  BiPoleBinary Theory Gamma Delta lab s t.

  (* We assume that quantifiers are encoded with one premise bipoles *)
  Definition wellFormedQuantifier: Prop :=
    forall Theory Gamma Delta (lab: quantifiers) (s:Side),
      BiPoleQuantifier Theory Gamma Delta lab s BOneP.

  Definition wellFormedTheory  : Prop :=
    wellFormedCte /\ wellFormedUnary /\ wellFormedBinary /\ wellFormedQuantifier .
  

  Definition wellTheory : Prop := CutCoherence  /\ wellFormedTheory.
  Hint Unfold CutCoherenceBin CutCoherenceQ  CutCoherence wellFormedCte wellFormedUnary wellFormedBinary wellFormedQuantifier wellTheory  : core .
  
  
  (** A theory with only with the object logic rules *)
  Inductive OLTheory   : oo -> Prop :=
  | ooth_rules : forall OO, buildTheory OO ->  OLTheory OO
  .

  (** A theory including cuts of size [n] *)
  Inductive OLTheoryCut (n:nat) : oo -> Prop :=
  | oothc_theory : forall OO, buildTheory OO ->  OLTheoryCut n OO
  | oothc_cutn : forall OO, CutRuleN n OO -> OLTheoryCut n OO
  .
  
  Hint Constructors  OLTheoryCut OLTheory : core.

  (** Inversion lemmas when [RINI] is used *)
  Lemma Init_inversion1 : forall h Gamma N M F1 F2,
      IsPositiveAtomFormulaL M ->
      IsPositiveAtomFormulaL N ->
      IsPositiveAtomFormulaL Gamma ->
      seqN OLTheory h Gamma ((atom (up F1) ) :: N) (>> RINIT F2) ->
      F1 = F2 /\ (N = [ atom (down F1) ] \/ (N = [] /\ In (atom (down F1) ) Gamma)).
  Proof with subst;solveF.
    intros.
    InvTriAll;CleanContext.
    clear H2 H3.
    {
      (*apply SplitAppPermute in H6.
              rewrite H6 in H5.*)
      apply PermutationInCons in H5 as H5'.
      inversion H5'...
      split...
      simpl in H5.
      apply Permutation_cons_inv in H5.
      apply Permutation_sym in H5.
      apply Permutation_unq in H5...
    }
    {
      (*apply SplitAppPermute in H6.
              rewrite H6 in H5;simpl in H5.*)
      apply Permutation_sym in H5.
      apply Permutation_unq in H5...
      inversion H5...
    }
    {
      (*apply SplitAppPermute in H6.
              rewrite H6 in H5; simpl in  H5.*)
      apply Permutation_sym in H5.
      apply Permutation_unq in H5...
      inversion  H5...
    }
    (*apply SplitAppPermute in H6.
            rewrite H6 in H5; simpl in  H5.*)
    apply Permutation_nil' in H5.
    inversion H5.
  Qed.
  
  Lemma Init_inversion2 : forall h Gamma N M F1 F2,
      IsPositiveAtomFormulaL M ->
      IsPositiveAtomFormulaL N ->
      IsPositiveAtomFormulaL Gamma ->
      seqN OLTheory h Gamma ((atom (down F1) ) :: N) (>> RINIT F2) ->
      F1 = F2 /\ (N = [ atom (up F1) ] \/ (N = [] /\ In (atom (up F1) ) Gamma)).
  Proof with subst;solveF.
    intros.
    InvTriAll;CleanContext.
    clear H2 H3.
    { 
      (*apply SplitAppPermute in H6.
              rewrite H6 in H5.*)
      apply PermutationInCons in H5 as H5'.
      inversion H5'...
      split...
      rewrite Permutation_app_comm in H5; simpl in H5...
      apply Permutation_cons_inv in H5.
      apply Permutation_sym in H5.
      apply Permutation_unq in H5...
      
    }
    {
      apply Permutation_sym in H5.
      apply Permutation_unq in H5...
      inversion H5...
    }
    {
      apply Permutation_sym in H5.
      apply Permutation_unq in H5...
      inversion  H5...
    }
    apply Permutation_nil' in H5.
    
    inversion H5.
  Qed.
  
  (** Some easy equivalences on the  above theories *)
  Lemma OOTheryCut0 : forall F, OLTheory F <-> (OLTheoryCut 0) F.
    intros.
    split;intro H ;inversion H;subst;auto.
    inversion H0.
    assert (m =  0) by omega;subst.
    generalize (LengthFormula H1 H2);intro. omega.
  Qed.

  
  Lemma TheoryEmb1 : forall n F  , OLTheory F -> (OLTheoryCut n) F.
    intros. 
    inversion H;subst;constructor;auto.
  Qed.

  
  Lemma TheoryEmb2 : forall n F  , ((CutRuleN n) F) -> (OLTheoryCut) n F.
    intros.
    inversion H;subst.
    apply oothc_cutn;auto.
  Qed.
End Bipoles.

(** ** Some useful tactics for proving cut-coherence and bipole conditions in Object Logics *)

(** This tactic solves the case when the bipole belongs to the Fail
Case *)
Ltac WFFailSolver :=
  match goal with
    [ |- BiPoleCte _ _ _ _ _ BCFail ]=>
    let n := fresh "n" in
    let HSeq := fresh "Hseq" in
    intros n HSeq;
    autounfold in HSeq;
    InvTriAll
  end.

(** This tactic is useful when performing proofs of cut-coherence and
well-formedness *)
Ltac WFSolver :=
  autounfold in *;
  simpl in *;
  try(match goal with
      | [ |- _ /\ _ ] => split;WFSolver
      end);
  try rewrite app_nil_r in *;
  solveF;
  try intros;
  try lia;
  solveLL';
  solveLL;
  repeat(
      match goal with
        
      | [ |-  IsPositiveAtomFormulaL _ ] => first[ constructor ;solveF |  IsPositiveLSolve]
      | [ |- Forall IsPositiveAtomFormula ?M] => fold  (IsPositiveAtomFormulaL M)
      | [ _ : seqN _ _ ?G ?M ?X |-  seq _ ?G ?M ?X ] => eauto using seqNtoSeq
      | [ |- seqN _ _ _ _ _] => solve [eauto]
      | [H: seqN _ _ _ ((_ ++ [_]) ++ [_]) (> []) |- _ ] =>  rewrite <- Per_app_assoc in H
      | [|- seq _ _ ((_ ++ [_]) ++ [_]) (> []) ] =>  rewrite <- Per_app_assoc;simpl
      end);
  try(
      match goal with
        [ His: isOLFormula _ |- IsPositiveAtomFormula _ ] =>
        inversion His;subst;
        try(match goal with
            |[ H: isOLConstant (t_ucon _ _)|-_] => inversion H
            |[ H: isOLConstant (t_bin _ _ _)|-_] => inversion H  end);
        constructor ; solveF
      | [ His: isOLFormulaL _ |- IsPositiveAtomFormula _ ] =>
        inversion His;subst;
        try(match goal with
            |[ H: isOLConstant (t_ucon _ _)|-_] => inversion H
            |[ H: isOLConstant (t_bin _ _ _)|-_] => inversion H  end);
        constructor ; solveF
      end);auto.
