(** * OL-Cut Elimination  *)

(** The procedure formalized here is tailored to the case of
object-logics (OL) where formulas on both the left and the right side
of the sequent can be weakened and contacted. Then, we assume that all
of them are stored into the classical context of LL.

Unlike the file [OLCutelimination] here we do not consider the
quantifiers at the object-level nor unary connectives.

We shall call to this kind of logics POSNEG-logics due to the POS rule
[left(F)^ * ?left(F)] that allows to store a left formula into the
classical context and the NEG rule [right(F)^ * ?right(F)] that stores
right formulas into the classical context.

 *)

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
Hint Constructors  OLTheoryCut OLTheory : core.

(** ** Rules of the encoded proof system *)
Section OLInferenceRules.
  Context `{OL: OLSyntax}.
  Inductive Side := Left | Right .

  (** Constants in the case of POS systems only can be TOP/ZERO or
  ZERO/TOP *)
  Inductive ContantEnc := TOPZERO | ZEROTOP .

  Definition CteRulesDefs (t:ContantEnc) (s:Side):=
    match t,s with
    | TOPZERO, Left => top
    | ZEROTOP, Left => zero
    | TOPZERO, Right => zero
    | ZEROTOP, Right => top
    end.


  (** In systems with POS and NEG, the kind of connectives used, in order to
  be cut-coherent, is also more restricted. Here the options
  available:       
                        
   - [PARTENSOR]: On the left rule, it takes the atom [A * B] and
   produces one premise containing both [A] and [B] (stored in the
   classical context). In the right rule, it generates two
   premises. This is the typical encoding for conjuction-like
   connectives.
   
   - [TENSORPAR]: On the left rule, it generates two premises and, on
   the right side, it generates only one premise. This is the typical
   encoding for disjunction-like connectives.

   - [TENSORPAREXCH]: Similar to the previous one but [A] goes to the
   right premise and [B] to the left premise. This is the typical
   encoding for a implication-like connective.

In all the cases, note that the subformulas are stored into the
classical context.
                                              
*)

  Inductive RulesEnc := PARTENSOR | TENSORPAR | TENSORPAREXCH .
  Definition RulesDefs (t:RulesEnc) (s:Side) (A B : uexp):=
    match t,s with
    | PARTENSOR, Left => (? d|A|) $ (? d|B|)
    | PARTENSOR, Right => ( ? u|A|) ** ( ? u|B|)
    | TENSORPAR, Left => (? d|A|) ** (? d|B|)
    | TENSORPAR, Right => ( ? u|A|) $ ( ? u|B|)
    | TENSORPAREXCH, Left => (? u|A|) ** (? d|B|)
    | TENSORPAREXCH, Right => (? d|A|) $ (? u|B|)
    end.
  

  (** Cut Rule storing the left formulas into the classical context *)
  Definition RCUTPOSNEG  (F:uexp) : oo := (? d|F|)  ** (? u|F|).

  (** The cut rule applied on object level terms of a given size  *)
  Inductive CutRulePOSNEGN (n:nat) : oo -> Prop :=
  | ctn : forall (F:uexp) m , isOLFormula F ->
                              lengthUexp F m -> m <= n ->
                              CutRulePOSNEGN n (RCUTPOSNEG F).

  (** We assume an external definition mapping each
    connective/quantifier with a left and right rule *) 
  Class OORules :=
    {
      (* TOPZERO means TOP for the left encoding and ZERO for the
      right encoding *)
      rulesCte : constants -> ContantEnc ; 
      rulesBin : connectives -> RulesEnc
    }.
End OLInferenceRules.

Section CutCoherence.
  Context `{OLR: OORules}.

  Hint Constructors CutRulePOSNEGN : core.
  
  (** Now we can prove that all the above definitions are cut-coherent
  in the sense below *)
  Theorem CutCoherenceCte (cte: ContantEnc) :
    seq EmptyTheory [] [] (> [dual ( CteRulesDefs cte Left );? dual ( CteRulesDefs cte Right ) ]).
  Proof with solveF.
    intros.
    destruct cte...
    solveLL'.
    decide2' top;solveLL'.
  Qed.

  Theorem CutCoherenceRules (R: RulesEnc) (A B : uexp) (n m : nat) :
    lengthUexp A n ->
    lengthUexp B m ->
    isOLFormula A ->
    isOLFormula B ->
    seq (CutRulePOSNEGN (max n m)) [] [] (> [ dual ( RulesDefs R Left A B );  dual ( RulesDefs R Right A B)]).
  Proof with solveF.
    intros.
    destruct R; simpl.
    + solveLL'...
      decide3' (RCUTPOSNEG A)...
      apply @ctn with (m:=n)...
      tensor'     [ (! d^| A |) ** (! d^| B |); ! u^| B |] [! u^| A |] .
      decide3' (RCUTPOSNEG B)...
      apply @ctn with (m:=m)...
      tensor'   [(! d^| A |) ** (! d^| B |)][! u^| B |].
      decide1' ((! d^| A |) ** (! d^| B |)).
      tensor' (@nil oo) (@nil oo).
      decide1' (d^|A|)... 
      decide1' (d^|B|)...
      decide1' (! u^|B|). 
      decide1' (u^|B|)...
      decide1' (! u^|A|).
      decide1' (u^|A|)...
    + solveLL'...
      decide3' (RCUTPOSNEG A)... 
      apply @ctn with (m:=n)...
      tensor' [! d^| A |][ ! d^| B |; (! u^| A |) ** (! u^| B |)].
      decide1' (! d^|A|).
      decide1' (d^|A|)...

      decide3' (RCUTPOSNEG B)...
      apply @ctn with (m:=m)...
      tensor' [! d^| B | ][ (! u^| A |) ** (! u^| B |)].
      decide1' (! d^|B|).
      decide1' (d^|B|)...
      decide1' ((! u^| A |) ** (! u^| B |)).
      tensor' (@nil oo) (@nil oo).
      decide1' (u^|A|) ...
      decide1' (u^|B|) ...
    + solveLL'.
      decide3' (RCUTPOSNEG A)...
      apply @ctn with (m:=n)...
      tensor' [ ! d^| B |; (! d^| A |) ** (! u^| B |)] [! u^| A |].

      decide3' (RCUTPOSNEG B)...
      apply @ctn with (m:=m)...
      tensor'  [! d^| B |] [ (! d^| A |) ** (! u^| B |)] ...
      decide1' (!d^|B|). 
      decide1' (d^|B|)...

      decide1' ((! d^| A |) ** (! u^| B |)).
      tensor' (@nil oo) (@nil oo).
      decide1' (d^|A|)...
      decide1' (u^|B|) ...

      decide1' (!u^|A|). 
      decide1' (u^|A|)...
  Qed.
End CutCoherence.

(** Building the inference rules (bipoles) *)
Section Bipoles.
  Context `{OLR: OORules}.
  
  (** building rules for constants *)
  Definition makeRuleConstant (lab : constants) (s:Side) :=
    match s with
    | Right => ( u^|t_cons lab| ) ** (CteRulesDefs (rulesCte lab) s)
    | Left => ( d^|t_cons lab| ) ** (CteRulesDefs (rulesCte lab) s)
    end.

  (** building rules for connectives *)
  Definition makeRuleBin (lab : connectives) (s:Side):=
    fun (A B :uexp) =>
      match s with
      | Right => (u^| t_bin lab A B|) ** (RulesDefs (rulesBin lab) s A B)
      | Left => (d^| t_bin lab A B|) ** (RulesDefs (rulesBin lab) s A B)
      end.

  Hint Unfold makeRuleConstant makeRuleBin  : core.

  Hint Constructors isFormula : core.
  Theorem RulesIsFormula : forall T S A B,
      isFormula ((RulesDefs T S A B) ).
    intros.
    destruct T;destruct S;simpl;auto.
  Qed.

  Theorem MRulesIsFormula : forall T S A B,
      isFormula ((makeRuleBin T S A B) ).
    intros.
    destruct S;simpl.
    constructor;auto using RulesIsFormula.
    constructor;auto using RulesIsFormula.
  Qed.
  
  Theorem RulesPerpIsFormula : forall T S A B,
      isFormula ((RulesDefs T S A B) ^).
    intros.
    destruct T;destruct S;simpl;auto.
  Qed.

  Theorem CtesIsFormula : forall C S,
      isFormula (makeRuleConstant C S).
    intros.
    destruct S;simpl;auto.
    destruct (rulesCte C);simpl;auto.
    destruct (rulesCte C);simpl;auto.
  Qed.
  
  (** This is the FLL logical theory including the right and left
    rules for the connectives and constants *)
  Inductive buildTheory  : oo ->  Prop :=
  | bcteR : forall C, isOLFormula (t_cons C) -> buildTheory (makeRuleConstant C Right)
  | bcteL : forall C, isOLFormula (t_cons C) -> buildTheory (makeRuleConstant C Left)
  | bconnR : forall C F G, isOLFormula ( t_bin C F G) -> buildTheory  (makeRuleBin C Right F G)
  | bconnL : forall C F G, isOLFormula ( t_bin C F G) -> buildTheory  (makeRuleBin C Left F G)
  .

  Lemma CuteRuleNBound : forall h n B L X ,  seqN (CutRulePOSNEGN n) h B L X ->
                                             forall m, n<=m -> seq (CutRulePOSNEGN m) B L X .
  Proof with solveF.
    induction h using strongind ; intros.
    inversion H ...
    inversion H0;solveF;
      repeat match goal with
             | [ Hs : seqN (CutRulePOSNEGN n) h ?B1 ?N1 ?X1 |- _] =>
               let Hs1 := fresh in
               assert (Hs1 : seq (CutRulePOSNEGN m) B1 N1 X1) by
                   (
                     eapply H  with (m:= h) (n:= n)  (m0:=m) (B:= B1);solveF 
                   );clear Hs
             end;solveLL';auto.

    rewrite H3. tensor' M N...
    decide1' F;eauto ...
    decide2' F;eauto ...
    decide3' F;eauto ...
    inversion H3...
    apply @ctn with (m:= m0)...
    existential' t.
    apply H4 in properX.
    eapply H with (m0:=m) in properX... 
  Qed.

  Lemma CuteRuleNBound' : forall n B L X ,
      seq (CutRulePOSNEGN n)  B L X ->
      forall m, n<=m -> seq (CutRulePOSNEGN m) B L X .
    intros.
    apply seqtoSeqN in H. destruct H.
    eapply CuteRuleNBound;eauto.
  Qed.
  
  (** There are no (object logic) formulas of size 0 *)
  Lemma CuteRuleN0 : forall F, ~ (CutRulePOSNEGN 0 F).
  Proof with solveF.
    intros F Hn.
    inversion Hn...
    generalize (LengthFormula H H0); intro.
    lia.
  Qed.

  (** A theory with only with the object logic rules *)
  Inductive OLTheory   : oo -> Prop :=
  | ooth_rules : forall OO, buildTheory OO ->  OLTheory OO
  | ooth_init : forall OO, isOLFormula OO -> OLTheory (RINIT OO) 
  .

  (** A theory including cuts of size [n] *)
  Inductive OLTheoryCut (n:nat) : oo -> Prop :=
  | oothc_theory : forall OO, buildTheory OO ->  OLTheoryCut n OO
  | oothc_init : forall OO, isOLFormula OO -> OLTheoryCut n (RINIT OO) 
  | oothc_cutn : forall OO, CutRulePOSNEGN n OO -> OLTheoryCut n OO
  .

  Hint Constructors  OLTheoryCut OLTheory  : core.
  Hint Unfold RINIT RCUTPOSNEG : core.
  Hint Constructors isFormula : core.

  (** Some easy equivalences on the  above theories *)
  Lemma OOTheryCut0 : forall F, OLTheory F <-> (OLTheoryCut 0) F.
    intros.
    split;intro H ;inversion H;subst;auto.
    inversion H0.
    assert (m =  0) by lia;subst.
    generalize (LengthFormula H1 H2);intro.
    lia.
  Qed.

  Lemma TheoryEmb1 : forall n F  , OLTheory F -> (OLTheoryCut n) F.
    intros.
    inversion H;subst; solve[constructor;auto].
  Qed.

  Lemma TheoryEmb2 : forall n F  , ((CutRulePOSNEGN n) F) -> (OLTheoryCut) n F.
    intros.
    inversion H;subst.
    apply oothc_cutn;auto.
  Qed.

  Hint Unfold down' up' : core .

  (** ** Invertibility lemmas *)
  (** In the following we prove that, when focusing on the bipole
  representing an OL rule, the derivation necessary has a specific
  shape *)

  Lemma Init_inversion1 : forall h Gamma F  th,
      IsPositiveAtomFormulaL Gamma ->
      seqN th h Gamma [] (>> RINIT F) ->
      ( (In (d| F|) Gamma) /\
        (In (u| F|) Gamma)).
  Proof with subst;solveF.
    intros.
    InvTriAll;CleanContext.
    apply Permutation_nil in H3... inversion H3.
    apply Permutation_nil in H3... inversion H3.
    apply Permutation_nil in H3... inversion H3.
  Qed.

  Theorem TENSORPARInv : forall A B Gamma n,
      ( seq (OLTheoryCut (pred n)) (d| A | :: Gamma) [] (> [])) ->
      ( seq (OLTheoryCut (pred n)) (d| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAR Left A B ) .
    intros;simpl;solveLL'.
    tensor' (@nil oo)(@nil oo).
    LLExact' H.
    LLExact' H0.
  Qed.

  Theorem TENSORPARInv' : forall A B Gamma n,
      ( seq (OLTheoryCut (pred n)) (u| A | :: u| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAR Right A B ) .
    intros;simpl;solveLL'.
    LLExact' H.
  Qed.

  Theorem TENSORPAREXCHInv : forall A B Gamma  n,
      ( seq (OLTheoryCut (pred n)) (u| A |:: Gamma) [] (> [])) ->
      ( seq (OLTheoryCut (pred n)) (d| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAREXCH Left A B ) .
    intros;simpl;solveLL'.
    tensor' (@nil oo) (@nil oo).
    LLExact' H.
    LLExact' H0.
  Qed.

  Theorem TENSORPAREXCHInv' : forall A B Gamma  n,
      ( seq (OLTheoryCut (pred n)) (d| A | :: u| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAREXCH Right A B ) .
    intros;simpl;solveLL'.
    LLExact' H.
  Qed.

  Theorem PARTensorInv : forall A B Gamma n,
      ( seq (OLTheoryCut (pred n)) (d| A | :: d| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs PARTENSOR Left A B ) .
    intros;simpl;solveLL'.
    LLExact' H.
  Qed.

  Theorem PARTensorInv' : forall A B Gamma n,
      ( seq (OLTheoryCut (pred n)) (u| A | :: Gamma) [] (> [])) ->
      ( seq (OLTheoryCut (pred n)) (u| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs PARTENSOR Right A B ) .
    intros;simpl;solveLL'.
    tensor' (@nil oo) (@nil oo);rewrite Permutation_app_comm;simpl;auto.
  Qed.


  Theorem FocusingRightCte : forall n Gamma C th,
      (seqN th n Gamma [] (>> makeRuleConstant C Right)) ->
      IsPositiveAtomFormulaL Gamma ->
      exists m, n = S m /\
                In ( u|t_cons C|) Gamma /\
                seqN th m Gamma []  (>> CteRulesDefs (rulesCte C) Right).
  Proof with solveF.
    intros.
    inversion H...
    apply Permutation_nil in H3.
    apply app_eq_nil in H3;CleanContext.
    inversion H7...
    eexists;eauto.
  Qed.

  Theorem FocusingLeftCte : forall n Gamma C th,
      (seqN th n Gamma [] (>> makeRuleConstant C Left)) ->
      IsPositiveAtomFormulaL Gamma ->
      exists m,
        n = S m /\
        ( In (d| t_cons C |) Gamma /\
          seqN th m Gamma []  (>> CteRulesDefs (rulesCte C) Left)).
  Proof with solveF.
    intros.
    InvTriAll.
    apply Permutation_nil in H3. inversion H3.
    apply Permutation_nil in H3...
    eexists.
    split...
  Qed.
  
  Theorem FocusingRightRule : forall n Gamma  C A B th,
      (seqN th n Gamma [] (>> makeRuleBin C Right A B)) ->
      IsPositiveAtomFormulaL Gamma ->
      exists m , n = S m /\
                 (In (u| t_bin C A B|) Gamma) /\
                 seqN th m Gamma []  (>> RulesDefs (rulesBin C) Right A B).
  Proof with solveF.
    intros.
    InvTriAll.
    apply Permutation_nil in H3. inversion H3.
    eexists;eauto.
    split...
    split...
    apply Permutation_nil in H3...
  Qed.

  Theorem FocusingLeftRule : forall n Gamma C A B th,
      (seqN th n Gamma [] (>> makeRuleBin C Left A B)) ->
      IsPositiveAtomFormulaL Gamma ->
      exists m , n = S m /\
                 ( In (d|t_bin C A B|) Gamma /\
                   seqN th m Gamma []  (>> RulesDefs (rulesBin C) Left A B)) .
  
  Proof with solveF.
    intros.
    InvTriAll.
    apply Permutation_nil in H3. inversion H3.
    apply Permutation_nil in H3...
    eexists;eauto.
  Qed.

  Theorem AppPARTENSORRight :
    forall n  Gamma A B th,
      (seqN th n Gamma [] (>> RulesDefs PARTENSOR Right A B)) ->
      exists m , n = S(S(S m))  /\
                 (seqN th m (u| A |::Gamma) [] (> []) ) /\
                 (seqN th m (u| B |::Gamma ) [] (> []) ) .
  Proof with solveF.
    intros.
    simpl in H.
    InvTriAll.
    eexists.
    split;eauto.
    apply Permutation_nil in H2.
    apply app_eq_nil in H2...
    split;eauto.
    LLExact H7.
    LLExact H8.
  Qed.

  Theorem AppPARTENSORLeft:
    forall n  Gamma  A B th,
      (seqN th n Gamma [] (>> RulesDefs PARTENSOR Left A B)) ->
      exists m , n = S(S(S (S m)))  /\
                 (seqN th m (d| A | ::  d| B |:: Gamma ) [] (> []) ) .
  Proof with solveF.
    intros.
    simpl in H.
    InvTriAll.
    eexists.
    split...
    LLExact H4.
  Qed.

  Theorem AppTENSORPARRight :
    forall n  Gamma  A B th,
      (seqN th n Gamma [] (>> RulesDefs TENSORPAR Right A B)) ->
      exists m , n = S(S(S(S m)))  /\
                 ( (seqN th m (u| A | :: u| B | :: Gamma) [] (> []) ) ).
  Proof with solveF.
    intros.
    simpl in H.
    InvTriAll.
    eexists.
    split;eauto.
    LLExact H4.
  Qed.

  Theorem AppTENSORPARLeft :
    forall n  Gamma  A B th,
      (seqN th n Gamma [] (>> RulesDefs TENSORPAR Left A B)) ->
      exists m , n = S(S(S m))  /\
                 ( (seqN th m (d| A|::Gamma) [] (> []) ) /\
                   (seqN th m (d| B|::Gamma) [] (> []) )) .
  Proof with solveF.
    intros.
    simpl in H.
    InvTriAll.
    apply Permutation_nil in H2.
    apply app_eq_nil in H2...
    eexists.
    split;eauto.
    split...
    LLExact H7.
    LLExact H8.
  Qed.

  Theorem AppTENSORPAREXCHRight :
    forall n  Gamma  A B th,
      (seqN th n Gamma [] (>> RulesDefs TENSORPAREXCH Right A B)) ->
      exists m , n = S(S(S(S m)))  /\
                 seqN th m (d| A |:: u| B | :: Gamma) [] (> []).
  Proof with solveF.
    intros.
    simpl in H.
    InvTriAll.
    eexists.
    split;eauto.
    LLExact H4.
  Qed.

  Theorem AppTENSORPAREXCHLeft :
    forall n  Gamma  A B th,
      (seqN th n Gamma [] (>> RulesDefs TENSORPAREXCH Left A B)) ->
      exists m  , n = S(S(S m))  /\
                  ( seqN th m (u| A |::Gamma) [] (> [])) /\
                  ( seqN th m (d| B | :: Gamma) [] (> [])).
  Proof with solveF.
    intros.
    simpl in H.
    InvTriAll.
    apply Permutation_nil in H2.
    apply app_eq_nil in H2...
    eexists.
    split;eauto.
    split.
    LLExact H7.
    LLExact H8.
  Qed.
End Bipoles.

Ltac CutTacPOSNEG :=
  CutTac;
  try
    match goal with
    | [H : isOLConstant (t_bin _ _ _) |- _] => inversion H  (* inconsistent hypothesis *)
    | [ |- OLTheoryCut _ _] =>  solve[constructor;constructor;auto]
    | [ |- isFormula _ ] => solve[SolveIsFormulas]
    | [ H: ~ IsPositiveAtom ?F, H': In ?F (atom _ :: _) |-_] => 
        solve [apply PositiveAtomIn in H';auto;contradiction]
    end.

Section OLCutElimination.
  Context `{OLR: OORules}.
  Hint Constructors CutRulePOSNEGN : core.
  Hint Unfold makeRuleConstant makeRuleBin (*makeLRuleQ makeRRuleQ*) : core.
  Hint Constructors  OLTheoryCut OLTheory  : core.
  Hint Unfold RINIT RCUTPOSNEG : core.	
  Hint Unfold down' up' : core .

  Theorem TheoryCutIsFormula n F:
    OLTheoryCut n F -> isFormula F.
  Proof with CutTacPOSNEG.
    intros.
    inversion H...
    inversion H0; auto using CtesIsFormula, RulesIsFormula,MRulesIsFormula...
    inversion H0...
  Qed.

  (** Inductive hypothesis during the cut-elimination procedure *)
  Definition CUTDefinition n' h :=
    forall m : nat,
      m <= h ->
      forall h2 h1 : nat,
        m = h1 + h2 ->
        forall n : nat,
          n' <= n ->
          forall FCut : uexp,
            isOLFormula FCut ->
            lengthUexp FCut n' ->
            forall Gamma : list oo,
              seqN OLTheory h1 (d| FCut | :: Gamma) [] (> []) ->
              seqN OLTheory h2 (u| FCut | :: Gamma) [] (> []) ->
              IsPositiveAtomFormulaL Gamma -> seq (OLTheoryCut (pred n)) Gamma [] (> []).

  
  (** Assuming that both premises of the cut use a right rule (and
  then, the cut rule is not principal in the left premise *)
  Theorem LeftPremiseRightRuleCases n n' h h1 h2 Gamma A B FCut C:
    (seqN OLTheory h1 (d| FCut |:: Gamma) []
          (>> makeRuleBin C Right A B)) ->
    (seqN OLTheory (S h1) (d| FCut | ::Gamma) [] (> [])) ->
    ( seqN OLTheory (S (S h2)) (u| FCut |::Gamma) [] (> [])) ->
    IsPositiveAtomFormulaL Gamma ->
    S h = S h1 + S (S h2) ->
    n' <= n ->
    lengthUexp (FCut) n' ->
    isOLFormula (FCut) ->
    isOLFormula (t_bin C A B) ->
    CUTDefinition n' h ->
    seq (OLTheoryCut (pred n)) Gamma [] (> []).
  Proof with CutTacPOSNEG.
    intros Hseq1 Hseq1' Hseq2 IsGamma Hh Hn Hluexp HisC  HisAB IH.
    apply FocusingRightRule in Hseq1...
    CleanContext.
    inversion H0...
    remember (rulesBin C).
    destruct r.
    + apply AppPARTENSORRight in H1.
      CleanContext.
      inversion HisAB...
      decide3' (makeRuleBin C Right A B)...
      tensor' (@nil oo) (@nil oo)...
      rewrite <- Heqr...
      tensor' (@nil oo) (@nil oo).
      permswap H2.
      rewrite Permutation_app_comm...
      eapply IH with (h1:= x0) (h2:= S ( S h2)) (m := x0 + S ( S h2)) (FCut:=FCut)...
      rewrite perm_swap.
      apply weakeningN...

      permswap  H3.
      rewrite Permutation_app_comm...
      eapply IH with (h1:= x0) (h2:= S ( S h2)) (m := x0 + S ( S h2)) (FCut:=FCut)...
      rewrite perm_swap.
      apply weakeningN...
    + apply AppTENSORPARRight in H1.
      CleanContext.
      inversion H0...
      inversion HisAB...
      decide3' (makeRuleBin C Right A B)...
      tensor' (@nil oo) (@nil oo)...
      rewrite <- Heqr...
      solveLL'.
      LLPermH H2  (d| FCut | :: u| A | :: u| B | :: Gamma).
      LLPerm (u| A |  :: u| B |:: Gamma ) .
      eapply IH with (h1:= x0) (h2:= S ( S h2)) (m := x0 + S ( S h2)) (FCut:=FCut)...
      rewrite perm_swap.
      apply weakeningN.
      rewrite perm_swap.
      apply weakeningN...
    + apply AppTENSORPAREXCHRight in H1.
      inversion H0...
      CleanContext.
      inversion HisAB...
      decide3' (makeRuleBin C Right A B)...
      tensor' (@nil oo) (@nil oo).
      rewrite <- Heqr... solveLL'.
      rewrite Permutation_app_comm...
      apply IH with (m:=x0 + S (S h2)) (h2 := S (S h2))  (h1:= x0) (FCut:=FCut)...
      LLExact H3.
      rewrite perm_swap...
      eapply weakeningN...
      LLPerm (d| A | :: u| FCut | :: Gamma ).
      eapply weakeningN...
  Qed.

  (** Assuming that the cut formula in the right premise of the cut
  was principal, we analyze the cases of the left premise.
  Here we assume that the cut-formula is a constant
   *)
  Theorem RCtePrincipalLCases n n' h h1 h2 Gamma  C :
    (seqN OLTheory (S ( S h1)) (d| t_cons C |:: Gamma) [] (> [])) ->
    (seqN OLTheory h2 (u| t_cons C |:: Gamma) [] (>> CteRulesDefs (rulesCte C) Right)) ->
    (seqN OLTheory (S (S h2)) (u| t_cons C |::Gamma) [] (> [])) ->
    IsPositiveAtomFormulaL Gamma ->
    S h = S (S h1) + S (S h2) ->
    n' <= n ->
    lengthUexp (t_cons C) n' ->
    isOLFormula (t_cons C) ->
    CUTDefinition n' h ->
    seq (OLTheoryCut (pred n)) Gamma [] (> []).
  Proof with CutTacPOSNEG.
    intros Hseq1 Hseq2 Hseq2' IsGamma Hh Hn Hluexp HisC IH .
    (** By case analysis on the continuation of HSeq1 *)
    inversion Hseq1...
    inversion H1...
    inversion H0...
    { (* rule *)
      inversion H...
      + (* right constant --- Never principal --- *)
        apply FocusingRightCte in H2...
        CleanContext.
        inversion H2...
        remember (rulesCte C0).
        destruct c;simpl in H4...
        inversion H4...
        decide3' (makeRuleConstant C0 Right)...
        tensor' (@nil oo) (@nil oo).
        rewrite <- Heqc... solveLL'.
      + (* left constant *)
        apply FocusingLeftCte in H2...
        CleanContext.
        inversion H2;CleanContext.
        inversion H5...
        remember (rulesCte C0).
        destruct c;simpl in *...
        inversion Hseq2...
        inversion H4...

        remember (rulesCte C0).
        destruct c;simpl in *...

        decide3' (makeRuleConstant C0 Left) .
        tensor' (@nil oo) (@nil oo).
        rewrite <- Heqc... solveLL'.
        inversion H4...
      + (* Right Rule --- Never principal --- *)
        apply FocusingRightRule in H2...
        CleanContext.
        remember (rulesBin C0).
        destruct r...
        ++ apply AppPARTENSORRight in H4...
           CleanContext.
           inversion H2...
           inversion H3...
           decide3' (makeRuleBin C0 Right F0 G)...
           tensor' (@nil oo) (@nil oo).
           rewrite <- Heqr...
           permswap  H5.
           permswap  H6.
           tensor' (@nil oo) (@nil oo);rewrite Permutation_app_comm...
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           rewrite perm_swap; apply weakeningN...
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           rewrite perm_swap; apply weakeningN...
        ++ apply AppTENSORPARRight in H4...
           CleanContext.
           inversion H3...
           inversion H2...
           decide3' (makeRuleBin C0 Right F0 G)...
           tensor' (@nil oo) (@nil oo).
           rewrite <- Heqr...
           solveLL'.
           LLPermH H5  (d| t_cons C | :: u| F0 | :: u| G | :: Gamma) .
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           LLExact H5.
           rewrite Permutation_app_comm...
           rewrite perm_swap; apply weakeningN...
           rewrite Permutation_app_comm...
           rewrite perm_swap; apply weakeningN...
        ++ apply AppTENSORPAREXCHRight in H4...
           inversion H2...
           CleanContext.
           inversion H3...
           decide3' (makeRuleBin C0 Right F0 G)...
           tensor' (@nil oo)(@nil oo).
           rewrite <- Heqr...
           solveLL'...
           rewrite Permutation_app_comm...
           LLPermH H6  (d| t_cons C | :: d| F0 | :: u| G | :: Gamma) .
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           LLExact H6.
           rewrite perm_swap; apply weakeningN...
           rewrite Permutation_app_comm...
           rewrite perm_swap; apply weakeningN...
      + (* left Rule Never Principal*)
        apply FocusingLeftRule in H2...
        CleanContext.
        inversion  H2;CleanContext...
        (* Non Principal case *)
        remember (rulesBin C0).
        destruct r...
        ++ inversion H2...
           apply AppPARTENSORLeft in H4.
           CleanContext.
           decide3' (makeRuleBin C0 Left F0 G)...
           tensor' (@nil oo) (@nil oo)...
           rewrite <- Heqr... solveLL'.
           LLPerm (d| F0 | :: d| G | :: Gamma).
           LLPermH H6 (d| t_cons C| :: d| F0 | :: d| G | :: Gamma) .
           inversion H3...
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           rewrite perm_swap; apply weakeningN...
           rewrite perm_swap; apply weakeningN...
        ++ apply AppTENSORPARLeft in H4.
           CleanContext.
           inversion H3...
           decide3' (makeRuleBin C0 Left F0 G)...
           tensor' (@nil oo)(@nil oo).
           permswap  H6.
           permswap  H7.
           rewrite <- Heqr...
           tensor' (@nil oo)(@nil oo);rewrite Permutation_app_comm...
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           rewrite perm_swap; apply weakeningN...
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           rewrite perm_swap; apply weakeningN...
        ++ apply AppTENSORPAREXCHLeft in H4.
           CleanContext.
           inversion H3...
           decide3' (makeRuleBin C0 Left F0 G)...
           tensor' (@nil oo) (@nil oo).
           rewrite <- Heqr...
           tensor' (@nil oo) (@nil oo);rewrite Permutation_app_comm...
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           LLExact H6.
           rewrite perm_swap; apply weakeningN...
           permswap  H7.
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           rewrite perm_swap; apply weakeningN...
    }
    { (* init *)
      apply Init_inversion1 in H2...
      inversion H3...
      inversion H2...
      subst.
      apply contractionN in Hseq2'...
      apply seqNtoSeq in Hseq2'...
      apply WeakTheory with (theory' := (OLTheoryCut (pred n)) ) in Hseq2' ;auto using TheoryEmb1;CutTacPOSNEG.
      decide3' (RINIT OO).
      tensor' (@nil oo) (@nil oo).
    }
  Qed.

  Hint Constructors isFormula : core.

  (** Principal cases are solved with cut at the meta-level (i.e.,
  with cuts in linear logic. Note that use of cut-coherence for that
  *)
  Theorem CutObjectLL: forall T A B C Gamma n n', 
      (seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs T Left A B)) ->
      (seq (OLTheoryCut (pred n))  Gamma [] (>> RulesDefs T Right A B)) ->
      isOLFormula (t_bin C A B) ->
      lengthUexp (t_bin C A B) n' ->
      n' <= n ->
      IsPositiveAtomFormulaL Gamma ->
      seq (OLTheoryCut (pred n)) Gamma [] (> []).
  Proof with CutTacPOSNEG.
    intros.
    change [] with ((@nil oo) ++ []).
    apply @GeneralCut' with (dualC:= RulesDefs T Right A B) (C := ( RulesDefs T Right A B)^);CutTacPOSNEG;SolveIsFormulas;eauto using RulesPerpIsFormula, IsPositiveIsFormula,TheoryCutIsFormula, RulesIsFormula.
    rewrite <- ng_involutive...
    change [] with ((@nil oo) ++ []).
    apply @GeneralCut' with (dualC:=  RulesDefs T Left A B ) (C:= ( RulesDefs T Left A B) ^);CutTacPOSNEG;eauto using RulesPerpIsFormula, IsPositiveIsFormula,RulesIsFormula,TheoryCutIsFormula; SolveIsFormulas.
    rewrite <- ng_involutive...
    inversion H1...
    inversion H2...
    generalize (CutCoherenceRules T H11 H12 H7 H9);intro.
    assert (Nat.max n1 n2 <= (pred n)) by lia.
    apply CuteRuleNBound' with (m:= pred n) in H5...
    apply WeakTheory with (theory' := OLTheoryCut (pred n)) in H5;auto using TheoryEmb2...
    LLPerm (Gamma ++ [] ).
    apply weakeningGen...
  Qed.

  
  (** Assuming that the cut formula in the right premise of the cut
  was principal, we analyze the cases of the left premise.
  Here we assume that the cut-formula is a connective 
   *)

  Theorem RBinPrincipalLCases n n' h h1 h2 Gamma C A B:
    (seqN OLTheory h1 (d|t_bin C A B|::Gamma) [] (> [])) ->
    (seqN OLTheory h2 (u|t_bin C A B|::Gamma) [] (>> RulesDefs (rulesBin C) Right A B)) ->
    (seqN OLTheory (S (S h2)) (u| t_bin C A B |::Gamma) [] (> [])) ->
    IsPositiveAtomFormulaL Gamma ->
    S h = h1 + S (S h2) ->
    n' <= n ->
    lengthUexp (t_bin C A B) n' ->
    isOLFormula (t_bin C A B) ->
    CUTDefinition n' h ->
    seq (OLTheoryCut (pred n)) Gamma [] (> []).
  Proof with CutTacPOSNEG.
    intros Hseq1 Hseq2 Hseq2' IsGamma Hh Hn Hluexp HisC IH.
    (** By case analysis on the continuation of HSeq1 *)
    inversion Hseq1...
    inversion H0...
    inversion H...
    { (* rule *)
      inversion H2...
      + (* right cte never principal *)
        apply FocusingRightCte in H1...
        CleanContext.
        inversion H1...
        remember (rulesCte C0).
        destruct c;simpl in H4...
        inversion H4...
        decide3' (makeRuleConstant C0 Right)...
        tensor' (@nil oo) (@nil oo).
        rewrite <- Heqc... solveLL'.
      + (* left cte *)
        apply FocusingLeftCte in H1...
        CleanContext.
        inversion H1...
        destruct H1;CleanContext.
        inversion H1...
        remember (rulesCte C0).
        destruct c;simpl in *...
        decide3' (makeRuleConstant C0 Left)...
        tensor'  (@nil oo) (@nil oo).
        rewrite <- Heqc... solveLL'.
        inversion H4...
      + (* right rule never principal *)
        eapply LeftPremiseRightRuleCases;eauto.
      + (* left rule *)
        apply FocusingLeftRule in H1 as H1'...
        CleanContext.
        inversion H4; subst;CleanContext.
        ++ (* principal case *)
          inversion H0...
          remember (rulesBin C0).
          destruct r.
          +++ apply AppPARTENSORLeft in H5.
              CleanContext.
              inversion H3...

              LLPermH H5   (d|t_bin C0 F0 G|:: d| F0 | :: d| G | :: Gamma).
              assert(Cut1L:  seq (OLTheoryCut (pred n)) ( d| F0 | :: d| G | :: Gamma) [] (> [])) .
              apply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C0 F0 G)...
              rewrite perm_swap;apply weakeningN...
              rewrite perm_swap;apply weakeningN...
              assert(Cut2: seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs PARTENSOR Left F0 G )) by (apply PARTensorInv;auto).

              apply AppPARTENSORRight in Hseq2.
              CleanContext.
              permswap  H6.
              permswap  H8.
              assert(Cut1R:  seq (OLTheoryCut (pred n)) ( u| F0 | :: Gamma) [] (> [])) .
              apply IH with (h2 := x) (h1:= (S (S (S (S (S (S x0))))))) (m := (S (S (S (S (S (S x0))))))+x) (FCut:= t_bin C0 F0 G)...
              rewrite perm_swap;apply weakeningN...
              assert(Cut1R':  seq (OLTheoryCut (pred n)) ( u| G | :: Gamma) [] (> [])) .
              apply IH with (h2 := x) (h1:= (S (S (S (S (S (S x0))))))) (m := (S (S (S (S (S (S x0))))))+x) (FCut:= t_bin C0 F0 G)...
              rewrite perm_swap;apply weakeningN...

              assert(Cut2L: seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs PARTENSOR Left F0 G )) by (apply PARTensorInv;auto).
              assert(Cut2R: seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs PARTENSOR Right F0 G )) by (apply PARTensorInv';auto).
              
              eapply CutObjectLL;eauto.
              
          +++ apply AppTENSORPARLeft in H5.
              CleanContext.
              inversion H3...
              
              permswap  H5.
              permswap  H6.
              assert(Cut1:  seq (OLTheoryCut (pred n))  (d| F0 | :: Gamma) [] (> [])).
              apply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C0 F0 G)...
              rewrite perm_swap; apply weakeningN...
              assert(Cut1':  seq (OLTheoryCut (pred n))  (d| G | :: Gamma) [] (> [])).
              apply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C0 F0 G)...
              rewrite perm_swap; apply weakeningN...
              
              
              assert(Cut2: seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAR Left F0 G )) by (apply TENSORPARInv;auto).

              apply AppTENSORPARRight in Hseq2.
              CleanContext.
              LLPermH H7 (u| t_bin C0 F0 G | :: u| F0 | :: u| G | :: Gamma).
              assert(Cut1R:  seq (OLTheoryCut (pred n))  (u| F0 | :: u| G | :: Gamma) [] (> [])).
              apply IH with (h2 := x) (h1:=(S (S (S (S (S x0)))))) (m := (S (S (S (S (S x0)))))+x) (FCut:= t_bin C0 F0 G)...
              rewrite perm_swap; apply weakeningN...
              rewrite perm_swap; apply weakeningN...
              assert(Cut2R: seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAR Right F0 G )) by (apply TENSORPARInv';auto).
              eapply CutObjectLL;eauto.
              
          +++ apply AppTENSORPAREXCHLeft in H5.
              CleanContext.
              inversion H3...
              permswap  H5.
              permswap  H6.
              
              assert(Cut1:  seq (OLTheoryCut (pred n))  (u| F0 |::Gamma) [] (> [])).
              apply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C0 F0 G)...
              rewrite perm_swap; apply weakeningN...
              assert(Cut1':  seq (OLTheoryCut (pred n))  (d| G |::Gamma) [] (> [])).
              apply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C0 F0 G)...
              rewrite perm_swap; apply weakeningN...
              
              assert(Cut2: seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAREXCH Left F0 G )) by (apply TENSORPAREXCHInv;auto).

              apply AppTENSORPAREXCHRight in Hseq2.
              CleanContext.
              LLPermH H7 (u| t_bin C0 F0 G | :: d| F0 | :: u| G | :: Gamma).
              
              assert(Cut1R:  seq (OLTheoryCut (pred n))  (d| F0 |:: u|G| :: Gamma) [] (> [])).
              apply IH with (h2 := x) (h1:=(S (S (S (S (S x0)))))) (m := (S (S (S (S (S x0))))) + x) (FCut:= t_bin C0 F0 G)...
              rewrite perm_swap; apply weakeningN...
              rewrite perm_swap; apply weakeningN...
              assert(Cut2R: seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAREXCH Right F0 G )) by (apply TENSORPAREXCHInv';auto).
              eapply CutObjectLL;eauto.
              
        ++ (* Non Principal cases *)
          inversion H3...
          remember (rulesBin C0).
          destruct r.
          +++ apply AppPARTENSORLeft in H5.
              CleanContext.
              decide3' (makeRuleBin C0 Left F0 G  ) ...
              tensor' (@nil oo) (@nil oo)...
              rewrite <- Heqr... solveLL'.
              LLPerm  (d| F0 | :: d| G | :: Gamma).
              LLPermH H6   (d|t_bin C A B|:: d| F0 | :: d| G | :: Gamma).
              apply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C A B)...
              rewrite perm_swap; apply weakeningN...
              rewrite perm_swap; apply weakeningN...
          +++ apply AppTENSORPARLeft in H5.
              CleanContext.
              decide3' (makeRuleBin C0 Left F0 G  ) .
              tensor' (@nil oo) (@nil oo).
              permswap  H6.
              permswap  H7.
              rewrite <- Heqr...
              tensor' (@nil oo) (@nil oo);rewrite Permutation_app_comm...
              
              eapply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C A B)...
              rewrite perm_swap; apply weakeningN...
              eapply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C A B)...
              rewrite perm_swap; apply weakeningN...
          +++ apply AppTENSORPAREXCHLeft in H5.
              CleanContext.
              decide3' (makeRuleBin C0 Left F0 G  ) .
              permswap  H7.
              tensor' (@nil oo) (@nil oo).
              rewrite <- Heqr...
              permswap  H6.
              tensor' (@nil oo) (@nil oo);rewrite Permutation_app_comm...

              eapply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C A B)...
              rewrite perm_swap; apply weakeningN...
              eapply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C A B)...
              rewrite perm_swap; apply weakeningN...
    } 
    { (* init *)
      apply Init_inversion1 in H1...
      inversion H3...
      inversion H1...
      subst.
      
      apply contractionN in Hseq2'...
      apply seqNtoSeq in Hseq2'...
      apply WeakTheory with (theory' := (OLTheoryCut (pred n)) ) in Hseq2' ;auto using TheoryEmb1;CutTacPOSNEG.
      
      decide3' (RINIT OO).
      tensor' (@nil oo) (@nil oo).
    }
    Qed.

  (* LeftRule applied on the right premise of the cut. This case in never principal *)
  Theorem LeftRuleOnRightPremise n n' h h1 h2 Gamma FCut C A B :
    (seqN OLTheory h1 (d|FCut| :: Gamma) [] (> [])) ->
    (seqN OLTheory h2 (u| FCut |::Gamma) [] (>> makeRuleBin C Left A B)) ->
    (seqN OLTheory (S h2) (u| FCut |::Gamma) [] (> [])) ->
    IsPositiveAtomFormulaL Gamma ->
    S h = h1 + S h2 ->
    n' <= n ->
    lengthUexp FCut n' ->
    isOLFormula FCut ->
    isOLFormula (t_bin C A B) ->
    CUTDefinition n' h ->
    seq (OLTheoryCut (pred n)) Gamma [] (> []).
  Proof with CutTacPOSNEG.
    intros Hseq1 Hseq2 Hseq2' IsGamma Hh Hn Hluexp HisFcut  HisAB IH.
    apply FocusingLeftRule in Hseq2...
    CleanContext.
    inversion H0...
    inversion HisAB...
    remember (rulesBin C).
    destruct r...
    + apply AppPARTENSORLeft in H1...
      CleanContext.
      apply weakeningGenN with (CC':= [atom (down'  A); atom (down' B)]) in Hseq1;simpl in Hseq1.
      decide3' ( makeRuleBin C Left A B)...
      
      tensor' (@nil oo) (@nil oo).
      rewrite <-  Heqr... solveLL'.
      LLPermH Hseq1 (d| FCut | :: atom (down' A) :: atom (down' B)  :: Gamma) .
      LLPerm (atom (down' A) :: atom (down' B) :: Gamma)...
      eapply IH with (h1 := h1) (h2:=x0) (m := h1+ x0) (FCut := FCut)...
      LLPerm (d| A | :: d| B | :: u| FCut | :: Gamma)...
      
    + apply AppTENSORPARLeft in H1...
      CleanContext.
      inversion H0...
      decide3' ( makeRuleBin C Left A B)...

      tensor' (@nil oo) (@nil oo) .
      rewrite <-  Heqr... solveLL'.
      tensor' (@nil oo) (@nil oo) .
      
      apply weakeningGenN with (CC':= [atom (down'  A)]) in Hseq1.
      rewrite Permutation_app_comm...
      eapply IH with (h1 := h1) (h2:=x0) (m := h1+ x0) (FCut := FCut)...
      LLPermH Hseq1 (d| FCut | :: atom(down' A) :: Gamma) ...
      LLExact H2.
      
      apply weakeningGenN with (CC':= [atom (down'  B)]) in Hseq1.
      LLPermH Hseq1 (d| FCut | :: Gamma ++ [atom (down' B)]).
      eapply IH with (h1 := h1) (h2:=x0) (m := h1+ x0) (FCut := FCut)...
      LLExact H3.

    + apply AppTENSORPAREXCHLeft in H1...
      CleanContext.
      inversion H0...
      decide3' ( makeRuleBin C Left A B)...
      
      tensor' (@nil oo) (@nil oo).
      rewrite <-  Heqr... 
      tensor' (@nil oo)  (@nil oo).
      permswap  H3.

      eapply IH with (h1 := h1) (h2:=x0) (m := h1+ x0) (FCut := FCut)...
      LLPerm (u| A | :: d| FCut | :: Gamma).
      apply weakeningN...
      LLExact H2.
      
      permswap  H3.
      eapply IH with (h1 := h1) (h2:=x0) (m := h1+ x0) (FCut := FCut)...
      LLPerm (d| B | :: d| FCut | :: Gamma ).
      apply weakeningN...
      LLExact H3.
  Qed.

  (** The main auxiliarly result eliminating the top-most cut *)
  Theorem CutElimStep:
    forall h1 h2 n n' Gamma Fcut,
      (seqN OLTheory h1 (d|Fcut|:: Gamma) [] (> [])) ->
      (seqN OLTheory h2 (u|Fcut|::Gamma) [] (> [])) ->
      isOLFormula Fcut ->
      IsPositiveAtomFormulaL Gamma ->
      lengthUexp Fcut n' ->
      n' <= n ->
      (seq (OLTheoryCut (pred n)) Gamma []  (> [])).
  Proof with CutTacPOSNEG.
    intros h1 h2 n n' Gamma FCut Hseq1 Hseq2 HIsFcut  HIsGamma HLeng Hnn'.
    remember (plus h1 h2) as h.
    generalize dependent Gamma.
    generalize dependent FCut.
    generalize dependent n.
    generalize dependent h1.
    generalize dependent h2.
    induction h using strongind;intros.

    assert (h1 = 0) by lia...
    inversion Hseq1.
    assert(IH : CUTDefinition n' h) by auto. clear H.

    (* Let's analyze Hseq2 -- the right premise in the cut rule *)
    inversion Hseq2...
    inversion H0...
    inversion H...
    { (* from the theory *)
      inversion H2...
      
      + (* Right Constant (in the right premise of the cut *)
        apply FocusingRightCte in H1...
        CleanContext.
        (* We look at the sequent Hseq1 *)
        inversion Hseq1...
        inversion H5...
        inversion H0...
        { (* from the theory -- Left premise -- *)
          inversion H7...
          + (* right constant in the left premise --- never principal ---*)
            apply FocusingRightCte in H6...
            CleanContext.
            inversion H6...
            remember (rulesCte C0).
            destruct c;simpl in H9.
            inversion H9...
            decide3' (makeRuleConstant C0 Right ) .
            tensor' (@nil oo) (@nil oo).
            rewrite <- Heqc...
            solveLL'.
          + (* left constant in the left premise *)
            apply FocusingLeftCte in H6...
            CleanContext.
            destruct H6;CleanContext.
            inversion H5...
            destruct H1;CleanContext.
            inversion H1...
            (* Principal case *)
            eapply RCtePrincipalLCases with (h1:= x0) (h2:= x);eauto.
            
            (* Non principal case *) 
            remember (rulesCte C).
            destruct c...
            simpl in H4. inversion H4...
            decide3' (makeRuleConstant C Right ).
            tensor' (@nil oo)(@nil oo)...
            rewrite <- Heqc... solveLL'.

            remember (rulesCte C0).
            destruct c...
            decide3' (makeRuleConstant C0 Left ).
            tensor' (@nil oo)(@nil oo).
            rewrite <- Heqc... solveLL'.
            simpl in H9. inversion H9...
          + (* right rule in the left premise *)
            eapply LeftPremiseRightRuleCases with (h1:= n0) (h2:= x);eauto.
          + (* left rule in the left premise *)
            apply FocusingLeftRule in H6...
            CleanContext.
            inversion H1;CleanContext...
            subst.
            inversion H6;CleanContext...
            (* Principal cases *)
            eapply RCtePrincipalLCases with (h1:= x0) (h2:= x);eauto.
            (* non principal cases *)
            remember (rulesCte C).
            destruct c...
            simpl in H4. inversion H4...
            decide3' (makeRuleConstant C Right ).
            tensor' (@nil oo)(@nil oo).
            rewrite <-Heqc... solveLL'.
        }
        { (* Init from the left premise *)
          apply Init_inversion1  in H6...
          inversion H8...
          inversion H6...
          subst.
          apply contractionN in Hseq2...
          apply seqNtoSeq in Hseq2...
          apply WeakTheory with (theory' := (OLTheoryCut (pred n)) ) in Hseq2 ;auto using TheoryEmb1;CutTacPOSNEG.
          decide3' (RINIT OO).
          tensor' (@nil oo) (@nil oo). 
        }
      + (* Left Constant in the right premise -- never principal --*)
        apply FocusingLeftCte in H1...
        CleanContext.
        inversion H1...
        remember (rulesCte C).
        destruct c...
        decide3' (makeRuleConstant C Left ).
        tensor' (@nil oo) (@nil oo).
        rewrite <- Heqc...
        solveLL'.
        simpl in H4... inversion H4...
      + (* right rule in the right premise *)
        apply FocusingRightRule in H1...
        CleanContext.
        inversion H1...
        subst.
        eapply RBinPrincipalLCases with (h1:=h1) (h2:=x);eauto.
        (* non principal cases *)
        remember (rulesBin C).
        destruct r.
        ++ apply AppPARTENSORRight in H4;CleanContext.
           inversion H3...
           permswap  H5.
           permswap  H6.
           decide3' (makeRuleBin C Right F0 G)...
           tensor' (@nil oo) (@nil oo)...
           rewrite <- Heqr...
           tensor' (@nil oo) (@nil oo);rewrite Permutation_app_comm...
            
           apply IH with (m:=h1 + x0) (h2:=x0)  (h1:= h1) (FCut:=FCut)...
           rewrite perm_swap; apply weakeningN...
           apply IH with (m:=h1 + x0) (h2:=x0)  (h1:= h1) (FCut:=FCut)...
           rewrite perm_swap; apply weakeningN...
        ++ apply AppTENSORPARRight in H4;CleanContext.
           inversion H3...
           LLPermH H5 (u| FCut | :: u| F0 | :: u| G | :: Gamma).
           decide3' (makeRuleBin C Right F0 G)...
           tensor' (@nil oo) (@nil oo)...
           rewrite <- Heqr... solveLL'.
           rewrite Permutation_app_comm...
           rewrite Permutation_app_comm...
           apply IH with (m:=h1 + x0) (h2:=x0)  (h1:= h1) (FCut:=FCut)...
           rewrite perm_swap; apply weakeningN...
           rewrite perm_swap; apply weakeningN...
           LLExact H5.
        ++ apply AppTENSORPAREXCHRight in H4;CleanContext.
           inversion H3...
           LLPermH H5 (u| FCut | :: d| F0 | :: u| G | :: Gamma).
           decide3' (makeRuleBin C Right F0 G)...
           tensor' (@nil oo) (@nil oo)...
           rewrite <- Heqr... solveLL'.
           rewrite Permutation_app_comm...
           rewrite Permutation_app_comm...
           apply IH with (m:=h1 + x0) (h2:=x0)  (h1:= h1) (FCut:=FCut)...
           rewrite perm_swap; apply weakeningN...
           rewrite perm_swap; apply weakeningN...
           LLExact H5.
      + (* left rule in the left premise -- never principal *)
        eapply LeftRuleOnRightPremise;eauto.
    }
    { (* initial rule *)
      apply Init_inversion1 in H1...
      inversion H1...
      inversion H3...
      subst.
      apply contractionN in Hseq1...

      apply seqNtoSeq in Hseq1...
      apply WeakTheory with (theory' := (OLTheoryCut (pred n)) ) in Hseq1 ;auto using TheoryEmb1;CutTacPOSNEG.
      decide3' (RINIT OO).
      tensor' (@nil oo) (@nil oo).
    }
  Qed.

  (** Cut Elimination *)
  Theorem CutElimination:
    forall n h  Gamma ,
      (seqN (OLTheoryCut n) h Gamma []  (> [])) ->
      IsPositiveAtomFormulaL Gamma ->
      (seq  OLTheory Gamma []  (> [])).
  Proof with CutTacPOSNEG.
    induction n;induction h using strongind ; intros; try solve[inversion H].

    apply WeakTheoryN with (theory' := OLTheory) in H0.
    apply seqNtoSeq in H0...
    apply OOTheryCut0.

    inversion H0...
    inversion H4...

    apply Forall_forall with (x := F) in H1...
    inversion H1...
    inversion H3...
    + (* A formula from the theory was used *)
      inversion H2...
      ++ (* Right constant *)
        apply FocusingRightCte in H5...
         CleanContext.
         apply seqNtoSeq in H7.
         remember (rulesCte C).
         destruct c;simpl in *...
         inversion H7...
         decide3' (makeRuleConstant C Right).
         tensor' (@nil oo) (@nil oo).
         rewrite <- Heqc... solveLL'.
      ++ (* Left constant *)
        apply FocusingLeftCte in H5...
         CleanContext.
         apply seqNtoSeq in H7.
         remember (rulesCte C).
         destruct c;simpl in *...
         decide3' (makeRuleConstant C Left).
         tensor' (@nil oo) (@nil oo).
         rewrite <- Heqc... solveLL'.
         inversion H7...
      ++ (* Right rule *)
        apply FocusingRightRule in H5...
         CleanContext.
         remember (rulesBin C).
         destruct r...
         +++ apply AppPARTENSORRight in H7.
             CleanContext.
             inversion H6...
             apply H in H7...
             apply H in H8...
             decide3' (makeRuleBin C Right F0 G).
             tensor' (@nil oo) (@nil oo).
             rewrite <- Heqr...
             tensor' (@nil oo)(@nil oo);rewrite Permutation_app_comm...
         +++ apply AppTENSORPARRight in H7.
             CleanContext.
             inversion H6...
             apply H in H7...
             decide3' (makeRuleBin C Right F0 G)...
             tensor'  (@nil oo)(@nil oo)...
             rewrite <- Heqr... solveLL'.
             LLExact' H7.
         +++ apply AppTENSORPAREXCHRight in H7.
             inversion H6...
             CleanContext.
             apply H in H7...
             decide3' (makeRuleBin C Right F0 G)...
             tensor' (@nil oo) (@nil oo)...
             rewrite <- Heqr...
             solveLL'.
             LLExact' H7.
      ++ (* Left rule *)
        apply FocusingLeftRule in H5...
         CleanContext.
         remember (rulesBin C).
         destruct r...
         +++ apply AppPARTENSORLeft in H7.
             CleanContext.
             inversion H6...
             apply H in H7...
             decide3' (makeRuleBin C Left F0 G)...
             tensor' (@nil oo) (@nil oo).
             rewrite <- Heqr...
             solveLL'.
             LLExact' H7.
         +++ apply AppTENSORPARLeft in H7.
             CleanContext.
             inversion H6...
             apply H in H7...
             apply H in H8...
             decide3' (makeRuleBin C Left F0 G)...
             tensor' (@nil oo) (@nil oo).
             rewrite <- Heqr...
             tensor' (@nil oo) (@nil oo).
             LLExact' H7.
             LLExact' H8.
         +++ apply AppTENSORPAREXCHLeft in H7.
             CleanContext.
             inversion H6...
             apply H in H7...
             apply H in H8...
             decide3' (makeRuleBin C Left F0 G)...
             tensor' (@nil oo) (@nil oo) .
             rewrite <- Heqr...
             tensor' (@nil oo) (@nil oo) .
             LLExact' H7.
             LLExact' H8.
    + (* INIT was used *)
      apply Init_inversion1 in H5...
      decide3' (RINIT OO).
      tensor' (@nil oo) (@nil oo).
    + (* Cut used *)
      inversion H2...
      InvTriAll.
      rewrite Permutation_app_comm in H16;simpl in H16.
      rewrite Permutation_app_comm in H17;simpl in H17.
      apply Permutation_nil in H11.
      apply app_eq_nil in H11...
      apply H in H16...
      apply H in H17...
      apply seqtoSeqN in H16.
      apply seqtoSeqN in H17.
      CleanContext.
      assert(HCut: seq (OLTheoryCut (pred (S n))) Gamma [] (> [])).
      eapply CutElimStep;eauto...
      simpl in HCut.
      apply seqtoSeqN in HCut.
      CleanContext.
      apply IHn in H9...
  Qed.
End OLCutElimination.
