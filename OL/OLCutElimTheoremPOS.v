(** * OL-Cut Elimination  *)

(** The procedure formalized here is tailored to the case of
object-logics (OL) where only formulas on the left side of the sequent
can be weakened and contacted. Then, we assume that all of them are
stored into the classical context of LL and the only formula in the
linear context is the formula on the right side of the (OL) sequent.

Unlike the file [OLCutelimination] here we do not consider the
quantifiers at the object-level nor unary connectives.

We shall call to this kind of logics POS-logics due to the POS rule
(left(F)^ * ?left(F)) that allows to store a left formula into the
classical context of LL.

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

Hint Constructors IsPositiveLAtomFormula : core .
Hint Unfold IsPositiveLAtomFormulaL : core.


(** This tactic solves most of the [IsPositiveLSolve] goals *)
Ltac IsPositiveLSolve :=
  match goal with
  | [ |- IsPositiveLAtomFormulaL []] => constructor
  | [ |- IsPositiveLAtomFormulaL (_ ++ _)] =>
    solve [ apply IsPositiveLAtomFormulaLApp;eauto  using Forall_Permute]
  | [ |- IsPositiveLAtomFormulaL [_] ] => constructor ;solveF
  | [ |- IsPositiveLAtomFormulaL (_ :: ?M)] =>
    first [
        do 3 (constructor;auto)
       |constructor;auto;constructor;auto
       |constructor ;solveF; fold (IsPositiveLAtomFormulaL M);  IsPositiveLSolve
                                                                  
      ]
  end.

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

  (** In systems with POS, the kind of connectives used, in order to
  be cut-coherent, is also more restricted. Here the options
  available. 
  
   - [PARTENSOR]: On the left rule, it take the atom [A * B] and
   produces one premise containing both [A] and [B] (stored in the
   classical context). In the right rule, it generates two
   premises. This is the typical encoding for conjuction-like
   connectives.

   - [WITHPLUS]: On the left rule, it generates two premises sharing
     the right formula (the unique formula stored into the linear
     context) and, on the right side, it generates only one premise
     that chooses either [A] or [B] . This is the typical encoding for
     disjunction-like connectives.

   - [TENSORPAR]: On the left side, it splits the context forcing [up
     A] to be in one premise and [? down B] in the other. Note the use
     of [!] to neatly control this behavior.

   *)
  Inductive RulesEnc := PARTENSOR | WITHPLUS | TENSORPAR .

  

  (** In POS systems, we enforce a unique Right formula on the linear context by using ! *)
  Definition RulesDefs (t:RulesEnc) (s:Side) (A B : uexp):=
    match t,s with
    | PARTENSOR, Left => (? d|A|) $ (? d|B|)
    | PARTENSOR, Right => ( !u|A|) ** ( !u|B|)
    | WITHPLUS, Left => (? d|A|) & (? d|B|)
    | WITHPLUS, Right => ( !u|A|) op ( !u|B|)
    | TENSORPAR, Left => (! u|A|) ** (? d|B|)
    | TENSORPAR, Right => (? d|A|) $ (u|B|)
    end.

  (** Cut Rule storing the left formulas into the classical context *)
  Definition RINIT (F:uexp) : oo := (u^| F|)  ** (d^| F| ) .
  Definition RCUT  (F:uexp) : oo := (? d|F|)  ** (! u|F|).

  (** The cut rule applied on object level terms of a given size  *)
  Inductive CutRuleN (n:nat) : oo -> Prop :=
  | ctn : forall (F:uexp) m , isOLFormula F ->
                              lengthUexp F m -> m <= n ->
                              CutRuleN n (RCUT F). 


  (** We assume an external definition mapping each
    connective/quantifier with a left and right rule *) 
  Class OORules :=
    {
      (* TOPZERO means TOP for the left encoding and ZERO for the
      right encoding *)
      rulesCte : constants -> ContantEnc ; 
      rulesBin : connectives -> RulesEnc;
      (*rulesQ :   quantifiers -> ruleQ*)
    }.
End OLInferenceRules.

Section CutCoherence.
  Context `{OLR: OORules}.

  Hint Constructors CutRuleN : core.
  
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
    seq (CutRuleN (max n m)) [] [] (> [ dual ( RulesDefs R Left A B );? dual ( RulesDefs R Right A B)]).
  Proof with solveF.
    intros.
    destruct R; simpl.
    + solveLL'...
      decide2'((? u^| A |) $ (? u^| B |));solveLL'.
      rewrite Permutation_app_comm...
      decide1' ((! d^| A |) ** (! d^| B |)).
      tensor' (@nil oo)(@nil oo).
      decide3' (RCUT A)...
      apply @ctn with (m:=n)...
      tensor'    [( d^| A |)]  (@nil oo)...
      decide1' (d^|A|). init'...
      decide2' (u^|A|).
      
      decide3' (RCUT B)...
      apply @ctn with (m:=m)... 
      tensor'   [ d^| B |]  (@nil oo).
      rewrite Permutation_app_comm...
      decide1' (d^|B|). init'...
      decide2' (u^|B|).
    + solveLL'...
      decide2' ((? u^| A |) & (? u^| B |));solveLL';rewrite Permutation_app_comm...

      decide1' ((! d^| A |) op (! d^| B |)).
      oplus1'.
      decide3' (RCUT A)...
      apply @ctn with (m:=n)...
      tensor'    [( d^| A |)]  (@nil oo)...
      decide1' (d^|A|). init'...
      decide2' (u^|A|).

      decide1' ((! d^| A |) op (! d^| B |)).
      oplus2'.
      decide3' (RCUT B)...
      apply @ctn with (m:=m)...
      tensor'    [( d^| B |)]  (@nil oo)...
      decide1' (d^|B|). init'...
      decide2' (u^|B|).
    + solveLL'.
      decide1' (! d^| B |); solveLL'.

      decide3' (RCUT B)...
      apply @ctn with (m:=m)...
      tensor'    [( d^| B |)]  (@nil oo)...
      decide1' (d^|B|). init'...

      decide2' ((! d^| A |) ** u^| B |).
      tensor' (@nil oo) [u| B |].

      decide3' (RCUT A)...
      apply @ctn with (m:=n)...
      tensor'    [( d^| A |)]  (@nil oo)...
      decide1' (d^|A|). init'...
      decide2' (u^|A|).
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

  Theorem RulesBangIsFormula : forall T S A B,
      isFormula (! (RulesDefs T S A B) ).
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
    apply @ctn with (m:= m0)...
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
  | oothc_cutn : forall OO, CutRuleN n OO -> OLTheoryCut n OO
  .

  Hint Constructors  OLTheoryCut OLTheory  : core.
  Hint Unfold RINIT RCUT : core.
  Hint Constructors isFormula : core.

  (** Some easy equivalences on the  above theories *)
  Lemma OOTheryCut0 : forall F, OLTheory F <-> (OLTheoryCut 0) F.
    intros.
    split;intro H ;inversion H;subst;auto.
    inversion H0.
    assert (m =  0) by omega;subst.
    generalize (LengthFormula H1 H2);intro.
    lia.
  Qed.

  Lemma TheoryEmb1 : forall n F  , OLTheory F -> (OLTheoryCut n) F.
    intros.
    inversion H;subst; solve[constructor;auto].
  Qed.

  Lemma TheoryEmb2 : forall n F  , ((CutRuleN n) F) -> (OLTheoryCut) n F.
    intros.
    inversion H;subst.
    apply oothc_cutn;auto.
  Qed.

  Hint Unfold down' up' : core .

  (** ** Invertibility lemmas *)
  (** In the following we prove that, when focusing on the bipole
  representing an OL rule, the derivation necessary has a specific
  shape *)

  (** Inversion lemmas when [RINIT] is used *)
  Lemma Init_inversion1 : forall h Gamma F1 F2 th,
      IsPositiveLAtomFormulaL Gamma ->
      seqN th h Gamma [u|F1| ] (>> RINIT F2) ->
      (F1 = F2 /\ In (d| F1|) Gamma).
  Proof with subst;solveF.
    intros.
    InvTriAll;CleanContext.
    simpl in *.
    inversion H3.
    simpl in H3.
    inversion H3...
  Qed.

  Theorem WITHPlusInv : forall A B Gamma R n,
          ( seq (OLTheoryCut (pred n)) (d| A | :: Gamma) [u| R |] (> [])) ->
          ( seq (OLTheoryCut (pred n)) (d| B | :: Gamma) [u| R |] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [u| R |] (>> RulesDefs WITHPLUS Left A B ) .
    intros;simpl;solveLL'.
    LLExact' H.
    LLExact' H0.
  Qed.

  Theorem WITHPlusInvR : forall h Gamma A B n,
      (seqN OLTheory h Gamma [] (>> RulesDefs WITHPLUS Right A B)) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> ! RulesDefs WITHPLUS Right A B).
    intros;simpl in *.
    apply seqNtoSeq in H.
    apply WeakTheory with (theory := OLTheory);auto using TheoryEmb1.
    solveLL'.
    decide1' ((! u| A |) op (! u| B |));auto.
  Qed.

  Theorem TENSORParInv : forall A B Gamma R n,
          ( seq (OLTheoryCut (pred n)) Gamma [u| A |] (> [])) ->
          ( seq (OLTheoryCut (pred n)) (d| B | :: Gamma) [u| R |] (> [])) ->
          seq (OLTheoryCut (pred n)) Gamma [u| R |] (>> RulesDefs TENSORPAR Left A B ) .
    intros;simpl;solveLL'.
    tensor' (@nil oo) [u|R|].
    rewrite Permutation_app_comm;simpl.
    LLExact' H0.
  Qed.

  Theorem TENSORParInvR : forall h Gamma A B n,
      (seqN OLTheory h Gamma [] (>> RulesDefs TENSORPAR Right A B)) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> ! RulesDefs TENSORPAR Right A B).
    intros;simpl in *.
    apply seqNtoSeq in H.
    apply WeakTheory with (theory := OLTheory);auto using TheoryEmb1.
    InvTriAll'.
    simpl in H6.
    solveLL'.
  Qed.
  
  Theorem FocusingRightCte : forall n Gamma R C th,
      (seqN th n Gamma [u| R|] (>> makeRuleConstant C Right)) ->
      IsPositiveLAtomFormulaL Gamma ->
      exists m, n = S m /\
                R = t_cons C /\
                seqN th m Gamma []  (>> CteRulesDefs (rulesCte C) Right).
  Proof with solveF.
    intros.
    inversion H...
    inversion H7...
    simpl in H3.
    inversion H3...
    eexists;eauto.
    apply NotUpInLAtom in H6...
  Qed.

  Theorem FocusingLeftCte : forall n Gamma R C th,
      (seqN th n Gamma [u| R|] (>> makeRuleConstant C Left)) ->
      IsPositiveLAtomFormulaL Gamma ->
      exists m,
        n = S m /\
        ( In (d| t_cons C |) Gamma /\
          seqN th m Gamma [u| R|]  (>> CteRulesDefs (rulesCte C) Left)).
  Proof with solveF.
    intros.
    InvTriAll.
    simpl in H3.
    inversion H3.
    subst.
    eexists.
    split...
  Qed.
  
  Theorem FocusingRightRule : forall n Gamma R  C A B th,
      (seqN th n Gamma [u| R|] (>> makeRuleBin C Right A B)) ->
      IsPositiveLAtomFormulaL Gamma ->
      exists m , n = S m /\
                 R = t_bin C A B /\
                 seqN th m Gamma []  (>> RulesDefs (rulesBin C) Right A B).
  Proof with solveF.
    intros.
    inversion H...
    inversion H7...
    simpl in H3. inversion H3...
    eexists;eauto.
    apply NotUpInLAtom in H6...
  Qed.

  Theorem FocusingLeftRule : forall n Gamma R C A B th,
      (seqN th n Gamma [u| R|] (>> makeRuleBin C Left A B)) ->
      IsPositiveLAtomFormulaL Gamma ->
      exists m , n = S m /\
                 ( In (d|t_bin C A B|) Gamma /\
                   seqN th m Gamma [u|R|]  (>> RulesDefs (rulesBin C) Left A B)) .
  
  Proof with solveF.
    intros.
    InvTriAll.
    simpl in H3.
    inversion H3.
    eexists;eauto.
    split;eauto.
    split;eauto.
    subst...
  Qed.

  Theorem AppPARTENSORRight :
    forall n  Gamma Delta A B th,
      (seqN th n Gamma Delta (>> RulesDefs PARTENSOR Right A B)) ->
      exists m , n = S(S(S m))  /\
                 Delta = [] /\
                 (seqN th m Gamma [u| A |] (> []) ) /\
                 (seqN th m Gamma [u| B |] (> []) ) .
  Proof with solveF.
    intros.
    simpl in H.
    InvTriAll.
    simpl in *.
    eexists.
    split;eauto.
    apply Permutation_nil' in H2.
    split;eauto.
  Qed.

  Theorem AppPARTENSORLeft:
    forall n  Gamma Delta A B th,
      (seqN th n Gamma Delta (>> RulesDefs PARTENSOR Left A B)) ->
      exists m , n = S(S(S (S m)))  /\
                 (seqN th m (d| A | ::  d| B |:: Gamma ) Delta (> []) ) .
  Proof with solveF.
    intros.
    simpl in H.
    InvTriAll.
    eexists.
    split...
    LLExact H4.
  Qed.

  Theorem AppWITHPLUSRight :
    forall n  Gamma Delta A B th,
      (seqN th n Gamma Delta (>> RulesDefs WITHPLUS Right A B)) ->
      exists m , n = S(S(S m))  /\
                 Delta = [] /\
                 ( (seqN th m Gamma [u| A |] (> []) ) \/
                   (seqN th m Gamma [u| B |] (> []) )) .
  Proof with solveF.
    intros.
    simpl in H.
    InvTriAll.
    simpl in H6.
    eexists.
    split;eauto.
    
    eexists.
    split;eauto.
  Qed.

  Theorem AppWITHPLUSLeft :
    forall n  Gamma Delta A B th,
      (seqN th n Gamma Delta (>> RulesDefs WITHPLUS Left A B)) ->
      exists m , n = S(S(S m))  /\
                 ( (seqN th m (d| A|::Gamma) Delta (> []) ) /\
                   (seqN th m (d| B|::Gamma) Delta (> []) )) .
  Proof with solveF.
    intros.
    simpl in H.
    InvTriAll.
    eexists.
    split;eauto.
    split...
    LLExact H5.
    LLExact H4.
  Qed.

  Theorem AppTENSORPARRight :
    forall n  Gamma Delta A B th,
      (seqN th n Gamma Delta (>> RulesDefs TENSORPAR Right A B)) ->
      exists m , n = S(S(S(S m)))  /\
                 seqN th m (d| A |:: Gamma) (u| B |::Delta) (> []).
  Proof with solveF.
    intros.
    simpl in H.
    InvTriAll.
    eexists.
    split;eauto.
    LLExact H7.
  Qed.

  Theorem AppTENSORPARLeft :
    forall n  Gamma Delta A B th,
      (seqN th n Gamma Delta (>> RulesDefs TENSORPAR Left A B)) ->
      exists m  , n = S(S(S m))  /\
                  ( seqN th m Gamma [u| A |] (> [])) /\
                  ( seqN th m (d| B | :: Gamma) Delta (> [])).
  Proof with solveF.
    intros.
    simpl in H.
    InvTriAll.
    eexists.
    split;eauto.
    split.
    LLExact H9.
    LLExact H6.
    rewrite H2...
  Qed.

  Theorem PARTensorInv : forall A B Gamma R n,
      ( seq (OLTheoryCut (pred n)) (d| A | :: d| B | :: Gamma) [u| R |] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [u| R |] (>> RulesDefs PARTENSOR Left A B ) .
    intros;simpl;solveLL'.
    LLExact' H.
  Qed.

  Theorem PARTensorInvR : forall h Gamma A B n,
      (seqN OLTheory h Gamma [] (>> RulesDefs PARTENSOR Right A B)) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> ! RulesDefs PARTENSOR Right A B).
    intros;simpl in *.
    apply seqNtoSeq in H.
    apply WeakTheory with (theory := OLTheory);auto using TheoryEmb1.
    solveLL'.
    decide1' ((! u| A |) ** (! u| B |));auto.
  Qed.
  
End Bipoles.

(** Adding some new cases to [CutTac] *)

Ltac CutTacPOS :=
  CutTac;
  try
  match goal with
  | [ |-  IsPositiveLAtomFormulaL _ ] => solve  IsPositiveLSolve 

  | [  H1 : IsPositiveLAtomFormulaL ?L , H2 : ~ IsPositiveAtom ?F , H3 : Remove ?F ((_ ++ ?N)) _ |- _ ] =>
    apply Remove_In in H3; destruct H3;solveF;
    apply  Forall_forall  with (x:= F) in H1;auto;destruct H1;solveF


  | [  H1 : IsPositiveLAtomFormulaL ?N , H2 : ~ IsPositiveAtom ?F , H3 : Remove ?F ?N _ |- _ ] =>
    apply Remove_In in H3;apply  Forall_forall  with (x:= F) in H1;auto;destruct H1;solveF

  | [  H1 : IsPositiveLAtomFormulaL ?N , H2 : ~ IsPositiveAtom ?F , H3 : Remove ?F (_ :: ?N) _ |- _ ] =>
    apply Remove_In in H3;destruct H3;subst;solveF

  | [ HIn :  In ?F ?B , HB : IsPositiveLAtomFormulaL ?B , Hneg : ~ IsPositiveAtom ?F |- _]
    => let HB' := fresh in
       apply Forall_forall with (x:= F) in HB as HB';auto;subst;inversion HB';solveF

  | [ HPos : IsPositiveLAtomFormulaL ?N, HRem : Remove ?F ([ atom (up ?A)  ] ++ ?N) _, HNeg : ~ IsPositiveAtom ?F |- _] => let H' := fresh "H" in generalize (Remove_In HRem);intro H';inversion H2;subst;solveF;IsPositiveLSolve

  | [ |- Forall IsPositiveLAtomFormula ?M] => fold  (IsPositiveLAtomFormulaL M)

  | [ H: seqN _ _ _ _ (>> zero) |- _] => invTri H
  | [ H: seq  _ _ _ (>> zero) |- _] => invTri' H
  | [ |- OLTheoryCut _ _ ]=> solve [repeat (constructor;auto)]
  | [ |- OLTheory _ ]=> solve [repeat (constructor;auto)]
  | [ H : isOLConstant (t_bin _ _ _) |- _] => inversion H (* this is inconsistent *)
                                                        
  end.

  Section OLCutElimination.
    Context `{OLR: OORules}.
    Hint Constructors CutRuleN : core.
    Hint Constructors IsPositiveLAtomFormula : core .
    Hint Unfold IsPositiveLAtomFormulaL : core. 
    Hint Unfold makeRuleConstant makeRuleBin (*makeLRuleQ makeRRuleQ*) : core.
    Hint Constructors  OLTheoryCut OLTheory  : core.
    Hint Unfold RINIT RCUT : core.	
    Hint Unfold down' up' : core .

    Theorem TheoryCutIsFormula n F:
    OLTheoryCut n F -> isFormula F.
  Proof with CutTacPOS.
    intros.
    inversion H...
    inversion H0; auto using CtesIsFormula, RulesIsFormula,MRulesIsFormula.
    constructor...
    inversion H0...
    constructor...
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
      forall R : uexp,
      isOLFormula R ->
      forall Gamma : list oo,
      seqN OLTheory h1 (d| FCut | :: Gamma) [u| R |] (> []) ->
      seqN OLTheory h2 Gamma [u| FCut |] (> []) ->
      IsPositiveLAtomFormulaL Gamma -> seq (OLTheoryCut (pred n)) Gamma [u| R |] (> []).


  (** Assuming that both premises of the cut use a right rule (and
  then, the cut rule is not principal in the left premise *)
  Theorem LeftPremiseRightRuleCases n n' h h1 h2 Gamma R A B FCut C:
    (seqN OLTheory h1 (d| FCut |:: Gamma) [u| R |]
          (>> makeRuleBin C Right A B)) ->
    (seqN OLTheory (S h1) (d| FCut | ::Gamma) [u| R |] (> [])) ->
    ( seqN OLTheory (S (S h2)) Gamma [u| FCut |] (> [])) ->
    IsPositiveLAtomFormulaL Gamma ->
    S h = S h1 + S (S h2) ->
    n' <= n ->
    lengthUexp (FCut) n' ->
    isOLFormula (FCut) ->
    isOLFormula R ->
    isOLFormula (t_bin C A B) ->
    CUTDefinition n' h ->
    seq (OLTheoryCut (pred n)) Gamma [u| R |] (> []).
  Proof with CutTacPOS.
    intros Hseq1 Hseq1' Hseq2 IsGamma Hh Hn Hluexp HisC HisR HisAB IH.
    apply FocusingRightRule in Hseq1...
    CleanContext.
    remember (rulesBin C).
    destruct r.
    + apply AppPARTENSORRight in H1.
      CleanContext.
      inversion HisAB...
      decide3' (makeRuleBin C Right A B)...
      tensor'  [u| t_bin C A B |] (@nil oo)...
      rewrite <- Heqr...
      tensor' (@nil oo) (@nil oo);
        eapply IH with (h1:= x0) (h2:= S ( S h2)) (m := x0 + S ( S h2)) (FCut:=FCut);eauto...
    + apply AppWITHPLUSRight in H1.
      CleanContext.
      inversion HisAB...
      decide3' (makeRuleBin C Right A B)...
      tensor'  [u| t_bin C A B |] (@nil oo)...
      rewrite <- Heqr...
      inversion H1.
      oplus1'.
      eapply IH with (h1:= x0) (h2:= S ( S h2)) (m := x0 + S ( S h2)) (FCut:=FCut);eauto...
      oplus2'.
      eapply IH with (h1:= x0) (h2:= S ( S h2)) (m := x0 + S ( S h2)) (FCut:=FCut);eauto...
    + apply AppTENSORPARRight in H1.
      CleanContext.
      inversion HisR...
      decide3' (makeRuleBin C Right A B)...
      tensor'  [u| t_bin C A B |] (@nil oo).
      rewrite <- Heqr... solveLL'.
      rewrite Permutation_app_comm...
      apply IH with (m:=x0 + S (S h2)) (h2 := S (S h2))  (h1:= x0) (FCut:=FCut)...
      rewrite perm_swap...
      eapply weakeningN...
  Qed.
  
  (** Assuming that the cut formula in the right premise of the cut
  was principal, we analyze the cases of the left premise.
  Here we assume that the cut-formula is a constant
   *)
  Theorem RCtePrincipalLCases n n' h h1 h2 Gamma R C :
    (seqN OLTheory (S ( S h1)) (d| t_cons C |:: Gamma) [u| R |] (> [])) ->
    (seqN OLTheory h2 Gamma [] (>> CteRulesDefs (rulesCte C) Right)) ->
    (seqN OLTheory (S (S h2)) Gamma [u| t_cons C |] (> [])) ->
    IsPositiveLAtomFormulaL Gamma ->
    S h = S (S h1) + S (S h2) ->
    n' <= n ->
    lengthUexp (t_cons C) n' ->
    isOLFormula (t_cons C) ->
    isOLFormula R ->
    CUTDefinition n' h ->
    seq (OLTheoryCut (pred n)) Gamma [u| R |] (> []).
  Proof with CutTacPOS.
    intros Hseq1 Hseq2 Hseq2' IsGamma Hh Hn Hluexp HisC HisR IH .
    (** By case analysis on the continuation of HSeq1 *)
    inversion Hseq1...
    inversion H1... (* F must be an atom, a contradiction *)
    inversion H0...
    { (* rule *)
      inversion H...
      + (* right constant --- Never principal --- *)
        apply FocusingRightCte in H2...
        CleanContext.
        remember (rulesCte C0).
        destruct c;simpl in H4...
        decide3' (makeRuleConstant C0 Right)...
        tensor' [u| t_cons C0 |] (@nil oo).
        rewrite <- Heqc... solveLL'.
      + (* left constant *)
        apply FocusingLeftCte in H2...
        CleanContext.
        inversion H2;CleanContext.
        inversion H5...
        remember (rulesCte C0).
        destruct c;simpl in *...

        remember (rulesCte C0).
        destruct c;simpl in *...

        decide3' (makeRuleConstant C0 Left) .
        tensor' (@nil oo) [u|R|].
        rewrite <- Heqc... solveLL'.
      + (* Right Rule --- Never principal --- *)
        apply FocusingRightRule in H2...
        CleanContext.
        remember (rulesBin C0).
        destruct r...
        ++ apply AppPARTENSORRight in H4...
           CleanContext.
           inversion H3...
           decide3' (makeRuleBin C0 Right F0 G)...
           tensor' [u| t_bin C0 F0 G |] (@nil oo).
           rewrite <- Heqr...
           tensor' (@nil oo) (@nil oo);
             apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
        ++ apply AppWITHPLUSRight in H4...
           CleanContext.
           inversion H3...
           decide3' (makeRuleBin C0 Right F0 G)...
           tensor' [u| t_bin C0 F0 G |] (@nil oo).
           rewrite <- Heqr...
           destruct H5.
           oplus1'. apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           oplus2'. apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
        ++ apply AppTENSORPARRight in H4...
           CleanContext.
           inversion H3...
           decide3' (makeRuleBin C0 Right F0 G)...
           tensor' [u| t_bin C0 F0 G |] (@nil oo).
           rewrite <- Heqr...
           solveLL'...
           rewrite Permutation_app_comm...
           rewrite perm_swap in H4.
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           apply weakeningN...
      + (* left Rule Can be principal or not *)
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
           tensor' (@nil oo) [u| R |]...
           rewrite <- Heqr... solveLL'.
           LLPerm (d| F0 | :: d| G | :: Gamma).
           LLPermH H6 (d| t_cons C| :: d| F0 | :: d| G | :: Gamma) .
           inversion H3...
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           eapply weakeningN.
           eapply weakeningN...
        ++ apply AppWITHPLUSLeft in H4.
           CleanContext.
           inversion H3...
           decide3' (makeRuleBin C0 Left F0 G)...
           tensor' (@nil oo) [u| R |].
           permswap H6.
           permswap H7.
           rewrite <- Heqr... solveLL';rewrite Permutation_app_comm...
           
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           eapply weakeningN...
           
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           eapply weakeningN...
        ++ apply AppTENSORPARLeft in H4.
           CleanContext.
           inversion H3...
           decide3' (makeRuleBin C0 Left F0 G)...
           tensor' (@nil oo) [u| R |].
           rewrite <- Heqr...
           tensor' (@nil oo) [u| R |].
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           rewrite Permutation_app_comm...
           permswap H7.
           apply IH with (m:=x0 + S (S h2)) (h2:=S (S h2))  (h1:= x0) (FCut:=(t_cons C))...
           eapply weakeningN...
    }
    { (* init *)
      apply Init_inversion1  in H2...
      inversion H3...
      subst.
      apply WeakTheory with (theory := OLTheory);auto using TheoryEmb1.
      decide3' (makeRuleConstant C Right)...
      tensor' [u| t_cons C |] (@nil oo).
      apply seqNtoSeq in Hseq2...
      decide3' (RINIT OO).
      tensor' [u| OO |] (@nil oo).
    }
  Qed.

  Ltac SolveIsFormulas :=
    try
      match goal with
      | [ |- isNotAsyncL [u| _ |] ] => constructor;auto
      | [ |- Notasynchronous (u| _ |)] => let H':= fresh in intro H'; inversion H'
      | [ |- Forall Notasynchronous []] => constructor;auto
      | [ |- isNotAsyncL []] => constructor;auto
      end.
  
  Hint Constructors isFormula : core.
  Theorem CutObjectLL: forall T A B C Gamma R n n', 
      (seq (OLTheoryCut (pred n)) Gamma [u| R |] (>> RulesDefs T Left A B)) ->
      (seq (OLTheoryCut (pred n)) Gamma [] (>> ! RulesDefs T Right A B)) ->
      isOLFormula (t_bin C A B) ->
      lengthUexp (t_bin C A B) n' ->
      n' <= n ->
      IsPositiveLAtomFormulaL Gamma ->
      seq (OLTheoryCut (pred n)) Gamma [u| R |] (> []).
  Proof with CutTacPOS.
    intros.
    LLPerm ([ u|R|] ++ []).
    apply @GeneralCut' with (dualC:= ! RulesDefs T Right A B) (C := ? ( RulesDefs T Right A B)^);CutTac;SolveIsFormulas;eauto using RulesPerpIsFormula, RulesBangIsFormula, IsPositiveLIsFormula,TheoryCutIsFormula.
    rewrite <- ng_involutive...
    SolveIsFormulas.
    
    LLPerm ([] ++ [ u|R|] ).
    apply @GeneralCut' with (dualC:=  RulesDefs T Left A B ) (C:= ( RulesDefs T Left A B) ^);CutTac;eauto using RulesPerpIsFormula, RulesBangIsFormula, IsPositiveLIsFormula,RulesIsFormula,TheoryCutIsFormula; SolveIsFormulas.
    rewrite <- ng_involutive...
    SolveIsFormulas.
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
  Theorem RBinPrincipalLCases n n' h h1 h2 Gamma R C A B:
    (seqN OLTheory h1 (d|t_bin C A B|::Gamma) [u| R |] (> [])) ->
    (seqN OLTheory h2 Gamma [] (>> RulesDefs (rulesBin C) Right A B)) ->
    (seqN OLTheory (S (S h2)) Gamma [u| t_bin C A B |] (> [])) ->
    IsPositiveLAtomFormulaL Gamma ->
    S h = h1 + S (S h2) ->
    n' <= n ->
    lengthUexp (t_bin C A B) n' ->
    isOLFormula (t_bin C A B) ->
    isOLFormula R ->
    CUTDefinition n' h ->
    seq (OLTheoryCut (pred n)) Gamma [u| R |] (> []).
  Proof with CutTacPOS.
    intros Hseq1 Hseq2 Hseq2' IsGamma Hh Hn Hluexp HisC HisR IH.
    (** By case analysis on the continuation of HSeq1 *)
    inversion Hseq1...
    inversion H0...
    inversion H...
    { (* rule *)
      inversion H2...
      + (* right cte never principal *)
        apply FocusingRightCte in H1...
        CleanContext.
        remember (rulesCte C0).
        destruct c;simpl in H4...
        decide3' (makeRuleConstant C0 Right)...
        tensor' [u| t_cons C0 |] (@nil oo).
        rewrite <- Heqc... solveLL'.
      + (* left cte *)
        apply FocusingLeftCte in H1...
        CleanContext.
        destruct H1;CleanContext.
        inversion H0...
        remember (rulesCte C0).
        destruct c;simpl in *...
        decide3' (makeRuleConstant C0 Left)...
        tensor'  (@nil oo) [u| R |].
        rewrite <- Heqc... solveLL'.
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
              assert(Cut1:  seq (OLTheoryCut (pred n)) ( d| F0 | :: d| G | :: Gamma) [u| R |] (> [])) .
              apply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C0 F0 G)...
              do 2 eapply weakeningN...
              assert(Cut2: seq (OLTheoryCut (pred n)) Gamma [u| R |] (>> RulesDefs PARTENSOR Left F0 G )) by (apply PARTensorInv;auto).
              assert(Cut3: seq (OLTheoryCut (pred n)) Gamma [] (>> ! RulesDefs PARTENSOR Right F0 G)) by (eapply PARTensorInvR;eauto).
              eapply CutObjectLL;eauto.
              
          +++ apply AppWITHPLUSLeft in H5.
              CleanContext.
              inversion H3...
              permswap H5.
              permswap H6.
              assert(Cut1:  seq (OLTheoryCut (pred n))  (d| F0 | :: Gamma) [u| R |] (> [])).
              apply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C0 F0 G)...
              apply weakeningN...
              assert(Cut1':  seq (OLTheoryCut (pred n))  (d| G | :: Gamma) [u| R |] (> [])).
              apply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C0 F0 G)...
              apply weakeningN...
              
              
              assert(Cut2: seq (OLTheoryCut (pred n)) Gamma [u| R |] (>> RulesDefs WITHPLUS Left F0 G )) by (apply WITHPlusInv;auto).
              assert(Cut3: seq (OLTheoryCut (pred n)) Gamma [] (>> ! RulesDefs WITHPLUS Right F0 G)) by (eapply WITHPlusInvR;eauto).
              eapply CutObjectLL;eauto.
              
          +++ apply AppTENSORPARLeft in H5.
              CleanContext.
              inversion H3...
              permswap H6.
              assert(Cut1:  seq (OLTheoryCut (pred n))  Gamma [u| F0 |] (> [])).
              apply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C0 F0 G)...
              assert(Cut1':  seq (OLTheoryCut (pred n))  (d|G| :: Gamma) [u| R |] (> [])).
              apply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C0 F0 G)...
              apply weakeningN...

              assert(Cut2: seq (OLTheoryCut (pred n)) Gamma [u| R |] (>> RulesDefs TENSORPAR Left F0 G )) by (apply TENSORParInv;auto). 
              
              assert(Cut3: seq (OLTheoryCut (pred n)) Gamma [] (>> ! RulesDefs TENSORPAR Right F0 G)) by (eapply TENSORParInvR;eauto).
              eapply CutObjectLL;eauto.
              
        ++ (* None Principal *)
          inversion H3...
          remember (rulesBin C0).
          destruct r.
          +++ apply AppPARTENSORLeft in H5.
              CleanContext.
              decide3' (makeRuleBin C0 Left F0 G  ) ...
              tensor' (@nil oo) [u| R |]...
              rewrite <- Heqr... solveLL'.
              LLPerm  (d| F0 | :: d| G | :: Gamma).
              LLPermH H6   (d|t_bin C A B|:: d| F0 | :: d| G | :: Gamma).
              apply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C A B)...
              do 2 eapply weakeningN...
          +++ apply AppWITHPLUSLeft in H5.
              CleanContext.
              decide3' (makeRuleBin C0 Left F0 G  ) .
              tensor' (@nil oo) [u| R |].
              permswap H6.
              permswap H7.
              rewrite <- Heqr... solveLL';rewrite Permutation_app_comm...
              eapply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C A B)...
              eapply weakeningN...
              eapply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C A B)...
              eapply weakeningN...
          +++ apply AppTENSORPARLeft in H5.
              CleanContext.
              decide3' (makeRuleBin C0 Left F0 G  ) .
              permswap H7.
              tensor' (@nil oo) [u| R |].
              rewrite <- Heqr...
              tensor' (@nil oo) [u| R |].
              eapply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C A B)...
              rewrite Permutation_app_comm...
              eapply IH with (h1 := x0) (h2:=S (S h2)) (m := x0+ S (S h2)) (FCut:= t_bin C A B)...
              eapply weakeningN...
    } 
    { (* init *)
      apply Init_inversion1  in H1...
      inversion H3...
      subst.
      apply WeakTheory with (theory := OLTheory);auto using TheoryEmb1.
      apply seqNtoSeq in Hseq2'...
      decide3' (RINIT OO).
      tensor' [u| OO |] (@nil oo).
    }
  Qed.


  (* LeftRule applied on the right premise of the cut. This case in never principal *)
  Theorem LeftRuleOnRightPremise n n' h h1 h2 Gamma FCut R C A B :
    (seqN OLTheory h1 (d|FCut| :: Gamma) [u| R |] (> [])) ->
    (seqN OLTheory h2 Gamma [u| FCut |] (>> makeRuleBin C Left A B)) ->
    (seqN OLTheory (S h2) Gamma [u| FCut |] (> [])) ->
    IsPositiveLAtomFormulaL Gamma ->
    S h = h1 + S h2 ->
    n' <= n ->
    lengthUexp FCut n' ->
    isOLFormula FCut ->
    isOLFormula R ->
    isOLFormula (t_bin C A B) ->
    CUTDefinition n' h ->
    seq (OLTheoryCut (pred n)) Gamma [u| R |] (> []).
  Proof with CutTacPOS.
    intros Hseq1 Hseq2 Hseq2' IsGamma Hh Hn Hluexp HisFcut HisR HisAB IH.
    apply FocusingLeftRule in Hseq2...
    CleanContext.
    inversion HisAB...
    remember (rulesBin C).
    destruct r...
    + apply AppPARTENSORLeft in H1...
      CleanContext.
      apply weakeningGenN with (CC':= [atom (down'  A); atom (down' B)]) in Hseq1;simpl in Hseq1.
      decide3' ( makeRuleBin C Left A B)...
      tensor' (@nil oo)  [u| R | ].
      rewrite <-  Heqr... solveLL'.
      LLPermH Hseq1 (d| FCut | :: atom (down' A) :: atom (down' B)  :: Gamma) .
      LLPerm (atom (down' A) :: atom (down' B) :: Gamma)...
      eapply IH with (h1 := h1) (h2:=x0) (m := h1+ x0) (FCut := FCut)...
    + apply AppWITHPLUSLeft in H1...
      CleanContext.
      
      decide3' ( makeRuleBin C Left A B)...
      tensor' (@nil oo)  [u| R |].
      rewrite <-  Heqr... solveLL'.
      
      apply weakeningGenN with (CC':= [atom (down'  A)]) in Hseq1.
      LLPermH Hseq1 (d| FCut | :: Gamma ++ [atom (down' A)]).
      eapply IH with (h1 := h1) (h2:=x0) (m := h1+ x0) (FCut := FCut)...
      rewrite Permutation_app_comm...

      apply weakeningGenN with (CC':= [atom (down'  B)]) in Hseq1.
      LLPermH Hseq1 (d| FCut | :: Gamma ++ [atom (down' B)]).
      eapply IH with (h1 := h1) (h2:=x0) (m := h1+ x0) (FCut := FCut)...
      rewrite Permutation_app_comm...

    + apply AppTENSORPARLeft in H1...
      CleanContext.
      decide3' ( makeRuleBin C Left A B)...
      tensor' (@nil oo)  [u| R |].
      rewrite <-  Heqr... 
      tensor' (@nil oo)  [u| R |].
      apply seqNtoSeq in H1.
      apply WeakTheory with (theory' := (OLTheoryCut (pred n)) ) in H1 ;auto using TheoryEmb1;CutTac.

      rewrite Permutation_app_comm...
      apply weakeningGenN with (CC':= [atom (down'  B)]) in Hseq1.
      eapply IH with (h1 := h1) (h2:=x0) (m := h1+ x0) (FCut := FCut)...
      LLPerm ([atom (down' B)] ++ d| FCut | :: Gamma)...
  Qed.


  Theorem CutElimStep:
    forall h1 h2 n n' Gamma R Fcut,
      (seqN OLTheory h1 (d|Fcut|:: Gamma) [u|R|] (> [])) ->
      (seqN OLTheory h2 Gamma [u|Fcut|] (> [])) ->
      isOLFormula Fcut ->
      isOLFormula R ->
      IsPositiveLAtomFormulaL Gamma ->
      lengthUexp Fcut n' ->
      n' <= n ->
      (seq (OLTheoryCut (pred n)) Gamma [u|R|]  (> [])).
  Proof with CutTacPOS.
    intros h1 h2 n n' Gamma R FCut Hseq1 Hseq2 HIsFcut HIsR HIsGamma HLeng Hnn'.
    remember (plus h1 h2) as h.
    generalize dependent Gamma.
    generalize dependent R.
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
    inversion H...
    { (* from the theory *)
      inversion H2...
      { (* Right Constant (in the right premise of the cut *)
        apply FocusingRightCte in H1...
        CleanContext.
        (* principal case depending on the left premise *)
        inversion Hseq1...
        inversion H1...
        inversion H0... 
        { (* a rule was applied *)
          inversion H6...
          + (* Right rule never is principal *)
            apply FocusingRightCte in H5...
            CleanContext.
            remember (rulesCte C0).
            destruct c;simpl in H8...
            decide3' (makeRuleConstant C0 Right ) .
            tensor' [u| t_cons C0 |] (@nil oo).
            rewrite <- Heqc...
            solveLL'.
          + (* Left Constant : may be principal *)
            apply FocusingLeftCte in H5...
            CleanContext.
            destruct H5;CleanContext.
            (* Principal case *)
            eapply RCtePrincipalLCases with (h1:= x0) (h2:= x);eauto.
            (* Non principal case *)
            remember (rulesCte C0).
            destruct c...
            decide3' (makeRuleConstant C0 Left ) .
            tensor' (@nil oo)  [u| R |].
            rewrite <-Heqc... solveLL'.
            simpl in H8...
          + (* Right Rule is never principal *)
            eapply LeftPremiseRightRuleCases with (h1:= n0) (h2:= x);eauto.

          + (* Left rule may or may not be principal *)
            apply FocusingLeftRule in H5...
            CleanContext.
            destruct H5;CleanContext;
              eapply RCtePrincipalLCases with (h1:= x0) (h2:= x);eauto.
        }
        { (* init was applied *)
          apply Init_inversion1  in H5...
          inversion H7...
          subst.
          
          apply seqNtoSeq in Hseq2...
          apply WeakTheory with (theory' := (OLTheoryCut (pred n)) ) in Hseq2 ;auto using TheoryEmb1;CutTac.

          decide3' (RINIT OO).
          tensor' [u| OO|] (@nil oo).
        }
      }
      { (* Left Constant -- never principal --*)
        apply FocusingLeftCte in H1...
        CleanContext.
        remember (rulesCte C).
        destruct c...
        decide3' (makeRuleConstant C Left ).
        tensor' (@nil oo)  [u| R |].
        rewrite <- Heqc...
        solveLL'.
        simpl in H4...
      }
      { (* Right Rule *)
        apply FocusingRightRule in H1...
        CleanContext.
        eapply RBinPrincipalLCases with (h1:=h1) (h2:=x);eauto.
      }
      { (* left rule --- never principal ---*)
        eapply LeftRuleOnRightPremise;eauto.
      }
    }
    { (* init *)
      apply Init_inversion1 in H1...
      apply contractionN in Hseq1...

      apply seqNtoSeq in Hseq1...
      apply WeakTheory with (theory' := (OLTheoryCut (pred n)) ) in Hseq1 ;auto using TheoryEmb1;CutTac.
    }
  Qed.

  Theorem CutElimination:
    forall n h  Gamma R,
      (seqN (OLTheoryCut n) h Gamma [u|R|]  (> [])) ->
      IsPositiveLAtomFormulaL Gamma ->
      isOLFormula R ->
      (seq  OLTheory Gamma [u|R|]  (> [])).
  Proof with CutTacPOS.
    induction n;induction h using strongind ; intros; try solve[inversion H].

    apply WeakTheoryN with (theory' := OLTheory) in H0.
    apply seqNtoSeq in H0...
    apply OOTheryCut0.

    inversion H0...
    inversion H4...
    + inversion H3...
      ++ apply FocusingRightCte in H6...
         CleanContext.
         apply seqNtoSeq in H8.
         remember (rulesCte C).
         destruct c;simpl in *...
         decide3' (makeRuleConstant C Right).
         tensor' [u| t_cons C |] (@nil oo).
         rewrite <- Heqc... solveLL'.
      ++ apply FocusingLeftCte in H6...
         CleanContext.
         apply seqNtoSeq in H8.
         remember (rulesCte C).
         destruct c;simpl in *...
         decide3' (makeRuleConstant C Left).
         tensor' (@nil oo) [u| R |] .
         rewrite <- Heqc... solveLL'.
      ++ apply FocusingRightRule in H6...
         CleanContext.
         remember (rulesBin C).
         destruct r...
         +++ apply AppPARTENSORRight in H8.
             CleanContext.
             inversion H7...
             apply H in H8...
             apply H in H9...
             decide3' (makeRuleBin C Right F0 G).
             tensor'  [u| t_bin C F0 G |] (@nil oo).
             rewrite <- Heqr...
             tensor' (@nil oo)(@nil oo).
         +++ apply AppWITHPLUSRight in H8.
             CleanContext.
             inversion H7...
             inversion H8...
              
             apply H in H5...
             decide3' (makeRuleBin C Right F0 G)...
             tensor'  [u| t_bin C F0 G |] (@nil oo)...
             rewrite <- Heqr...
             oplus1'.

             apply H in H5...
             decide3' (makeRuleBin C Right F0 G)...
             tensor'  [u| t_bin C F0 G |] (@nil oo)...
             rewrite <- Heqr...
             oplus2'.
         +++ apply AppTENSORPARRight in H8.
             CleanContext.
             inversion H7...
             apply H in H6...
             decide3' (makeRuleBin C Right F0 G)...
             tensor'  [u| t_bin C F0 G |] (@nil oo)...
             rewrite <- Heqr...
             solveLL'.
             LLExact' H6.
      ++ apply FocusingLeftRule in H6...
         CleanContext.
         remember (rulesBin C).
         destruct r...
         +++ apply AppPARTENSORLeft in H8.
             CleanContext.
             inversion H7...
             apply H in H8...
             decide3' (makeRuleBin C Left F0 G)...
             tensor' (@nil oo) [u|R|].
             rewrite <- Heqr...
             solveLL'.
             LLExact' H8.
         +++ apply AppWITHPLUSLeft in H8.
             CleanContext.
             inversion H7...
             apply H in H8...
             apply H in H9...
             decide3' (makeRuleBin C Left F0 G)...
             tensor' (@nil oo) [u|R|].
             rewrite <- Heqr...
             solveLL'.
             LLExact' H8.
             LLExact' H9.
         +++ apply AppTENSORPARLeft in H8.
             CleanContext.
             inversion H7...
             apply H in H8...
             apply H in H9...
             decide3' (makeRuleBin C Left F0 G)...
             tensor' (@nil oo) [u|R|].
             rewrite <- Heqr...
             tensor' (@nil oo) [u|R|].
             LLExact' H9.
    + apply Init_inversion1 in H6...
      decide3' (RINIT OO).
      tensor' [u| OO|] (@nil oo).
    + (* Cut used *)
      inversion H3...
      InvTriAll.
      simpl in *.
      rewrite Permutation_app_comm in H16;simpl in H16.
      rewrite app_nil_r in H12...
      apply H in H16...
      apply H in H19...
      apply seqtoSeqN in H16.
      apply seqtoSeqN in H19.
      CleanContext.
      assert(HCut: seq (OLTheoryCut (pred (S n))) Gamma [u| R |] (> [])).
      eapply CutElimStep;eauto...
      simpl in HCut.
      apply seqtoSeqN in HCut.
      CleanContext.
      apply IHn in H10...
  Qed.
End OLCutElimination.
