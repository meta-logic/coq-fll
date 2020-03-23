(** * Syntax of First Order Linear Logic (LL)
This file defines the syntax of formulas in first-order linear logic
(type [oo]). Predicate [isFormula] determines when a term is a valid
LL formula (ruling out exotic terms). Proofs usually proceed by
induction on the fact that a term satisfies this property.
 *)

Require Export FLL.Misc.Utils.
Require Export FLL.Misc.Hybrid.
Require Export Lia.
Require Import Coq.Logic.FunctionalExtensionality.


Export ListNotations.
Set Implicit Arguments.

(** ** External definitions for the Object Logic (OL)
The class [OLSig] specifies the external definitions for terms and
atomic propositions of the object logic. The syntax is parametric on:

 - [atm] : type for atomic propositions (judgments at the Object Logic level)
 - [con] : type for syntactic constructors at the OL level
 - [uniform_atm] : predicate ruling out exotic terms at the OL level
 *)

Class OLSig :=
  {
    (* Signature for atoms (judgments at the OL level) *)
    atm:Set; 
    (* Type for constants (constructors for OL syntax) *)
    con:Set; 
    (* predicate ruling out exotic terms for atoms *)
    uniform_atm : (expr con -> atm) -> Prop
  }.



Section LLSyntax.
  Context `{OLS: OLSig}.
  
  (** Connectives of the logic *)
  Inductive oo : Set :=
  | atom : atm -> oo
  | perp : atm -> oo
  | Top : oo
  | One : oo
  | Zero : oo
  | Bot : oo 
  | AAnd : oo -> oo -> oo
  | MAnd : oo -> oo -> oo
  | AOr : oo -> oo -> oo
  | MOr : oo -> oo -> oo 
  | Bang : oo -> oo
  | Quest : oo -> oo 
  | All : (expr con -> oo) -> oo 
  | Some : (expr con -> oo) -> oo.
  
  (** Complexity of formulas *)
  Fixpoint complexity (X:oo) :=
    match X with
    | atom A   => 1
    | perp A   => 1
    | One => 1
    | Bot => 1
    | Zero => 1
    | Top => 1
    | MAnd F G => 1+ complexity F + complexity G
    | AAnd F G => 1+ complexity F + complexity G
    | MOr F G => 1+ complexity F + complexity G
    | AOr F G => 1+ complexity F + complexity G
    | Bang F   => 1+ complexity F
    | Quest F  => 1+ complexity F
    | Some FX => 1+ complexity (FX (VAR con 0))
    | All FX => 1+ complexity (FX (VAR con 0))
    end.

  (** Complexity on list of formulas *)
  Fixpoint complexityL (L: list oo) :=
    match L with
    | nil => 0
    | a :: L' => complexity a + complexityL L'
    end.

  Lemma Complexity0 : forall F, complexity F > 0.
    induction F;simpl;lia.
  Qed.

  Lemma ComplexityL0 : forall L, complexityL L =0 -> L = [].
    intros;destruct L;simpl;auto.
    simpl in H.
    generalize (Complexity0 o);intros.
    lia.
  Qed.
  
  (** Classical linear logic dualities *)
  Fixpoint dual (X: oo) :=
    match X with
    | atom A   => perp A
    | perp A   => atom A
    | One => Bot
    | Bot => One
    | Zero => Top
    | Top => Zero
    | MAnd F G => MOr (dual  F) (dual G)
    | AAnd F G => AOr (dual  F) (dual G)
    | MOr F G => MAnd (dual  F) (dual G)
    | AOr F G => AAnd (dual  F) (dual G)
    | Bang F   => Quest (dual F)
    | Quest F  => Bang (dual   F)
    | Some X => All (fun x => dual  (X x))
    | All X => Some (fun x => dual (X x))
    end.

  (** Negation is involutive *)
  Theorem ng_involutive: forall F: oo, F = dual (dual F).
  Proof.
    intro. 
    induction F; simpl; auto;
      try( try(rewrite <- IHF1); try(rewrite <- IHF2); try(rewrite <- IHF);auto);
      try(assert (o = fun x =>  dual (dual (o x))) by
             (extensionality e; apply H); rewrite <- H0; auto).
  Qed.

  Lemma DualComplexity : forall F, complexity F = complexity (dual F) .
    intros.
    induction F;intros;auto;
      try solve
          [simpl; try rewrite IHF; try rewrite IHF1; try rewrite IHF2;auto].
  Qed.

  (**  Linear Implication *)
  Definition Limp (F G : oo) : oo := MOr (dual F) G .

  (** Uniform Predicate (ruling out exotic terms) *)
  Inductive uniform_oo: (expr con -> oo) -> Prop := 
  | uniform_atom: forall (a: expr con -> atm),
      uniform_atm a -> uniform_oo (fun x => (atom (a x)))
  | uniform_perp: forall (a: expr con -> atm),
      uniform_atm a -> uniform_oo (fun x => (perp (a x)))
  | uniform_Top: uniform_oo (fun x => Top)
  | uniform_One: uniform_oo (fun x => One)
  | uniform_Bot: uniform_oo (fun x => Bot)  
  | uniform_Zero: uniform_oo (fun x => Zero)
  | uniform_AAnd: forall (A B: expr con -> oo),
      uniform_oo A -> uniform_oo B -> uniform_oo (fun x => (AAnd (A x) (B x)))
  | uniform_MAnd: forall (A B: expr con -> oo),
      uniform_oo A -> uniform_oo B -> uniform_oo (fun x => (MAnd (A x) (B x)))
  | uniform_AOr: forall (A B: expr con -> oo),
      uniform_oo A -> uniform_oo B -> uniform_oo (fun x => (AOr (A x) (B x)))
  | uniform_MOr: forall (A B: expr con -> oo),
      uniform_oo A -> uniform_oo B -> uniform_oo (fun x => (MOr (A x) (B x))) 
  | uniform_Bang: forall (A: expr con -> oo),
      uniform_oo A -> uniform_oo (fun x => (Bang (A x)))
  | uniform_Quest: forall (A: expr con -> oo), 
      uniform_oo A -> uniform_oo (fun x => (Quest (A x)))
  | uniform_All: forall (A: expr con -> expr con -> oo),
      (forall y:expr con, uniform_oo (fun x => (A y x))) ->
      uniform_oo (fun x => (All (fun y => (A y x))))
  | uniform_Some: forall (A: expr con -> expr con -> oo),
      (forall y:expr con, uniform_oo (fun x => (A y x))) ->
      uniform_oo (fun x => (Some (fun y => (A y x)))).

  (** Well formedness condition  *)
  Inductive isFormula: oo -> Prop  :=
  | wf_atm : forall (P1:atm), isFormula (atom P1)
  | wf_perp : forall (P1:atm), isFormula (perp P1)
  | wf_Top : isFormula Top
  | wf_One : isFormula One
  | wf_Zero : isFormula Zero
  | wf_Bot : isFormula Bot
  | wf_AAnd : forall (A1 A2 :oo), isFormula A1  -> isFormula A2  -> isFormula (AAnd A1 A2)
  | wf_MAnd : forall (A1 A2 :oo), isFormula A1  -> isFormula A2  -> isFormula (MAnd A1 A2)
  | wf_AOr : forall (A1 A2 :oo), isFormula A1  -> isFormula A2  -> isFormula (AOr A1 A2)
  | wf_MOr : forall (A1 A2 :oo), isFormula A1  -> isFormula A2  -> isFormula (MOr A1 A2)
  | wf_Bang : forall (A1 :oo), isFormula A1 -> isFormula (Bang A1)
  | wf_Quest : forall (A1 :oo), isFormula A1 -> isFormula (Quest A1)
  | wf_All : forall (A : expr con -> oo), uniform_oo A -> (forall t: expr con, isFormula (A t)) -> isFormula (All A)
  | wf_Some : forall (A : expr con -> oo), uniform_oo A -> (forall t: expr con, isFormula (A t)) -> isFormula (Some A).

  Hint Constructors isFormula : core.

  
  Lemma ComplexityUniformEq : forall FX x y , uniform_oo FX ->
                                            proper x -> proper y ->
                                            complexity (FX x) =  complexity (FX y).
    intros.
    induction H;subst;simpl;firstorder.
  Qed.
  
  (** Well formendness conditions for lists and arrows *)
  Definition isFormulaL  (L:list oo)  := Forall isFormula L. 
  Definition multiset := list.
  Hint Constructors Remove : core. 

  Lemma isFormulaIn : forall F L, 
      isFormulaL L -> In F L -> isFormula F. 
  Proof.
    intros.
    unfold isFormulaL in H.
    generalize (Forall_forall isFormula L );intro.
    destruct H1.
    apply H1 with (x:= F) in H ;auto.
  Qed.

  Generalizable All Variables.
  Global Instance isFormulaL_morph : 
    Proper ((@Permutation oo) ==> Basics.impl) (Forall isFormula).
  Proof.
    unfold Proper; unfold respectful; unfold Basics.impl.
    intros.
    eapply Forall_Permute;eauto.
  Qed.  
  
  
  (** Arrows for the focused system
      - [UP] : negative phase
      - [DW] : positive phase 
   *)
  Inductive Arrow  := 
  | UP (l : list oo) (* negative phase *)
  | DW (F : oo). (* positive phase *)

  (** Transforming arrows into lists of formulas *)
  Definition Arrow2LL (A: Arrow) : list oo :=
    match A  with
    | UP l => l
    | DW F => [F]
    end.

  (** Checking when a formulas has to lose focusing *)
  Inductive release : oo -> Prop :=
  | RelNA1 : forall A,  release (atom A)
  | RelTop : release Top
  | RelBot : release Bot
  | RelPar : forall F G, release (MOr F G)
  | RelWith : forall F G, release (AAnd F G)
  | RelQuest : forall F, release (Quest F)
  | RelForall : forall FX, release (All FX).

  (** Positive formulas (focusing persists *)
  Inductive positiveFormula : oo -> Prop :=
  | PosAt : forall A,  positiveFormula (perp A)
  | PosOne : positiveFormula One
  | PosZero : positiveFormula Zero
  | PosTensor : forall F G, positiveFormula (MAnd F G)
  | PosPlus : forall F G, positiveFormula (AOr F G)
  | PosBang : forall F, positiveFormula (Bang F)
  | PosEx : forall FX, positiveFormula (Some FX).

  (** Every formula is either  a positive formula, or it must be released *)
  Theorem PositiveOrRelease : forall F,
      positiveFormula F \/ release F.
    intros.
    destruct F;try (left;constructor);try(right;constructor).
  Qed.

  (** Positive formulas cannot be released *)
  Theorem PositiveNotRelease: forall F,
      positiveFormula F -> ~ release F.
    intros F H Hneg.
    inversion H;subst;inversion Hneg.
  Qed.

  Theorem ReleaseNotPositive : forall F,
      release F -> ~ positiveFormula F.
    intros F H Hneg.
    inversion H;subst;inversion Hneg.
  Qed.
  
  (** The dual of a positive formula is a release formula *)
  Theorem PositiveDualRelease : forall F,
      positiveFormula F -> release (dual F).
    intros F Hpos.
    inversion Hpos;subst;constructor.
  Qed.

  Theorem ReleaseDualPositive : forall F, release F -> positiveFormula (dual F).
    intros F Hrel.
    inversion Hrel;subst;constructor.
  Qed.
  
  (** Assynchronous connectives *)
  Inductive asynchronous : oo -> Prop :=
  | aTop :   asynchronous Top
  | aBot :   asynchronous Bot
  | aPar :   forall F G, asynchronous (MOr F G)
  | aWith :  forall F G, asynchronous (AAnd F G)
  | aQuest : forall F  , asynchronous (Quest F)
  | aForall : forall FX  , asynchronous (All FX).

  Definition Notasynchronous F := ~ (asynchronous F).
  Definition isNotAsyncL (L : list oo) := Forall Notasynchronous L.

  (** Postive atoms *)
  Inductive IsPositiveAtom : oo -> Prop :=
  | IsPAP : forall A, IsPositiveAtom (atom A).

  (** Negative atoms *)
  Inductive IsNegativeAtom : oo -> Prop :=
  | IsNAP : forall A, IsNegativeAtom (perp A).

  
  Theorem NegativeAtomDec : forall F,
      IsNegativeAtom F \/ ~ IsNegativeAtom F.
    induction F;auto; try solve[right;intro H'; inversion H'].
    left;constructor.
  Qed.

  Hint Constructors IsPositiveAtom : core.
  Theorem PositiveAtomDec : forall F,
      IsPositiveAtom F \/ ~ IsPositiveAtom F.
    destruct F;auto;right;intro H';inversion H'.
  Qed.

  (** List of positive atoms *)
  Definition IsPositiveAtomL  L : Prop := Forall IsPositiveAtom L.

  Lemma NotAsynchronousPosAtoms :
    forall F, ~ asynchronous  F -> positiveFormula F \/ IsPositiveAtom F.
    intros.
    destruct F;intuition;  first
                             [left;constructor
                             | match goal with [_:  asynchronous ?F -> False |- _] => 
                                               assert(asynchronous F) by constructor;contradiction end
                             ].
  Qed.

  Lemma AsyncRelease: forall F, asynchronous F -> release F.
  Proof.
    intros.
    inversion H; constructor.
  Qed.
  
  Lemma AsIsPosRelease: forall F,
      (asynchronous F \/ IsPositiveAtom F ) -> release F.
  Proof.
    intros.
    destruct H;auto using AsyncRelease.
    inversion H;constructor;auto.
  Qed.

  Lemma NotAsynchronousPosAtoms' :
    forall G, ~ asynchronous G ->
              IsPositiveAtom G \/ (positiveFormula G).
    intros G HG.
    apply NotAsynchronousPosAtoms in HG;tauto.
  Qed.

  Lemma  IsPositiveAtomNotAssync :
    forall F,  IsPositiveAtom F -> ~ asynchronous F.
  Proof.
    intros.
    inversion H;auto.
    intro.
    inversion H1.
  Qed.
  
  Lemma LexpPosConc : forall M F, isNotAsyncL M ->
                                  ~ asynchronous F ->
                                  isNotAsyncL (M ++ [F]).
    intros.
    apply ForallAppComm.
    apply ForallApp;auto.
  Qed.


  Lemma PosAtomConc : forall M F,  isNotAsyncL M ->
                                   IsPositiveAtom F ->
                                   isNotAsyncL (M ++ [F]).
    intros.
    apply ForallAppComm.
    apply ForallApp;auto.
    inversion H0;subst;auto.
    constructor;auto.
    intro Hn;inversion Hn.
  Qed.
  
  Lemma NegAtomConc : forall M F,  isNotAsyncL M ->
                                   IsNegativeAtom F ->
                                   isNotAsyncL (M ++ [F]).
    intros.
    apply ForallAppComm.
    apply ForallApp;auto.
    inversion H0;subst;auto.
    constructor;auto.
    intro Hn;inversion Hn.
  Qed.
  
  Lemma PosConc : forall M F,  isNotAsyncL M ->
                               positiveFormula F ->
                               isNotAsyncL (M ++ [F]).
    intros.
    apply ForallAppComm.
    apply ForallApp;auto.
    constructor;auto.
    intro Hn;inversion Hn;subst;inversion H0.
  Qed.
End LLSyntax.
