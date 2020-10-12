(** * Syntax for Object Ligics (OL). 

This file defines the general requirements imposed on the syntax of
OLs to prove cut-elimination.

 *)

Require Export FLL.Misc.Hybrid.
Require Export FLL.SL.FLLTactics.
Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

(** ** Object Logic Signature *)

(** This signature includes the types for the Object Level quantifiers
as well as the definitions for the binary and unary connectives and the
quantifiers. We assume that these types will be filled in by a Coq
inductive Set, e.g., 

[OLType := nat], 
[Inductive connectives := cand | cor | cimp . ], and 
[Inductive quantifiers := qex | qall . 
 *)

Class OLSyntax :=
  {
    OLType:Set;
    constants : Set ; (* 0 ary connectives *)
    uconnectives : Set ; (* unary connectives *)
    connectives : Set ; (* binary connectives *)
    quantifiers : Set (* quantifiers *)
  }.



(** ** Definition of the OL Syntax  *)

(** This module defines the [con] type needed in [Hybrid]. Such type
includes constructors for the atoms of the Object Logic, the binary
and unary connectives and also the quantifiers (of the object logic). 
Measures and constructors for those types are also provided *)

Section OLSyntax.
  Context `{OL: OLSyntax}.

  
  (** Syntax of the Object logic *)
  Inductive Econ: Set :=
  | oo_cons : constants -> Econ
  | oo_un : uconnectives -> Econ
  | oo_bin : connectives -> Econ (* binary connectives *)
  | oo_q : quantifiers -> Econ (* quantifiers *)
  | oo_atom : nat -> Econ (* names for atoms *)
  | oo_term : OLType -> Econ    (* Coercion --terms *)
  .

  (** Notation for Syntax *)
  Definition uexp : Set := expr Econ.
  Definition Var : var -> uexp := (VAR Econ).
  Definition Bnd : bnd -> uexp := (BND Econ).

  (** Terms *)
  Definition t_term (t:OLType)   :=  (CON (oo_term  t)) .  
  (** Atoms  *)
  Definition t_atom (id:nat) (A:uexp)  := APP (CON (oo_atom  id)) A.  (* atoms *)

    (** constants *)
  Definition t_cons (lab :constants)  := CON (oo_cons lab) .
  
  (* Unary connectives *)
  Definition t_ucon (lab : uconnectives) F    := APP (CON ( (oo_un lab ))) F .

  (** Binnary connectives *)
  Definition t_bin (lab : connectives) : uexp -> uexp -> uexp  :=
    fun M1:uexp => fun M2:uexp => (APP (APP (CON (oo_bin lab )) M1) M2).
  (** Quantifiers *)
  Definition t_quant (lab : quantifiers) : (uexp -> uexp) -> uexp :=
    fun M:uexp->uexp => (APP (CON (oo_q lab)) (lambda M)).
  
  
  (** *** Well-formedness conditions *)
  Inductive isOLTerm : uexp -> Prop :=
  | isOLTermT  : forall t, isOLTerm (t_term  t).

  Inductive isOLAtom : uexp -> Prop :=
  | isOLAtomAt : forall t id , isOLTerm t -> isOLAtom (t_atom id t).

  Inductive isOLConstant : uexp -> Prop :=
  | isOLCons : forall id , isOLConstant (t_cons id)
  .
  
  Inductive isOLFormula : uexp -> Prop :=
  | isFAtom : forall t id , isOLTerm t -> isOLFormula (t_atom id t)
  | isFCons : forall id , isOLConstant id -> isOLFormula id
  | isFUn : forall (lab : uconnectives) F ,
      isOLFormula F ->  isOLFormula ( t_ucon lab F)
  | isFBin : forall (lab : connectives) F G,
      isOLFormula F -> isOLFormula G -> isOLFormula ( t_bin lab F G)
  | isFQ : forall lab (FX : uexp -> uexp),
      uniform FX -> (forall (t:uexp), proper t -> isOLFormula (FX t)) ->
      isOLFormula (t_quant lab FX) .
  
  (** Well formendness conditions for lists of formulas and list of judgments *)
  Definition isOLFormulaL  L : Prop := Forall isOLFormula L.

  Hint Constructors isOLTerm isOLAtom isOLConstant isOLFormula : core.
  Hint Unfold isOLFormulaL : core.
  
  (* *** Complexity of OL formulas *)
  
  (** We count the number of constructors (CON) in the
  expression. Note that the measure of a formula is independent of the
  terms in the atoms *)

  Inductive lengthUexp : uexp -> nat -> Prop :=
  | l_Var : forall (v:var), lengthUexp (Var v) 0
  | l_t_term : forall (t:OLType), lengthUexp (t_term t) 0
  | l_t_atomU : forall (id:nat) (A:uexp), lengthUexp (t_atom id A) 1
  | l_cons : forall id, lengthUexp (t_cons id) 1
  | l_ucon : forall (lab:uconnectives) (M1:uexp) (n1:nat),
      lengthUexp M1 n1 ->  lengthUexp (t_ucon lab M1) (S n1)
  | l_tbin : forall (lab:connectives) (M1 M2:uexp) (n1 n2:nat),
      lengthUexp M1 n1 -> lengthUexp M2 n2 ->
      lengthUexp (t_bin lab M1 M2) (S (n1 + n2))
  | l_tall : forall (lab:quantifiers) (M:uexp -> uexp) (n:nat),
      uniform M -> lengthUexp (M (Var 0)) n -> lengthUexp (t_quant lab M) (S n).

  (** Some results regarding the length of formulas *)

  Lemma LengthTerm : forall F, isOLTerm F -> lengthUexp F 0.
    intros.
    inversion H;subst;clear H;constructor.
  Qed.
  
  Lemma LengthFormula : forall F n, isOLFormula F -> lengthUexp F n -> n > 0.
    intros.
    induction H;simpl.
    - inversion H0; lia.
    - inversion H;subst. inversion H0;lia.
    - inversion H0;subst;  lia.
    - inversion H0; lia.
    - inversion H0; lia.
  Qed.

  Lemma lengthAtom : forall id t, isOLFormula (t_atom id t)  -> lengthUexp (t_atom id t) 1.
    intros;inversion H;subst;simpl.
    inversion H1;subst;constructor.
    inversion H0;subst;constructor.
  Qed.

  Lemma lengthCons : forall id , isOLFormula (t_cons id )  -> lengthUexp (t_cons id) 1.
    intros;inversion H;subst;constructor.
  Qed.
    

    Lemma lengthUnary : forall lab F n , isOLFormula (t_ucon lab F) -> lengthUexp F n -> lengthUexp (t_ucon lab F) (S n).
    intros;subst;constructor;auto.
  Qed.

    
    Lemma lengthBin : forall lab F G n m, isOLFormula (t_bin lab F  G) -> lengthUexp F n -> lengthUexp G m -> lengthUexp (t_bin lab F G) (S (n+m)).
    intros;subst;constructor;auto.
  Qed.

  Lemma lengthAll : forall lab FX n, uniform FX -> isOLFormula (t_quant lab FX) -> lengthUexp (FX (Var 0)) n -> lengthUexp  (t_quant lab  FX) (S n).
    intros;subst.
    inversion H0;simpl;subst;constructor;auto.
  Qed.

  (** [lengthUexp] is indeed a function *)
  Lemma lengthFunction : forall n F , isOLFormula F -> lengthUexp F n -> forall n', lengthUexp F n' -> n = n'.
  Proof with auto;subst;try lia.
    induction n using strongind;intros ...
    apply LengthFormula in H0...
    
    inversion H0...
    inversion H1...
    inversion H2...

    inversion H3...
    inversion H2...
    inversion H1...

    inversion H2...
    inversion H1...
    assert (n = n1). eapply H with (F:= F0)...
    lia.
 
    inversion H2...
    inversion H1...
    assert (n0 = n1).
    eapply H with (F:= F0)...
    
    assert (n3 = n2).
    eapply H with (F:= G)...
    lia.

    inversion H2...
    inversion H1...
    apply lbindEq in H8...
    apply lbindEq in H6...
    assert (ext_eq FX M0).
    apply ext_eq_S_Symmetric...
    assert (ext_eq M M0).
    eapply ext_eq_trans;eauto.
    assert (proper (Var 0)) by constructor.
    
    assert (n = n0).
    eapply H with (F:= M0 (Var 0))...
    
    assert(isOLFormula (FX (Var 0))).
    apply H4 ...
    
    generalize (H8 (Var 0) H13);intro...
    rewrite H15...
    
    generalize (H10 (Var 0) H13);intro...
    rewrite H14 in H9...
    lia.
  Qed.

    
  Lemma lengthBinSizeL :
    forall F G C n n',
      isOLFormula F -> isOLFormula G ->
      lengthUexp (t_bin C F G) n -> lengthUexp F n' ->
      n' < n.
  Proof with auto;subst;try lia.
    intros.
    inversion H1... 
    generalize (lengthFunction H H7);intros.
    apply H3 in H2...
  Qed.
  
  Lemma lengthBinSizeR :
    forall F G C n n', isOLFormula F -> isOLFormula G ->
                       lengthUexp (t_bin C F G) n ->
                       lengthUexp G n' ->
                       n' < n.
    Proof with auto;subst;try lia.
    intros.
    inversion H1...
    generalize (lengthFunction H0 H8);intros.
    apply H3 in H2...
    Qed.

    Lemma length1 : forall F ,
        isOLFormula F -> lengthUexp F 1 ->
        isOLAtom F \/ isOLConstant F.
  Proof with subst;auto.
    intros.
    inversion H ...
    - inversion H0...
      generalize (LengthFormula H1 H3);lia.
    - inversion H0...
      assert (n1 = 0) by lia.
      generalize (LengthFormula H2 H8);intro. lia.
    -  inversion H0 ...
       generalize (lbindEq  H6  H1 H4);intro.
       assert (proper (Var 0)). constructor.
       generalize (H3 _ H5);intro. rewrite H8 in H7.
       apply H2 in H5.
       generalize (LengthFormula H5 H7 );lia.
       
  Qed.

  (** Proper conditions *)
  
  Lemma isOLTermProper : forall t, isOLTerm t -> proper t.
    intros.
    inversion H.
    unfold t_term.
    auto with hybrid.
  Qed.

  Lemma isOLAtomProper : forall t, isOLAtom t -> proper t.
    intros.
    inversion H.
    unfold t_atom.
    inversion H0;subst.
    unfold t_term.
    auto with hybrid.
  Qed.

  Lemma isOLFormulaProper : forall F, isOLFormula F -> proper F.
  Proof with repeat constructor;auto.
    intros.
    induction H.
    - inversion H ...
    - inversion H...
    - constructor; eauto with hybrid.
    - constructor; eauto with hybrid.
    - constructor; eauto with hybrid.
      
  Qed.
  
  (** ** LL predicated needed in the encoding *)
  (** Predicates [up] (formulas on the right of the HyLL sequent) and
  [down] (formulas on the left of the HyLL sequent) *)
  Inductive atm' : Set :=
  | up : uexp -> atm'    (* formulas on the right *)
  | down : uexp -> atm'  (* formulas on the left *)
  .
  
  (** Uniform Predicate for atoms *)
  Inductive uniform_atm' : (uexp -> atm') -> Prop :=
  | uniform_up: forall FX, uniform FX -> uniform_atm' (fun x:uexp => up (FX x))
  | uniform_down: forall FX, uniform FX -> uniform_atm' (fun x:uexp => down (FX x))
  .
  Hint Constructors uniform_atm' : core.

  (** Well Formedness Conditions *)
  Lemma uniform_at : forall (FX:uexp->uexp),
      uniform FX -> uniform (fun x => FX x).
  Proof.
    intros.
    auto with hybrid.
  Qed. 
  Hint Resolve uniform_at : core.

   Global Instance OLSyntaxIns : OLSig :=
    {|
      atm := atm';
      con := Econ ;
      uniform_atm := uniform_atm'
    |}.

End OLSyntax.

(** Notation for atoms of the form [up] and [down] *)
Notation "'u|' A '|'" := (atom (up A)) (at level 10) .
Notation "'d|' A '|'" := (atom (down A)) (at level 10) .
Notation "'u^|' A '|'" := (perp (up A)) (at level 10) .
Notation "'d^|' A '|'" := (perp (down A)) (at level 10) .

