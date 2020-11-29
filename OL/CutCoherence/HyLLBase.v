(*  ** HyLL System

This file introduces the syntax of HyLL (hybrid Linear logic) and its
inference rules (as an inductive type).  Files HyLL.v HyLLCut.v give
different encodings of this logic as an LL theory.
*)


Require Import FLL.SL.CutElimination.
Set Implicit Arguments.

(** We assume an external definition for the monoidal structure of HyLL *)
Class HyLLSyntax :=
  { W:Set; (* Set of Worlds *)
    ID: W;
    T : Set (* Terms of the OL *)
  }.

Section HyLL.
  Context `{OL: HyLLSyntax}.
  
  (** *** Syntax *)

  (** Constants of the syntactic elements *)
  Inductive Econ: Set :=
  | oo_term : T -> Econ (* term at the object level *)
  | oo_atom : nat  -> Econ (* Nat is the id of the predicate *)
  | oo_tensor
  | oo_impl
  | oo_bang
  | oo_all (* universal quantifier *)
  | oo_at (* F at w  *)
  | oo_arrow (* down arrow in HyLL*)
  | oo_atW (* F @ w *)
  | oo_world : W -> Econ (* building worlds from W *)
  | oo_wop (* monoidal operator on worlds: w wop w' *)
  .

  Definition uexp : Set := expr Econ.
  Definition Var : var -> uexp := (VAR Econ).
  Definition Bnd : bnd -> uexp := (BND Econ).

  (** More suitable constructors to work with *)

  (** Terms *)
  Definition t_term (t:T) : uexp := (CON (oo_term  t)) .   
  (** Atoms  *)
  Definition t_atom (id:nat) (t: uexp)  := APP (CON (oo_atom  id)) t.
  (* Words *)
  Definition t_world (w : W)  :uexp :=  CON (oo_world  w) .
  (** Tensor *)
  Definition t_tensor (A B :uexp) :uexp  :=  (APP (APP (CON oo_tensor) A) B).

  (** Implication *)
  Definition t_impl (A B :uexp) :uexp  :=  (APP (APP (CON oo_impl) A) B).

  (* Universal quantifier *)
  Definition t_all (FX: uexp -> uexp) : uexp := (APP (CON oo_all) (lambda FX)).

  (* F at w *)
  Definition t_at (F : uexp) (wexp : uexp) :uexp := (APP (APP (CON oo_at) F) wexp).

  (* F arrow v -- binder *)
  Definition t_arrow (FX : uexp -> uexp) : uexp := (APP (CON oo_arrow) (lambda FX)).

  (* ! F  *)
  Definition t_bang (A : uexp) : uexp := (APP (CON oo_bang) A).

  (* monoidal operations on worlds *)
  Definition t_wop (wexp wexp': uexp) : uexp := (APP (APP (CON oo_wop) wexp) wexp').
  
  (* F @ w *)
  Definition t_atW  (F: uexp) (wexp  :uexp) : uexp  :=  (APP (APP (CON oo_atW) F) wexp).

  Notation "F @ w" := (t_atW F w) (at level 10) .
  Notation "F *** G" := (t_tensor F G) (at level 10) .
  Notation "F --o G" := (t_impl F G) (at level 10) .
  Notation "'ALL' FX" := (t_all FX) (at level 10) .
  Notation "F 'AT' u" := (t_at F u) (at level 10) .
  Notation " !! F" := (t_bang F) (at level 10) .
  Notation "'ARROW' FW " := (t_arrow FW) (at level 10) .
  Notation "w 'wop' v" := (t_wop w v) (at level 10) .

  (** *** Well-formedness conditions *)

  (** For terms *)
  Inductive isOLTerm : uexp -> Prop :=
  | isOLTermT  : forall t, isOLTerm (t_term  t).

  (** For atoms *)
  Inductive isOLAtom : uexp -> Prop :=
  | isOLAtom' : forall id t ,  isOLTerm t -> isOLAtom (t_atom id t).

  (** For world expression *)
  Inductive isWorldExp : uexp -> Prop :=
  | isWorldExp' : forall w, isWorldExp (t_world w)
  | isWorldExp'' : forall wexp wexp', isWorldExp wexp -> isWorldExp wexp' -> isWorldExp (t_wop wexp wexp')
  .

  (** Formulas *)
  Inductive isOLFormula' : uexp -> Prop :=
  | isFAtom : forall t id , isOLTerm t -> isOLFormula' (t_atom id t)
  | isFTensor : forall A B , isOLFormula' A -> isOLFormula' B -> isOLFormula' (A *** B)
  | isFImpl : forall A B , isOLFormula' A -> isOLFormula' B -> isOLFormula' (A --o B)
  | isBang : forall A, isOLFormula' A -> isOLFormula' ( !! A)
  | isFAt : forall F wexp, isOLFormula' F -> isWorldExp wexp -> isOLFormula' (F AT wexp)
  | isFArrow : forall (FW: uexp -> uexp),
      uniform FW -> (forall (t:uexp), proper t -> isWorldExp t ->  isOLFormula' (FW t)) -> isOLFormula' (ARROW FW) 
  | isFQ : forall  (FX : uexp -> uexp),
      uniform FX -> (forall (t:uexp), proper t -> isOLFormula' (FX t)) ->
      isOLFormula' (ALL FX)
  .

  (** Well-formed judgments [F @ w] where [F] is a well-formed formula
  and [w] a well-formed world expression *)
  Inductive isOLFormula : uexp -> Prop :=
  | isOL : forall F wexp , isOLFormula' F -> isWorldExp wexp -> isOLFormula (F @ wexp)
  .
  
  (** Well formendness conditions for lists of formulas and list of judgments *)
  Definition isOLFormulaL  L : Prop := Forall isOLFormula L.

  Hint Constructors isOLTerm isOLAtom isWorldExp isOLFormula' isOLFormula : core.
  Hint Unfold isOLFormulaL : core.

  (** the predicate [ddown] is used to store the classical formulas of HyLL *)
  Inductive atm' : Set :=
  | up' : uexp -> atm'    (* formulas on the right *)
  | down' : uexp -> atm'  (* formulas on the left *)
  | ddown' : uexp -> atm'  (* formulas on the classical context (left) *)
  .

  (** Uniform Predicate for atoms *)
  Inductive uniform_atm' : (uexp -> atm') -> Prop :=
  | uniform_up: forall FX, uniform FX -> uniform_atm' (fun x:uexp => up' (FX x))
  | uniform_down: forall FX, uniform FX -> uniform_atm' (fun x:uexp => down' (FX x))
  | uniform_ddown: forall FX, uniform FX -> uniform_atm' (fun x:uexp => ddown' (FX x))
  .
  
  Hint Constructors uniform_atm' : core.

  Global Instance OLSyntaxIns : OLSig :=
    {|
      atm := atm';
      con := Econ ;
      uniform_atm := uniform_atm'
    |}.

  Definition up : uexp -> atm := up'.
  Definition down : uexp -> atm := down'.
  Definition ddown : uexp -> atm := ddown'.

  (** *** Inference rules *)
  (** Inductive definition of HyLL sequents. This definition will be
  used later (in HyLL and HyLLCut) to prove that the encodings are
  sound and complete *)

  Inductive HyLL : (list uexp) -> (list uexp) -> uexp -> Prop :=
  | hy_init : forall Gamma F, HyLL Gamma [ F]  F
  | hy_tenL : forall Gamma A B w L G, HyLL Gamma ( A @ w :: B @ w :: L) G -> HyLL Gamma ( (A *** B) @ w :: L) G
  | hy_tenR : forall Gamma A B w L L' , HyLL Gamma L (A @ w) ->  HyLL Gamma L' (B @ w) -> HyLL Gamma (L ++ L') ( (A *** B)  @ w)
  | hy_impL : forall Gamma A B w L L' G, HyLL Gamma L (A @ w) -> HyLL Gamma ( B @ w :: L') G -> HyLL Gamma ( (A --o B) @ w :: (L ++ L')) G
  | hy_impR : forall Gamma A B w L,  HyLL Gamma ((A @ w)::L) (B @ w) -> HyLL Gamma L ( (A --o B)  @ w)
  | hy_atL   : forall Gamma A v w L G , HyLL Gamma ( A @ v :: L)  G -> HyLL Gamma ( (A AT v) @ w :: L) G
  | hy_atR   : forall Gamma A v w L , HyLL Gamma L (A @ v) -> HyLL Gamma L ( (A AT v) @ w)
  | hy_arrowL : forall Gamma FW w L G, uniform FW -> isWorldExp w ->   HyLL Gamma (( ( FW w) @ w) :: L) G -> HyLL Gamma ( ( (ARROW FW) @ w) :: L) G
  | hy_arrowR : forall Gamma FW w L , uniform FW -> isWorldExp w ->   HyLL Gamma L ( ( FW w) @ w)   -> HyLL Gamma L ( (ARROW FW) @ w)
  | hy_bangL : forall Gamma F w L G, HyLL ( (F @ w) :: Gamma) L G -> HyLL Gamma (  ( (!! F) @ w) :: L ) G
  | hy_bangR : forall Gamma F w , HyLL Gamma [] ( F @ w) -> HyLL Gamma [] ( (!! F) @ w)
  | hy_copy : forall Gamma F w L G, In (F @ w) Gamma -> HyLL Gamma ((F @ w) :: L) G -> HyLL Gamma L G 
  | hy_allL : forall Gamma FX t w L G, uniform FX -> proper t -> HyLL Gamma ( (FX t) @ w ::L) G -> HyLL Gamma ( (ALL FX) @ w ::L) G
  | hy_allR : forall Gamma FX w L , uniform FX -> (forall t, proper t -> HyLL Gamma L ( (FX t) @ w)) ->
                                    HyLL Gamma L ( (ALL FX) @ w)
  | hy_exange : forall Gamma L L' G, Permutation L L' -> HyLL Gamma L' G -> HyLL Gamma  L G
  .

  Hint Constructors HyLL : core .

  (** Well formed conditions *)
  Lemma isWorldProper: forall w, isWorldExp w -> proper w.
  Proof with repeat constructor;auto.
    intros.
    induction H...
  Qed.

  Lemma isOLFormulaProper' : forall F, isOLFormula' F -> proper F.
  Proof with repeat constructor;auto.
    intros.
    induction H;solveF;try solve [auto;repeat constructor;auto].
    inversion H ...
    eauto with hybrid...
    apply isWorldProper in H0...
    constructor; eauto with hybrid.
    constructor; eauto with hybrid.
  Qed.
  
  Lemma isOLFormulaProper : forall F, isOLFormula F -> proper F.
  Proof with repeat constructor;auto.
    intros.
    induction H.
    apply isOLFormulaProper' in H.
    apply isWorldProper in H0...
  Qed.

  (** Measure of formulas (needed in the proof of cut-coherence and cut-elimination *)
  (* Worlds does not count in the complexity *)
  Inductive lengthUexp : uexp -> nat -> Prop :=
  | l_Var : forall (v:var), lengthUexp (Var v) 0
  | l_t_term : forall t, lengthUexp (t_term t) 0
  | l_t_world : forall w, lengthUexp (t_world w) 0
  | l_t_atomU : forall (id:nat) (A:uexp), lengthUexp (t_atom id A) 1
  | l_t_tensor: forall A B n1 n2, lengthUexp A n1 -> lengthUexp B n2 -> lengthUexp (A *** B) (S (n1 + n2))
  | l_t_impl: forall A B n1 n2, lengthUexp A n1 -> lengthUexp B n2 -> lengthUexp (A --o B) (S (n1 + n2))
  | l_t_bang: forall A  n1 , lengthUexp A n1  -> lengthUexp (!! A) (S n1)
  | l_t_at: forall A w n1, lengthUexp A n1 ->  lengthUexp (A AT w) (S n1)
  | l_t_arrow: forall FX n1, uniform FX -> lengthUexp(FX (t_world ID)) n1 -> lengthUexp (ARROW FX) (S n1)
  | l_t_all: forall FX n1, uniform FX -> lengthUexp(FX (Var 0)) n1 -> lengthUexp (ALL FX) (S n1)
  | l_t_atW : forall A w n1, lengthUexp A n1 -> lengthUexp (A @ w) n1 
  .
  
  (** Some results regarding the length of formulas *)

  Lemma LengthTerm : forall F, isOLTerm F -> lengthUexp F 0.
    intros.
    inversion H;subst;clear H;constructor.
  Qed.

  Lemma LengthFormula' : forall F n, isOLFormula' F -> lengthUexp F n -> n > 0.
    intros.
    induction H;simpl; try solve[inversion H0;lia].
  Qed.

  Lemma LengthFormula : forall F n, isOLFormula F -> lengthUexp F n -> n > 0.
    intros.
    inversion H;subst.
    inversion H0;subst.
    eapply LengthFormula' in H1;eauto.
  Qed.
  
  Lemma lengthAtom : forall id t, isOLFormula (t_atom id t)  -> lengthUexp (t_atom id t) 1.
    intros;inversion H;subst;simpl.
  Qed.

  (** [lengthUexp] is indeed a function *)
  Hint Constructors isOLFormula : core.
  Hint Resolve isWorldProper isOLFormulaProper' isOLFormulaProper:core.
  Lemma lengthFunction' : forall n F ,  lengthUexp F n -> isOLFormula' F -> forall n', lengthUexp F n' -> n = n'.
  Proof with auto;subst;try lia.
    induction 1;intros;try solve[inversion H0;subst;try lia].
    + inversion H1...
      inversion H2...
    + inversion H1...
      inversion H2...
    + inversion H1...
      inversion H0...
    + inversion H1...
      inversion H0...
    + inversion H1...
      inversion H2...
      apply lbindEq in H3...
      apply lbindEq in H6...
      apply eq_S.
      apply IHlengthUexp...
      rewrite <- H3...
      rewrite <- H6...
    + inversion H1...
      inversion H2...
      apply lbindEq in H3...
      apply lbindEq in H6...
      apply eq_S.
      apply IHlengthUexp...
      rewrite <- H3;eauto using proper_VAR.
      rewrite <- H6;eauto using proper_VAR.
  Qed.

End HyLL.
