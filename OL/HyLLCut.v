(* An alternative encoding of HyLL. Here we do not have adequacy at the level of derivations but we can prove a meta-theorem showing that non-legal application are "useless" *)

Require Export FLL.Misc.Hybrid.
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

Section Syntax.
  Variable W : Set. (* Set of Worlds *)
  Variable ID : W.
  Variable T : Set. (* Terms of the object logic *)

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

  (** Notation for Syntax *)
  Definition uexp : Set := expr Econ.
  Definition Var : var -> uexp := (VAR Econ).
  Definition Bnd : bnd -> uexp := (BND Econ).

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

  (* Hint Unfold  t_term t_atom t_world t_tensor t_impl t_all t_arrow t_bang t_wop t_at  t_atW : core. *)

  Notation "F @ w" := (t_atW F w) (at level 10) .
  Notation "F *** G" := (t_tensor F G) (at level 10) .
  Notation "F --o G" := (t_impl F G) (at level 10) .
  Notation "'ALL' FX" := (t_all FX) (at level 10) .
  Notation "F 'AT' u" := (t_at F u) (at level 10) .
  Notation " !! F" := (t_bang F) (at level 10) .
  Notation "'ARROW' FW " := (t_arrow FW) (at level 10) .
  Notation "w 'wop' v" := (t_wop w v) (at level 10) .

  (** *** Well-formedness conditions *)
  Inductive isOLTerm : uexp -> Prop :=
  | isOLTermT  : forall t, isOLTerm (t_term  t).

  Inductive isOLAtom : uexp -> Prop :=
  | isOLAtom' : forall id t ,  isOLTerm t -> isOLAtom (t_atom id t).

  Inductive isWorldExp : uexp -> Prop :=
  | isWorldExp' : forall w, isWorldExp (t_world w)
  | isWorldExp'' : forall wexp wexp', isWorldExp wexp -> isWorldExp wexp' -> isWorldExp (t_wop wexp wexp')
  .
  
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

  

  Inductive isOLFormula : uexp -> Prop :=
  | isOL : forall F wexp , isOLFormula' F -> isWorldExp wexp -> isOLFormula (F @ wexp)
  .
  
  (** Well formendness conditions for lists of formulas and list of judgments *)
  Definition isOLFormulaL  L : Prop := Forall isOLFormula L.

  Hint Constructors isOLTerm isOLAtom isWorldExp isOLFormula' isOLFormula : core.
  Hint Unfold isOLFormulaL : core.
  
  Inductive atm' : Set :=
  | up : uexp -> atm'    (* formulas on the right *)
  | down : uexp -> atm'  (* formulas on the left *)
  | ddown : uexp -> atm'  (* formulas on the classical context (left) *)
  .

  (** Uniform Predicate for atoms *)
  Inductive uniform_atm' : (uexp -> atm') -> Prop :=
  | uniform_up: forall FX, uniform FX -> uniform_atm' (fun x:uexp => up (FX x))
  | uniform_down: forall FX, uniform FX -> uniform_atm' (fun x:uexp => down (FX x))
  | uniform_ddown: forall FX, uniform FX -> uniform_atm' (fun x:uexp => ddown (FX x))
  .
  
  Hint Constructors uniform_atm' : core.

  Global Instance OLSyntaxIns : OLSig :=
    {|
      atm := atm';
      con := Econ ;
      uniform_atm := uniform_atm'
    |}.

  Notation "'u|' A '|'" := (atom (up A)) (at level 10) .
  Notation "'d|' A '|'" := (atom (down A)) (at level 10) .
  Notation "'dd|' A '|'" := (atom (ddown A)) (at level 10) .
  Notation "'u^|' A '|'" := (perp (up A)) (at level 10) .
  Notation "'d^|' A '|'" := (perp (down A)) (at level 10) .
  Notation "'dd^|' A '|'" := (perp (ddown A)) (at level 10) .

  Inductive HyLL : (list uexp) -> (list uexp) -> uexp -> Prop :=
  | hy_init : forall Gamma F, HyLL Gamma [ F]  F
  | hy_tenL : forall Gamma A B w L G, HyLL Gamma ( A @ w :: B @ w :: L) G -> HyLL Gamma ( (A *** B) @ w :: L) G
  | hy_tenR : forall Gamma A B w L L' , HyLL Gamma L (A @ w) ->  HyLL Gamma L' (B @ w) -> HyLL Gamma (L ++ L') ( (A *** B)  @ w)
  | hy_impL : forall Gamma A B w L L' G, HyLL Gamma L (A @ w) -> HyLL Gamma ( B @ w :: L') G -> HyLL Gamma ( (A --o B) @ w :: (L ++ L')) G
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

  Hint Resolve isWorldProper isOLFormulaProper' isOLFormulaProper.

  Example HyLL1: forall (a:T) (w:uexp) (t:T) id ,
      isWorldExp w ->
      HyLL [] [(ALL (fun x => t_atom id x)) @ w] ( (t_atom id (t_term t)) @ w).
  Proof with solveF.
    intros.
    apply hy_allL with (t:= t_term t)...
    constructor.
  Qed.

  Example HyLL2: forall (a:T) (w:uexp)  id , isWorldExp w -> HyLL [] [(ALL (fun x => t_atom id x)) @ w] ((ALL (fun x => t_atom id x)) @ w).
  Proof with solveF.
    intros.
    eapply  hy_allR...
    intros.
    apply hy_allL with (t:= t)...
  Qed.

  Example HyLL3: forall (F:uexp) (wexp:uexp)  , isWorldExp wexp -> isOLFormula' F ->  HyLL[] [ (ARROW (fun x => (F AT x))) @ wexp ] ((ARROW (fun x => (F AT x))) @ wexp) .
  Proof with solveF.
    intros.
    eapply hy_arrowR...
    eapply hy_atR...
    eapply hy_arrowL...
  Qed.

  Example HyLL4: forall (F:uexp) (w:uexp)  , isWorldExp w -> isOLFormula' F ->  HyLL [] [ (ARROW (fun x => (F AT (x wop w)))) @ w ] (F @ (w wop w)) .
  Proof with solveF.
    intros.
    eapply hy_arrowL...
  Qed.
  
  Definition RINIT (F:uexp) (w:uexp) : oo := u^|F @ w|  ** ( d^|F @ w| ) .
  Definition RTENSORL (F G w :uexp) :oo := d^| (F *** G) @ w| ** (d|F @ w| $ d|G @ w|).
  Definition RTENSORR (F G w :uexp) :oo := u^| (F *** G) @ w| ** (u|F @ w| ** u|G @ w|).
  Definition RIMPLL (F G w : uexp) : oo := d^| (F --o G) @ w | ** ( u|F @ w| ** d|G @ w|).
  Definition RIMPLR (F G w : uexp) : oo := u^| (F --o G) @ w | ** ( d|F @ w| $ u|G @ w|) .
  Definition RATL (F v w : uexp) := d^|(F AT v) @ w| ** d| F @ v| .
  Definition RATR (F v w : uexp) := u^|(F AT v) @ w| ** u| F @ v|.
  Definition RARROWL FW w := d^| (ARROW FW) @ w| ** d| (FW w) @ w|.
  Definition RARROWR FW w := u^| (ARROW FW) @ w| ** u| (FW w) @ w|.
  Definition RBANGL F w := d^| (!! F) @ w| ** ? d|F @ w|.
  Definition RBANGR F w := u^| (!! F) @ w| ** ! u|F @ w|.
  Definition RCOPY F w :=  d^| F @ w| ** d| F @ w| . 
  Definition RALLL FX w := d^|(ALL FX) @ w| ** E{ fun x => d|(FX x) @ w|} .
  Definition RALLR FX w := u^|(ALL FX) @ w| ** F{ fun x => u|(FX x) @ w|}.

  Hint Unfold RINIT RTENSORL RTENSORR RIMPLL RIMPLR RATL RATR RARROWL RARROWR RBANGL RBANGR RCOPY  RALLL RALLR : core.
  
  Inductive OLTheory  : oo ->  Prop :=
  | ll_init : forall F w, isOLFormula (F @ w) -> OLTheory(RINIT  F w)
  | ll_tenL : forall F G w , isOLFormula ((F *** G) @ w)  -> OLTheory (RTENSORL F G w)
  | ll_tenR : forall F G w, isOLFormula ((F *** G) @ w) -> OLTheory (RTENSORR F G w)
  | ll_implL : forall F G w , isOLFormula ( (F --o G) @ w) -> OLTheory(RIMPLL F G w )
  | ll_implR : forall F G w, isOLFormula ((F --o G) @ w) -> OLTheory (RIMPLR F G w)
  | ll_atL : forall F v w , isOLFormula ((F AT v) @ w) -> OLTheory(RATL F v w )
  | ll_atR : forall F v w , isOLFormula ((F AT v) @ w) -> OLTheory( RATR F v w)
  | ll_arrowL : forall FW  w , uniform FW -> isOLFormula ( (ARROW FW) @ w) -> OLTheory( RARROWL FW w)
  | ll_arrowR : forall FW  w , uniform FW -> isOLFormula ( (ARROW FW) @ w) -> OLTheory( RARROWR FW w)
  | ll_bangL : forall F w, isOLFormula ( (!! F) @ w) -> OLTheory (RBANGL F w)
  | ll_bangR : forall F w, isOLFormula ( (!! F) @ w) -> OLTheory (RBANGR F w)
  | ll_copy : forall F w, isOLFormula (F @ w) -> OLTheory (RCOPY F w)
  | ll_allL : forall FX w, uniform FX ->  isOLFormula ((ALL FX) @ w) -> OLTheory(RALLL FX w)
  | ll_allR : forall FX w, uniform FX -> isOLFormula ((ALL FX) @ w) -> OLTheory(RALLR FX w)
  .

  Definition LEncode L := map (fun x => d| x|) L.
  (* Definition CLEncode L := map (fun x => dd| x|) L. (* classical encoding *) *)
  Definition REncode F := u| F|.
  

  Hint Constructors OLTheory: core.
  Hint Constructors isOLFormula : core.
  Hint Unfold LEncode REncode .


  (*********************************)
  (* CUT ELIMINATIOn *)
  (*********************************)
  Definition RCUT (F:uexp) (w:uexp) : oo := d|F @ w|  ** ( u|F @ w| ) .
  Hint Unfold RCUT .

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
  
  Inductive OLTheoryCut (n:nat) : oo -> Prop :=
  | oo_theory : forall OO, OLTheory OO ->  OLTheoryCut n OO
  | oothc_cutn : forall F w m, isOLFormula (F @ w) -> lengthUexp F m -> m <= n ->  OLTheoryCut n (RCUT F w)
  .

  Hint Constructors OLTheoryCut : core.

  (** atoms of the form [down A] *)
  Inductive IsPositiveLAtomFormula : oo -> Prop :=
  | IsFPAL_dw : forall A w , isOLFormula (A @ w) -> IsPositiveLAtomFormula (d| A @ w|)
  .
  Hint Constructors IsPositiveLAtomFormula : core .

  
  Definition IsPositiveLAtomFormulaL L : Prop := Forall IsPositiveLAtomFormula L.
  Hint Unfold IsPositiveLAtomFormulaL : core. 

  
  
  (* For each rule, BUT copy, prove the self duality of the bodies of the rules *)

  Theorem CutCoherenceTensor F G w n m:
    lengthUexp F n ->
    lengthUexp G m ->
    isOLFormula' F ->
    isOLFormula' G ->
    isWorldExp w ->
    seq (OLTheoryCut (max n m)) [] [] (> [dual (d|F @ w| $ d|G @ w|); dual (u|F @ w| ** u|G @ w|)]).
  Proof with solveF.
    intros;simpl.
    solveLL'.
    (* With cut we can change up^ to down *)
    decide3' (RCUT F w)...
    apply oothc_cutn with (m:=n)...
    tensor' [d^| F @ w | ** d^| G @ w |; u^| G @ w |] [u^| F @ w |].

    decide3' (RCUT G w)...
    apply oothc_cutn with (m:=m)...
    tensor' [d^| F @ w | ** d^| G @ w |; d| F @ w |] [u^| G @ w |].

    decide1' (d^| F @ w | ** d^| G @ w |).
    tensor' [d| F @ w | ][ d| G @ w |].
  Qed.


  Definition CutDefinition n' h :=
    forall m : nat,
      m <= h ->
      forall h2 h1 : nat,
        m = h1 + h2 ->
        forall n : nat,
          n' <= n ->
          forall FCut : uexp,
            lengthUexp FCut n' ->
            forall G w : uexp,
              isOLFormula (FCut @ w) ->
              forall v : uexp,
                isOLFormula (G @ v) ->
                forall Delta2 : list uexp,
                  isOLFormulaL Delta2 ->
                  forall Delta1 : list uexp,
                    isOLFormulaL Delta1 ->
                    forall Gamma : list uexp,
                      seqN OLTheory h1 (LEncode Gamma) (REncode (G @ v) :: LEncode (FCut @ w :: Delta1)) (> []) ->
                      seqN OLTheory h2 (LEncode Gamma) (REncode (FCut @ w) :: LEncode Delta2) (> []) ->
                      isOLFormulaL Gamma ->
                      seq (OLTheoryCut (pred n)) (LEncode Gamma) (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)) (> []).

  Theorem NoUPinDOwn: forall F w L F1 w1 N,
      IsPositiveLAtomFormulaL L ->
      Permutation (u| F @ w | :: L) ([u| F1 @ w1 |] ++ N) ->
      F = F1 /\ w = w1 /\ Permutation L N.
  Proof.
    intros.
    symmetry in H0.
    apply PermutationInCons in H0 as H'.
    inversion H'.
    {
      inversion H1;subst;split;auto.
      symmetry in H0.
      apply Permutation_cons_inv in H0; auto.
    }
    
    apply in_split in H1.
    do 2 destruct H1.
    rewrite H1 in H.
    apply ForallAppInv2 in H.
    
    inversion H;subst;auto.
    inversion H4.
    
  Qed.
  Hint Unfold IsPositiveLAtomFormulaL : core.
  Hint Constructors IsPositiveLAtomFormula : core.
  Theorem LEncodePositiveAtom: forall L, 
      isOLFormulaL L ->  IsPositiveLAtomFormulaL (LEncode L).
  Proof with solveF.
    intros.
    induction L...
    inversion H...
    inversion H2...
    constructor;auto.
    apply IHL in H3...
  Qed.

  Theorem NoUPinDOwn': forall F w L F1 w1 N,
      isOLFormulaL L ->
      Permutation (u| F @ w | :: LEncode L) ([u| F1 @ w1 |] ++ N) ->
      F = F1 /\ w = w1 /\ Permutation (LEncode L) N.
  Proof.
    intros.
    apply NoUPinDOwn in H0;auto.
    apply LEncodePositiveAtom;auto.
  Qed.
  
  Theorem NoUPInPositiveLAtom: forall F w L,
      IsPositiveLAtomFormulaL L ->
      ~ In (u| F @ w |) L.
  Proof with solveF.    
    intros.
    intro HNeg.
    induction L;simpl in*;auto.
    destruct HNeg...
    
    inversion H...
    inversion H2.
    
    apply IHL;auto.
    inversion H... 
  Qed.

  Theorem NoUPInPositiveLAtom': forall F w L,
      ~ In (u| F @ w |) (LEncode L).
  Proof with solveF.    
    intros.
    intro HNeg.
    induction L;simpl in*;auto.
    destruct HNeg...
  Qed.

  Theorem FocusinRightAtom: forall n Gamma F w L F1 w0 G,
      isOLFormulaL Gamma ->
      isOLFormulaL L ->
      seqN OLTheory n (LEncode Gamma) (REncode (F @ w) :: LEncode L) (>> u^| F1 @ w0 | ** G) ->
      exists n', n = (S n') /\
                 seqN OLTheory n' (LEncode Gamma) (LEncode L) (>> G) /\
                 F = F1 /\ w = w0.
  Proof.               
    intros.
    InvTriAll.
    * apply NoUPinDOwn' in H4;auto.
      CleanContext.
      eexists;split;eauto.
      split;eauto.
      rewrite H4;auto.
    * (* Cannot be taken from Gamma *)
      apply NoUPInPositiveLAtom in H3. contradiction.
      apply LEncodePositiveAtom;auto.
  Qed.

  Theorem FocusinLeftAtom: forall n Gamma F w L F1 w0 G,
      seqN OLTheory n (LEncode Gamma) (REncode (F @ w) :: LEncode L) (>> d^| F1 @ w0 | ** G) ->
      exists n', n = (S n') /\
                 ( (exists L',
                       Permutation L  (F1 @ w0 :: L') /\
                       seqN OLTheory n' (LEncode Gamma) (REncode (F @ w) :: LEncode L') (>> G)
                   ) \/
                   ( In (F1 @ w0) Gamma /\
                     seqN OLTheory n' (LEncode Gamma) (REncode (F @ w) :: LEncode L) (>> G)))
  .
    

    intros.
    InvTriAll.
    { (* from the linear context *)
      simpl in H2.
      apply PermutationNeqIn in H2 as H2';[| intro HNeg;inversion HNeg].
      CleanContext.
      rewrite H0 in H2.
      rewrite perm_swap in H2.
      apply Permutation_cons_inv in H2.
      exists n0.
      split;auto.
      left.
      apply Permutation_sym in H2.
      apply Permutation_map_inv in H2.
      CleanContext.
      destruct x0. inversion H1.
      inversion H1;subst;auto.
      eexists.
      split;eauto.
      rewrite H0 in H7;auto.
    }
    { (* from the classical context *)
      eexists;split;eauto.
      right.
      split...
      apply in_map_iff in H1.
      CleanContext.
      inversion H0;subst;auto.
      rewrite <- H2 in H7.
      LLExact H7.
    }
  Qed.
  
  Theorem TheoryInclusion: forall F n , OLTheory F -> OLTheoryCut n F.
    intros.
    inversion H;subst;auto.
  Qed.


  (*********************)
  (* INVERSION LEMMA *)
  (*******************)

  Theorem RINITInv:  forall n Gamma F w L F1 w0,
      isOLFormulaL  Gamma ->
      isOLFormulaL  L ->
      seqN OLTheory n (LEncode Gamma) (REncode (F @ w) :: LEncode L) (>> RINIT F1 w0) ->
      (F = F1 /\ w = w0 /\ ( L = [ F1 @ w0]  \/ ( L = [] /\ In (F1 @ w ) Gamma))).
  Proof with solveF.
    intros.
    eapply FocusinRightAtom in H1...
    CleanContext.
    do 2 split;auto.
    inversion H2...
    + destruct L;simpl in H5;
        inversion H5.
      rewrite <- H4 in H5.
      inversion H5...
      assert (L=[]).
      eapply map_eq_nil. symmetry in H4;eauto.
      subst.
      left...
    + assert (L=[]).
      eapply map_eq_nil. symmetry in H1;eauto.
      subst;right.
      split...
      apply in_map_iff in H6.
      CleanContext.
      inversion H3...
  Qed.

  (* Inversion of the body of Tensor *)
  Theorem RInvPar: forall Th Gamma  Delta F G n,
      seqN Th n Gamma Delta (>> (atom F) $ (atom G)) ->
      exists n', n = S ( S ( S (S n'))) /\
                 seqN Th n' Gamma (Delta ++ [atom F ; atom G]) (> []).
    intros.
    InvTriAll.
    eexists;split;eauto.
    LLExact H8.
  Qed.
  

  
  Theorem CutElimStep:
    forall h1 h2 n n' Gamma Delta1 Delta2 G v w  Fcut,
      (seqN OLTheory h1 (LEncode Gamma) ( (REncode   (G @ v)) ::  LEncode( (Fcut @ w) :: Delta1)) (> []) ->
       (seqN OLTheory h2 (LEncode Gamma) ( (REncode (Fcut @ w)) :: LEncode Delta2)  (> [])) ->
       isOLFormulaL Gamma ->
       isOLFormulaL Delta1 ->
       isOLFormulaL Delta2->
       isOLFormula (Fcut @ w) ->
       isOLFormula (G @ v) ->
       lengthUexp Fcut n' ->
       n' <= n ->
       (seq (OLTheoryCut (pred n)) (LEncode Gamma) ( (REncode  (G @ v)) :: LEncode (Delta1 ++ Delta2))  (> []))).
  Proof with solveF. (* This was proved with CutTacPOS... see OLCutPos. *)
    intros h1 h2 n n' Gamma Delta1 Delta2 G v w FCut Hseq1 Hseq2.
    intros HIsGamma HIsDelta1 HIsDelta2 HIsFcut HIsG HLeng Hnn'.
    remember (plus h1 h2) as h.
    generalize dependent Gamma.
    generalize dependent Delta1.
    generalize dependent Delta2.
    generalize dependent v.
    generalize dependent w.
    generalize dependent G.
    generalize dependent FCut.
    generalize dependent n.
    generalize dependent h1.
    generalize dependent h2.
    
    induction h using strongind;intros.

    assert (h1 = 0) by lia...
    inversion Hseq1.
    assert(IH : CutDefinition n' h) by auto. clear H.
    

    (* Let's analyze Hseq1 -- the left premise in the cut rule *)
    inversion Hseq1...

    admit. (* cannot be from the linear context *)
    admit. (* cannot be from the classical context *)

    (* Now HSeq2 -- the right premise *)
    inversion Hseq2 ...
    admit. (* cannot be from the linear context *)
    admit. (* cannot be from the classical context *)

    (* By case analysis on the rules applied in each case *)
    inversion H;solveF;inversion H2;solveF.
    { (* case INIT INIT *)

      (* Using the invertibility lemmas to deduce the consequences of applying the rule *)
      apply RINITInv in H1...
      apply RINITInv in H4...
      CleanContext.
      (* By cases on where the formula was taken *)
      destruct H4;destruct H7;simpl...
      + (* linear context *)
        inversion H1...
        decide3' (RINIT F1 w0)...
        tensor' [REncode (F1 @ w0)][ d| F1 @ w0 |].
      + (* classical context *)
        inversion H1...
        decide3' (RINIT F1 w0)...
        tensor' [REncode (F1 @ w0)] (@nil oo).
        apply in_map_iff.
        eexists;eauto.
    } 
    { (* INIT TensorLeft *)
      (* Tensor Left cannot be principal *)
      eapply FocusinLeftAtom in H4 as H4'...
      CleanContext.
      destruct H3;CleanContext...
      + (* from the linear context *)
        
        apply RInvPar in H3. (* inversion on the fact that the (body) of the tensor rule was used *)
        CleanContext.
        simpl in H7.
        
        (* The inductive hypothesis can be used on H7 _ Hseq1 *)
        
        assert (HCut:seq (OLTheoryCut (pred n)) (LEncode Gamma) (REncode (G @ v) :: LEncode (Delta1 ++ x0 ++ [F @ w1 ; G0 @ w1])) (> [])).
        apply IH with (h1:= S n0) (h2:= x1) (m:= S n0 + x1) (FCut:= FCut) (w:=w)...
        admit.
        unfold LEncode.
        rewrite map_app...
        clear H7.

        eapply Permutation_map in H0.
        unfold LEncode.
        rewrite map_app...
        rewrite H0.
        simpl.
        (* apply the rule *)
        decide3' ( RTENSORL F G0 w1).
        tensor'  [d| (F *** G0) @ w1 |] (REncode (G @ v) :: map (fun x : uexp => d| x |) Delta1 ++  map (fun x : uexp => d| x |) x0).
        assert(Heq:  (((map (fun x : uexp => d| x |) Delta1 ++ map (fun x : uexp => d| x |) x0) ++ [d| F @ w1 |]) ++ [d| G0 @ w1 |]) = LEncode ( (Delta1 ++ x0 ++ [F @ w1; G0 @ w1]))).
        unfold LEncode...
        repeat rewrite map_app.
        simpl.
        repeat rewrite app_assoc_reverse.
        reflexivity.
        rewrite Heq.
        LLExact' HCut.
      + (* from the classical context *)
        
        apply RInvPar in H3.
        CleanContext.
        simpl in H7.

        assert (HCut:seq (OLTheoryCut (pred n)) (LEncode Gamma) (REncode (G @ v) :: LEncode (Delta1  ++ (Delta2 ++ [F @ w1 ; G0 @ w1]))) (> [])).
        apply IH with (h1:= S n0) (h2:= x0) (m:= S n0 + x0) (FCut:= FCut) (w:=w)...
        admit.
        unfold LEncode.
        rewrite map_app...
        clear H7.

        decide3' ( RTENSORL F G0 w1).
        tensor' (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).

        eapply in_map in H0; exact H0.
        unfold LEncode.
        repeat rewrite map_app...
        unfold LEncode in HCut.
        repeat rewrite map_app in HCut.
        simpl in *.
        LLExact' HCut.
    }
    { (* INIT and tensor right *)
      (* RTENSORR is necessarily principal on the right *)
      apply FocusinRightAtom in H4 as H4'...
      CleanContext.
      

      (* Let's see what happen with RINIT on the left: it must necessarily be principal too *)
      apply RINITInv in H1...
      destruct H1...
      inversion H0...

      (* H3 is enough here (without induction) *)
      apply seqNtoSeq in H3.
      apply WeakTheory with (theory:= OLTheory).
      auto using TheoryInclusion.
      decide3' (RTENSORR F G0 w0).
      tensor' [REncode ((F *** G0) @ w0 )]  (LEncode Delta2).

    }
    
    
  Admitted.
    

  (********************* STOP ******************************)

  

  (** None legal applications of rules are OK *)

  Theorem NORightNotProvable : forall n Gamma  L ,
      isOLFormulaL Gamma -> 
      isOLFormulaL L ->  
      ~ seqN OLTheory n (LEncode Gamma)  (LEncode L) ( > [] ) .
 Proof with solveF.
    induction n using strongind;intros...
    * intro. inversion H1...
    * intro.
      inversion H2...
      + (* from Linear *)
        apply Remove_In in H5.
        apply in_map_iff in H5.
        destruct H5.
        destruct H3...
      + (* from Classical *)
        apply in_map_iff in H5.
        destruct H5.
        destruct H3...
      + (* from Theory *)
        inversion H4...
        -
        inversion H6...
        2:{ inversion H8. }
        
        symmetry in H9.
        apply Permutation_map_inv in H9.
        destruct H9.
        destruct H7...
        fold (LEncode x) in H7.
        symmetry in H7.
        apply map_eq_app in H7.
        destruct H7.
        destruct H7...
        fold (LEncode x0) in H13.
        fold (LEncode x1) in H14.
        
        inversion H13...
        symmetry in H11.
        apply map_eq_cons in H11.
        destruct H11.
        destruct H7...
        apply in_map_iff  in H12.
        destruct H12...
        - 
        inversion H6...
        2:{ inversion H8. }
        
        symmetry in H9.
        apply Permutation_map_inv in H9.
        destruct H9.
        destruct H7...
        fold (LEncode x) in H7.
        symmetry in H7.
        apply map_eq_app in H7.
        destruct H7.
        destruct H7...
        fold (LEncode x0) in H13.
        fold (LEncode x1) in H14.
        
        inversion H14...
        inversion H15... 
        inversion H16...
        inversion H19...
        
        clear H9.
        clear H14. 
        clear H15. 
        clear H16. 
        clear H18.
        clear H19.  
        clear H20.
        
        assert(Hc: ~ seqN OLTheory n0 (LEncode Gamma)
                  (LEncode (x1 ++ [F0 @ w] ++ [G @ w])) 
                   (> [])).
        apply H...          
        assert(isOLFormulaL (x0 ++ x1)).
        apply (Forall_Permute H1 H8).
        apply ForallApp...
        apply (ForallAppInv2 H7).
        inversion H3...
        inversion H11...
        
        apply Hc.

        assert(Hw:
        (LEncode (x1 ++ [F0 @ w; G @ w])) = 
        (LEncode x1 ++ LEncode [F0 @ w] ++ LEncode [G @ w])).
        
        apply map_app.
        simpl.
        rewrite Hw.
        rewrite app_assoc...
        -
        inversion H6...
        2:{ inversion H8. }
        
        symmetry in H9.
        apply Permutation_map_inv in H9.
        destruct H9.
        destruct H7...
        fold (LEncode x) in H7.
        symmetry in H7.
        apply map_eq_app in H7.
        destruct H7.
        destruct H7...
        fold (LEncode x0) in H13.
        fold (LEncode x1) in H14.
        
        inversion H13...
        symmetry in H11.
        apply map_eq_cons in H11.
        destruct H11.
        destruct H7...
        apply in_map_iff  in H12.
        destruct H12...
        -
        inversion H6...
        2:{ inversion H8. }
        
        symmetry in H9.
        apply Permutation_map_inv in H9.
        destruct H9.
        destruct H7...
        fold (LEncode x) in H7.
        symmetry in H7.
        apply map_eq_app in H7.
        destruct H7.
        destruct H7...
        fold (LEncode x0) in H13.
        fold (LEncode x1) in H14.
        
        inversion H14...
        inversion H17... 
        inversion H18...
        
        
        clear H9. 
        clear H14. 
        clear H17. 
        clear H18. 
        clear H20.
        
        symmetry in H10.
        apply Permutation_map_inv in H10.
        destruct H10.
        destruct H7...
        fold (LEncode x) in H7.
        symmetry in H7.
        apply map_eq_app in H7.
        destruct H7.
        destruct H7...
        fold (LEncode x2) in H16.
        fold (LEncode x3) in H21.
        
         
        assert(Hc: ~ seqN OLTheory n (LEncode Gamma)
                  (LEncode (x3 ++ [G @ w])) 
                   (> [])).
        apply H...          
        assert(isOLFormulaL (x0 ++ x1)).
        apply (Forall_Permute H1 H8).
        assert(isOLFormulaL x1).
        apply (ForallAppInv2 H7).
        
        assert(isOLFormulaL (x2 ++ x3)).
        
        apply (Forall_Permute H10 H9).
        
        apply ForallApp...
        apply (ForallAppInv2 H11).
        inversion H3...
        inversion H15...
        
        apply Hc.

        assert(Hw:
        (LEncode (x3 ++ [G @ w])) = 
        (LEncode x3 ++ LEncode [G @ w])).
        
        apply map_app.
        simpl.
        rewrite Hw...
        -
        inversion H6...
        2:{ inversion H8. }
        
        symmetry in H9.
        apply Permutation_map_inv in H9.
        destruct H9.
        destruct H7...
        fold (LEncode x) in H7.
        symmetry in H7.
        apply map_eq_app in H7.
        destruct H7.
        destruct H7...
        fold (LEncode x0) in H13.
        fold (LEncode x1) in H14.
        
        inversion H13...
        symmetry in H11.
        apply map_eq_cons in H11.
        destruct H11.
        destruct H7...
        apply in_map_iff  in H12.
        destruct H12...
        -
        inversion H6...
        2:{ inversion H8. }
        
        symmetry in H9.
        apply Permutation_map_inv in H9.
        destruct H9.
        destruct H7...
        fold (LEncode x) in H7.
        symmetry in H7.
        apply map_eq_app in H7.
        destruct H7.
        destruct H7...
        fold (LEncode x0) in H13.
        fold (LEncode x1) in H14.
        
        inversion H14...
        inversion H15...
        
        clear H9. 
        clear H14. 
        clear H15. 
        clear H17. 
             
        assert(Hc: ~ seqN OLTheory n0 (LEncode Gamma)
                  (LEncode (x1 ++ [F0 @ v])) 
                   (> [])).
        apply H...          
        assert(isOLFormulaL (x0 ++ x1)).
        apply (Forall_Permute H1 H8).
        assert(isOLFormulaL x1).
        apply (ForallAppInv2 H7).
        
        apply ForallApp...
        inversion H3...
        inversion H12...
        
        apply Hc.

        assert(Hw:
        (LEncode (x1 ++ [F0 @ v])) = 
        (LEncode x1 ++ LEncode [F0 @ v])).
        
        apply map_app.
        simpl.
        rewrite Hw...
        -
        inversion H6...
        2:{ inversion H8. }
        
        symmetry in H9.
        apply Permutation_map_inv in H9.
        destruct H9.
        destruct H7...
        fold (LEncode x) in H7.
        symmetry in H7.
        apply map_eq_app in H7.
        destruct H7.
        destruct H7...
        fold (LEncode x0) in H13.
        fold (LEncode x1) in H14.
        
        inversion H13...
        symmetry in H11.
        apply map_eq_cons in H11.
        destruct H11.
        destruct H7...
        apply in_map_iff  in H12.
        destruct H12...
        -
        inversion H6...
        2:{ inversion H9. }
        
        symmetry in H10.
        apply Permutation_map_inv in H10.
        destruct H10.
        destruct H8...
        fold (LEncode x) in H8.
        symmetry in H8.
        apply map_eq_app in H8.
        destruct H8.
        destruct H8...
        fold (LEncode x0) in H14.
        fold (LEncode x1) in H15.
        
        inversion H15...
        inversion H16...
        
        clear H10. 
        clear H15. 
        clear H16. 
        clear H18.
        
             
        assert(Hc: ~ seqN OLTheory n0 (LEncode Gamma)
                  (LEncode (x1 ++ [(FW w) @ w])) 
                   (> [])).
        apply H...          
        assert(isOLFormulaL (x0 ++ x1)).
        apply (Forall_Permute H1 H9).
        assert(isOLFormulaL x1).
        apply (ForallAppInv2 H8).
        
        apply ForallApp...
        
        inversion H7...
        inversion H13...
        
        assert(proper w) by auto.
        specialize(H16 w H17) as Hf.
        
        apply lbindEq in H11...
        rewrite  H11 in Hf... 
        
        apply Hc.

        assert(Hw:
        (LEncode (x1 ++ [(FW w) @ w])) = 
        (LEncode x1 ++ LEncode [(FW w) @ w])).
        
        apply map_app.
        simpl.
        rewrite Hw...
        -
        inversion H6...
        2:{ inversion H9. }
        
        symmetry in H10.
        apply Permutation_map_inv in H10.
        destruct H10.
        destruct H8...
        fold (LEncode x) in H8.
        symmetry in H8.
        apply map_eq_app in H8.
        destruct H8.
        destruct H8...
        fold (LEncode x0) in H14.
        fold (LEncode x1) in H15.
        
        inversion H14...
        symmetry in H12.
        apply map_eq_cons in H12.
        destruct H12.
        destruct H8...
        apply in_map_iff in H13.
        destruct H13...        
        -
        inversion H6...
        2:{ inversion H8. }
        
        symmetry in H9.
        apply Permutation_map_inv in H9.
        destruct H9.
        destruct H7...
        fold (LEncode x) in H7.
        symmetry in H7.
        apply map_eq_app in H7.
        destruct H7.
        destruct H7...
        fold (LEncode x0) in H13.
        fold (LEncode x1) in H14.
        
        inversion H14...
        inversion H15...
        
        clear H9. 
        clear H14. 
        clear H15. 
             
        assert(Hc: ~ seqN OLTheory n0 (LEncode (Gamma  ++ [F0 @ w]))
                  (LEncode x1) 
                   (> [])).
        apply H...
        apply ForallApp...
       
        inversion H3...
        inversion H10...
                  
        assert(isOLFormulaL (x0 ++ x1)).
        apply (Forall_Permute H1 H8).
        apply (ForallAppInv2 H7).
        
        apply Hc.

        assert(Hw:
        (LEncode (Gamma ++ [F0 @ w])) = 
        (LEncode Gamma ++ LEncode [F0 @ w])).
        
        apply map_app.
        simpl.
        rewrite Hw...
        -
        inversion H6...
        2:{ inversion H8. }
        
        symmetry in H9.
        apply Permutation_map_inv in H9.
        destruct H9.
        destruct H7...
        fold (LEncode x) in H7.
        symmetry in H7.
        apply map_eq_app in H7.
        destruct H7.
        destruct H7...
        fold (LEncode x0) in H13.
        fold (LEncode x1) in H14.
        
        inversion H13...
        symmetry in H11.
        apply map_eq_cons in H11.
        destruct H11.
        destruct H7...
        apply in_map_iff  in H12.
        destruct H12...
        -
        inversion H6...
        2:{ inversion H8. }
        
        symmetry in H9.
        apply Permutation_map_inv in H9.
        destruct H9.
        destruct H7...
        fold (LEncode x) in H7.
        symmetry in H7.
        apply map_eq_app in H7.
        destruct H7.
        destruct H7...
        fold (LEncode x0) in H13.
        fold (LEncode x1) in H14.
        
        inversion H14...
        inversion H15...
        
        clear H9. 
        clear H14. 
        clear H15.
        clear H17. 
             
        assert(Hc: ~ seqN OLTheory n0 (LEncode Gamma)
                  (LEncode (x1++ [F0 @ w])) 
                   (> [])).
        apply H...
        apply ForallApp...
                  
        assert(isOLFormulaL (x0 ++ x1)).
        apply (Forall_Permute H1 H8).
        apply (ForallAppInv2 H7).
        
        apply Hc.

        assert(Hw:
        (LEncode (x1 ++ [F0 @ w])) = 
        (LEncode x1 ++ LEncode [F0 @ w])).
        
        apply map_app.
        simpl.
        rewrite Hw...
        - 
        inversion H6...
        2:{ inversion H9. }
        
        symmetry in H10.
        apply Permutation_map_inv in H10.
        destruct H10.
        destruct H8...
        fold (LEncode x) in H8.
        symmetry in H8.
        apply map_eq_app in H8.
        destruct H8.
        destruct H8...
        fold (LEncode x0) in H14.
        fold (LEncode x1) in H15.
        
        inversion H15...
        inversion H17...
        inversion H19...
        
        clear H12. 
        clear H15. 
        clear H17. 
        clear H21.
        
             
        assert(Hc: ~ seqN OLTheory n (LEncode Gamma)
                  (LEncode (x1 ++ [(FX t) @ w])) 
                   (> [])).
        apply H...          
        assert(isOLFormulaL (x0 ++ x1)).
        apply (Forall_Permute H1 H9).
        assert(isOLFormulaL x1).
        apply (ForallAppInv2 H8).
        
        apply ForallApp...
        
        inversion H7...
        inversion H16...
        
        specialize(H18 t H11) as Hf.
        
        apply lbindEq in H13...
        rewrite  H13 in Hf... 
        
        apply Hc.

        assert(Hw:
        (LEncode (x1 ++ [(FX t) @ w])) = 
        (LEncode x1 ++ LEncode [(FX t) @ w])).
        
        apply map_app.
        simpl.
        rewrite Hw...
        -
        inversion H6...
        2:{ inversion H9. }
        
        symmetry in H10.
        apply Permutation_map_inv in H10.
        destruct H10.
        destruct H8...
        fold (LEncode x) in H8.
        symmetry in H8.
        apply map_eq_app in H8.
        destruct H8.
        destruct H8...
        fold (LEncode x0) in H14.
        fold (LEncode x1) in H15.
        
        inversion H14...
        symmetry in H12.
        apply map_eq_cons in H12.
        destruct H12.
        destruct H8...
        apply in_map_iff in H13.
        destruct H13...
        Qed.
    

  Ltac IS :=
    try
      match goal with
      |  [H : isOLFormulaL (_ :: _) |- _] =>  inversion H; clear H;subst;try IS
      |  [H : isOLFormula _ |- _ ] => inversion H; clear H;subst;try IS
      | [H: isOLFormula' (_ _ _) |- _] => inversion H;clear H;subst;try IS
      | [H: isOLFormula' (_ _) |- _]=> inversion H;clear H;subst;try IS
      | [H: lbind _ _ = _ |- _ ] => apply lbindEq in H;auto;subst
      end.
  
  Theorem Soundeness: forall Gamma L F w , HyLL Gamma L (F @ w) ->
                                           isOLFormulaL Gamma ->
                                           isOLFormulaL L ->
                                           isOLFormula (F @ w) ->
                                           seq OLTheory (CLEncode Gamma) (REncode (F @ w) :: (LEncode L)) (> []).
  Proof with solveF;IS;solveF.
    intros.
    induction H...
    + (* init *)
      decide3' (RINIT F1 wexp).
      tensor' [REncode (F1 @ wexp)] [d| F1 @ wexp |].
    + decide3' (RTENSORL A B w0)...
      tensor' [d| (A *** B) @ w0 |] (REncode (F0 @ wexp) :: LEncode L).
       simpl in *.
       LLPerm  (REncode (F0 @ wexp) :: d| A @ w0 | :: d| B @ w0 | :: LEncode L).
       apply  IHHyLL...
       
    + (* tensor right *)
      admit.
    + (* implication left *)
      decide3' (RIMPLL A B w0 ((F0 @ wexp))).
      tensor' [d| (A --o B) @ w0 | ; REncode (F0 @ wexp)] (LEncode (L ++ L')).
      tensor' [d| (A --o B) @ w0 | ][ REncode (F0 @ wexp)].
      tensor' (LEncode L) (LEncode L').
      autounfold; rewrite map_app...
      LLPerm (REncode (A @ w0) :: LEncode L).
      apply IHHyLL1...
      admit. (* by H7 *)
      LLPerm (u| F0 @ wexp | :: d| B @ w0 | :: LEncode L') .
      apply IHHyLL2...
      constructor ...
      admit. (* by H7 *)
    + (* at  *)
      decide3' (RATL A v w0).
      tensor' [d| (A AT v) @ w0 |] (REncode (F0 @ wexp) :: LEncode L).
      simpl in IHHyLL.
      LLPerm (REncode (F0 @ wexp) :: d| A @ v | :: LEncode L).
      apply IHHyLL...
    + (* at *)
      admit.
    + (* arrow *)
      decide3' (RARROWL FW w0).
      (* automatize here *)
      apply ll_arrowL...
      constructor...
      apply isFArrow...
      intros.
      rewrite <- H2...
      (* ***** *)
      tensor' [d| (ARROW FW) @ w0 |] (REncode (F0 @ wexp) :: LEncode L).
      simpl in  IHHyLL.
      LLPerm (REncode (F0 @ wexp) :: d| (FW w0) @ w0 | :: LEncode L).
      apply IHHyLL...
      constructor...
      constructor...
      rewrite <- H2...
    + (* arrow *)
      admit.
    + (* bang *)
      decide3' (RBANGL F0 w0).
      tensor' [d| (!! F0) @ w0 |] (REncode (F1 @ wexp)  :: LEncode L).
      simpl in IHHyLL.
      LLPerm (dd| F0 @ w0 | :: CLEncode Gamma).
      apply IHHyLL...
    + (* bang *)
      admit.
    + (* copy *)
      decide3' (RCOPY F0 w0).
      constructor...
      admit. (* by H and H0*)
      tensor' (@nil oo)(REncode (F1 @ wexp) :: LEncode L) .
      admit. (* by H *)
      simpl in IHHyLL.
      LLPerm (REncode (F1 @ wexp) :: d| F0 @ w0 | :: LEncode L).
      apply IHHyLL...
      admit. (* byu H and H1 *)
    + (* quantifier *)
      decide3' (RALLL FX w0).
      constructor...
      constructor...
      constructor...
      intros. rewrite <- H2...
      tensor' [d| (ALL FX) @ w0| ] (REncode (F0 @ wexp)  :: LEncode L) .
      existential' t.
      simpl in IHHyLL.
      LLPerm (REncode (F0 @ wexp) :: d| (FX t) @ w0 | :: LEncode L).
      apply IHHyLL...
      constructor...
      rewrite <- H2...
      
    + decide3' (RALLR FX w0).
      constructor...
      constructor...
      constructor...
      intros. rewrite <- H2...
      tensor' [REncode ((ALL FX) @ w0) ]  (LEncode L).
      specialize(H4 x properX).
      LLPerm (REncode ((FX x) @ w0) :: LEncode L).
      apply H4...
      constructor...
      rewrite <- H2...
      
    + (* permutation *)
      admit.
  Admitted.

  (* For completeness, better to prove some "invertibility" lemmas *)

  Theorem NoUPInCLEncode: forall F w Gamma,
      ~ In (u| F @ w |) (CLEncode Gamma).
    intros.
    intro HNeg.
    induction Gamma;simpl in*;auto.
    destruct HNeg.
    inversion H.
    apply IHGamma;auto.
  Qed.

  Theorem NoDOWNInCLEncode: forall F w Gamma,
      ~ In (d| F @ w |) (CLEncode Gamma).
    intros.
    intro HNeg.
    induction Gamma;simpl in*;auto.
    destruct HNeg.
    inversion H.
    apply IHGamma;auto.
  Qed.
  
  Theorem NoUPInLEncode: forall F w Gamma,
      ~ In (u| F @ w |) (LEncode Gamma).
    intros.
    intro HNeg.
    induction Gamma;simpl in*;auto.
    destruct HNeg.
    inversion H.
    apply IHGamma;auto.
  Qed.

  Theorem NoUPinDOwn: forall F w L F1 w1 N,
      Permutation (u| F @ w | :: map (fun x : uexp => d| x |) L) ([u| F1 @ w1 |] ++ N) ->
      F = F1 /\ w = w1 /\ Permutation  (map (fun x : uexp => d| x |) L) N.
    intros.
    simpl in H.
    apply Permutation_sym in H.
    apply PermutationInCons in H as H'.
    inversion H'.
    inversion H0;subst;split;auto.
    split;auto.  
    apply Permutation_cons_inv in H.
    rewrite H;perm.
    apply NoUPInLEncode in H0;contradiction.
  Qed.
  
  Theorem FocusinRightAtom: forall n Gamma F w L F1 w0 G,
      seqN OLTheory n (CLEncode Gamma) (REncode (F @ w) :: LEncode L) (>> u^| F1 @ w0 | ** G) ->
      exists n', n = (S n') /\
                 seqN OLTheory n' (CLEncode Gamma) (LEncode L) (>> G) /\
                 F = F1 /\ w = w0.
    intros.
    InvTriAll.
    apply NoUPinDOwn in H2.
    CleanContext.
    eexists;split;eauto.
    rewrite H2;auto.
    (* Cannot be taken from Gamma *)
    apply NoUPInCLEncode in H1;contradiction.
  Qed.

    
    

   

    

  Theorem RATLInv:  forall n Gamma F  F1 w L v w0,
      seqN OLTheory n (CLEncode Gamma) (REncode (F @ w) :: LEncode L) (>> RATL F1 v w0) ->
      exists n',
        exists L',
          n = S (S (S n')) /\
        Permutation L  ((F1 AT v) @ w0 :: L') /\
        seqN OLTheory n' (CLEncode Gamma) (REncode (F @ w) ::   LEncode ((F1 @ v) :: L')) (> []) .
  Proof with solveF.
    intros.
    unfold RATL in H.
    apply FocusinLeftAtom in H .
    CleanContext.
    
    InvTriAll.
    eexists.
    eexists.
    split;eauto.
    split;eauto.
    simpl in *.
    LLExact H8.
    autounfold;perm.
  Qed.

  Theorem RARROWRInv: forall n Gamma F w L FW w0,
      seqN OLTheory n (CLEncode Gamma) (REncode (F @ w) :: LEncode L) (>> RARROWR FW w0) ->
      exists n',
        n = S ( S ( S n')) /\
        F = (ARROW FW) /\ w = w0 /\
        seqN OLTheory n' (CLEncode Gamma) (REncode ( (FW w) @ w) :: LEncode L) (> []) .
  Proof with solveF.
    intros.
    unfold RARROWR in H.
    apply FocusinRightAtom in H .
    CleanContext.
    InvTriAll.
    eexists;split; eauto.
    split; eauto.
    split; eauto.
    unfold REncode.
    LLPerm (map (fun x : uexp => d| x |) L ++ [u| (FW w0) @ w0 |])...
  Qed.
    
    

    
  
  Theorem Completeness: forall  n Gamma L F w , 
                                           isOLFormulaL Gamma ->
                                           isOLFormulaL L ->
                                           isOLFormula (F @ w) ->
                                           seqN  OLTheory n (CLEncode Gamma) (REncode (F @ w) :: (LEncode L)) (> []) ->
                                           HyLL Gamma L (F @ w).
  Proof with solveF.
    induction n using strongind;intros...
    inversion H2.
    
    inversion H3...
    admit. (* cannot be from the context *)
    admit. (* cannot be from the classical context *)
     
    inversion H5...
    + (* init *)
      apply RINITInv in H7.
      CleanContext...
    + (* tensor left *)
      admit.
    + (* tensor right *)
      admit.
    + (*  implication left *)
      admit.
    + (* implication right *)
      admit.
    + (* at left *)
      apply RATLInv in H7.
      CleanContext.
      apply hy_exange with (L':=  ((F1 AT v) @ w0 :: x0))...
      apply hy_atL.
      apply H in H8...
      admit.
    + (* at right *)
      admit.
    + (* arrow Left *)
      admit.
    + (* arrow right *)
      apply RARROWRInv in H7.
      CleanContext.
      inversion H8...
      inversion H9...
      apply lbindEq in H6...
      
      apply hy_arrowR;auto.
      apply H in H10...
      rewrite <- H6...
  Admitted.
      
      


      
