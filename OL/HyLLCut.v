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
  Definition RTENSORR (F G w :uexp) :oo := u^| (F *** G) @ w| ** (u|F @ w| ** d|G @ w|).
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

  (** None legal applications of rules are OK *)

  Theorem NORightisOK : forall n Gamma Gamma' L L' F w,
      isOLFormulaL Gamma -> isOLFormulaL Gamma' ->
      isOLFormulaL L ->  isOLFormulaL L' ->
      isOLFormula (F @ w) ->
      seqN OLTheory n (LEncode Gamma)  (LEncode L) ( > [] ) ->
      seqN OLTheory n (LEncode (Gamma ++ Gamma'))  (REncode (F @ w)  :: LEncode (L ++ L')) ( > [] ) .
  Admitted.
    

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

   Theorem FocusinLeftAtom: forall n Gamma F w L F1 w0 G,
      seqN OLTheory n (CLEncode Gamma) (REncode (F @ w) :: LEncode L) (>> d^| F1 @ w0 | ** G) ->
      exists n', n = (S n') /\
                 exists L',
                   Permutation L  (F1 @ w0 :: L') /\
                   seqN OLTheory n' (CLEncode Gamma) (REncode (F @ w) :: LEncode L') (>> G).

    intros.
    InvTriAll.

    { simpl in H2.
      apply PermutationNeqIn in H2 as H2'.
      CleanContext.
      rewrite H0 in H2.
      rewrite perm_swap in H2.
      apply Permutation_cons_inv in H2.
      eexists;auto.
      split;eauto.
      apply Permutation_sym in H2.
      apply Permutation_map_inv in H2.
      CleanContext.
      destruct x0. inversion H1.
      inversion H1;subst;auto.
      exists x0.
      split;auto.
      rewrite H0 in H7;auto.
      intro HNeg;inversion HNeg.
    }
    (* Cannot be taken from Gamma *)
    apply NoDOWNInCLEncode in H1;contradiction.
   Qed.
    
    

  Theorem RINITInv:  forall n Gamma F w L F1 w0, 
      seqN OLTheory n (CLEncode Gamma) (REncode (F @ w) :: LEncode L) (>> RINIT F1 w0) ->
      F = F1 /\ w = w0 /\ L = [ F1 @ w0 ].
  Proof with solveF.
    intros.
    unfold RINIT in H.
    apply FocusinRightAtom in H .
    CleanContext.
    InvTriAll.
    {
      apply map_eq_cons in H1.
      CleanContext.
      inversion H1;subst.
      apply map_eq_nil in H2;subst.
      firstorder.
    }
    
    (* Cannot be from the classical context *)
    apply NoDOWNInCLEncode in H2;contradiction.
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
      
      


      