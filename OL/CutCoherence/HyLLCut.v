(*  ** HyLL as an LL theory 

This file defines an alternative encoding for HyLL rules. Such
encoding is adequate at the level of proofs but it is cut-coherent *)

Require Export FLL.Misc.Hybrid.
Require Import Coq.Init.Nat.
Require Import FLL.SL.CutElimination.
Import FLL.Misc.Permutations.
Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Optimize Proof.
Optimize Heap.
 
Hint Constructors seq seqN : core .
Hint Constructors uniform_oo : core.
Hint Constructors isFormula : core.

Section HyLL.
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

  Hint Resolve isWorldProper isOLFormulaProper' isOLFormulaProper:core.

  Definition BODY_RTENSORL (F G w :uexp) :oo := (d|F @ w| $ d|G @ w|).
  Definition BODY_RTENSORR (F G w :uexp) :oo := (u|F @ w| ** u|G @ w|).
  Definition BODY_RIMPLL (F G w : uexp) : oo := (u|F @ w| ** d|G @ w|).
  Definition BODY_RIMPLR (F G w : uexp) : oo := (d|F @ w| $ u|G @ w|) .
  Definition BODY_RATL (F v : uexp) := d| F @ v| .
  Definition BODY_RATR (F v : uexp) := u| F @ v|.
  Definition BODY_RARROWL FW w :=  d| (FW w) @ w|.
  Definition BODY_RARROWR FW w := u| (FW w) @ w|.
  Definition BODY_RBANGL F w := ? d|F @ w|.
  Definition BODY_RBANGR F w := ! u|F @ w|.
  Definition BODY_RALLL FX w := E{ fun x => d|(FX x) @ w|} .
  Definition BODY_RALLR FX w := F{ fun x => u|(FX x) @ w|}.
  
  Hint Unfold BODY_RTENSORL 
              BODY_RTENSORR BODY_RIMPLL 
                            BODY_RIMPLR BODY_RATL 
                                        BODY_RATR BODY_RARROWL 
                                                  BODY_RARROWR BODY_RBANGL 
                                                               BODY_RBANGR BODY_RALLL 
                                                                           BODY_RALLR : enc.
 
  
  Definition RINIT (F:uexp) (w:uexp) : oo := u^|F @ w|  ** ( d^|F @ w| ) .
  Definition RTENSORL (F G w :uexp) :oo := d^| (F *** G) @ w| ** BODY_RTENSORL F G w.
  Definition RTENSORR (F G w :uexp) :oo := u^| (F *** G) @ w| ** BODY_RTENSORR F G w.
  Definition RIMPLL (F G w : uexp) : oo := d^| (F --o G) @ w | ** BODY_RIMPLL F G w.
  Definition RIMPLR (F G w : uexp) : oo := u^| (F --o G) @ w | ** BODY_RIMPLR F G w.
  Definition RATL (F v w : uexp) := d^|(F AT v) @ w| ** BODY_RATL F v.
  Definition RATR (F v w : uexp) := u^|(F AT v) @ w| ** BODY_RATR F v.
  Definition RARROWL FW w := d^| (ARROW FW) @ w| ** BODY_RARROWL FW w.
  Definition RARROWR FW w := u^| (ARROW FW) @ w| ** BODY_RARROWR FW w.
  Definition RBANGL F w := d^| (!! F) @ w| ** BODY_RBANGL F w.
  Definition RBANGR F w := u^| (!! F) @ w| ** BODY_RBANGR F w.
  Definition RCOPY F w :=  d^| F @ w| ** d| F @ w| . 
  Definition RALLL FX w := d^|(ALL FX) @ w| ** BODY_RALLL FX w.
  Definition RALLR FX w := u^|(ALL FX) @ w| ** BODY_RALLR FX w.

  Hint Unfold RINIT RTENSORL RTENSORR RIMPLL RIMPLR RATL RATR RARROWL RARROWR RBANGL RBANGR RCOPY  RALLL RALLR : enc.
  
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
  Definition REncode F := u| F|.
  
  Ltac solveOLFormula :=
      match goal with  
      
   | [ H1 : forall t,proper t -> isWorldExp t -> isOLFormula' (?FW0 t),
       H2 : lbind 0 ?FW0 = lbind 0 ?FW |- _ ] => 
        apply lbindEq in H2;auto;rewrite <- H2;eauto using isWorldProper
  | [ H: isOLFormula (_ (_ ?FW ) ?w0) |- isOLFormula (_ (?FW ?w0) ?w0) ] => 
        inversion H as [z1 z2 z3];subst;constructor;auto;
        inversion z3;subst;solveOLFormula
  | [ H: isOLFormula (_ (_ ?FW ) ?w0) |- Forall isOLFormula [_ (?FW ?w0) ?w0] ] => 
        inversion H as [z1 z2 z3];subst;constructor;auto;
        inversion z3;subst;solveOLFormula
        
             
   | [ H1 : forall t,proper t -> isOLFormula' (?FX0 t),
       H2 : lbind 0 ?FX0 = lbind 0 ?FX |- _ ] => 
        apply lbindEq in H2;auto;rewrite <- H2;eauto using isWorldProper
   | [ H: isOLFormula(_ (_ ?FX) ?w0) |- isOLFormula (_ (?FX ?x0) ?w0) ] => 
        inversion H;subst; match goal with 
                        | [ Hf: isOLFormula' (_ ?FX) |- _ ] => 
                          inversion Hf;subst  
                        end;solveOLFormula
      | [ H: isOLFormula(_ (_ ?FX) ?w0) |- Forall isOLFormula [_ (?FX ?x0) ?w0] ] => 
        inversion H;subst; match goal with 
                        | [ Hf: isOLFormula' (_ ?FX) |- _ ] => 
                          inversion Hf;subst  
                        end;solveOLFormula   
        
        
     | [ Hf: isOLFormula (_ (_ ?F) ?w) |- Forall isOLFormula [_ ?F ?w] ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;solveF 
     | [ Hf: isOLFormula (_ (_ ?F) ?w) |- isOLFormula (_ ?F ?w) ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;solveF 
                  
     | [ Hf: isOLFormula (_ (_ ?F ?v) ?w) |- Forall isOLFormula [_ ?F ?v] ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;solveF 
     | [ Hf: isOLFormula (_ (_ ?F ?v) ?w) |- isOLFormula (_ ?F ?v) ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;solveF 
             
     | [ Hf: isOLFormula (_ (_ ?F ?G) ?w) |- Forall isOLFormula [_ ?F ?w] ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;solveF 
     | [ Hf: isOLFormula (_ (_ ?F ?G) ?w) |- isOLFormula (_ ?F ?w) ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;solveF              

             
     | [ Hf: isOLFormula (_ (_ ?F ?G) ?w) |- Forall isOLFormula [_ ?G ?w] ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;solveF 
     | [ Hf: isOLFormula (_ (_ ?F ?G) ?w) |- isOLFormula (_ ?G ?w) ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;solveF  
            
     | [ Hf: isOLFormula (_ (_ ?F ?G) ?w) |- Forall isOLFormula [_ ?F ?w;_ ?G ?w] ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;solveF 
   
     | [ Hf: isOLFormula (_ (_ ?F ?G) ?w) |- isOLFormula [_ ?G ?w;_ ?G ?w] ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;solveF                                            
     end.
       
  Hint Constructors OLTheory: core.
  Hint Constructors isOLFormula : core.
  Hint Unfold LEncode REncode : core.


  (*********************************)
  (* CUT ELIMINATIOn *)
  (*********************************)
  Definition RCUT (F:uexp) (w:uexp) : oo := d|F @ w|  ** ( u|F @ w| ) .
  Definition RCCUT (F:uexp) (w:uexp) : oo := d| (!! F) @ w|  ** ( u|F @ w| ) .

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
  | oothc_cutn : forall F w m, isOLFormula (F @ w) -> lengthUexp F m -> m <= n ->  OLTheoryCut n (RCUT F w).

  Hint Constructors OLTheoryCut : core.

  (** atoms of the form [down A] *)
  Inductive IsPositiveLAtomFormula : oo -> Prop :=
  | IsFPAL_dw : forall A w , isOLFormula (A @ w) -> IsPositiveLAtomFormula (d| A @ w|)
  .
  Hint Constructors IsPositiveLAtomFormula : core .

  
  Definition IsPositiveLAtomFormulaL L : Prop := Forall IsPositiveLAtomFormula L.
  Hint Unfold IsPositiveLAtomFormulaL : core. 

  
  (* For each rule, BUT copy, prove the self duality of the bodies of the rules *)

   Theorem CutCoherenceTensor B F G w n m:
    lengthUexp F n ->
    lengthUexp G m ->
    isOLFormula' F ->
    isOLFormula' G ->
    isWorldExp w ->
    seq (OLTheoryCut (max n m)) B [] (> [dual (BODY_RTENSORR F G w);dual (BODY_RTENSORL F G w)]).
  Proof with solveF.
    intros;simpl.
    
    solveLL.
    (* With cut we can change up^ to down *)
    decide3 (RCUT F w)...
    apply oothc_cutn with (m:=n)...
    tensor [d^| F @ w | ** d^| G @ w |; u^| G @ w |] [u^| F @ w |].

    decide3 (RCUT G w)...
    apply oothc_cutn with (m:=m)...
    tensor [d^| F @ w | ** d^| G @ w |; d| F @ w |] [u^| G @ w |].

    decide1 (d^| F @ w | ** d^| G @ w |).
    tensor [d| F @ w | ][ d| G @ w |].
  Qed.
  
Theorem CutCoherenceAt B F v n:
    lengthUexp F n ->
    isOLFormula' F ->
    isWorldExp v ->
    seq (OLTheoryCut n) B [] (> [dual (BODY_RATL F v); dual (BODY_RATR F v)]).
   Proof with solveF.
    intros;simpl.
    solveLL.
    (* With cut we can change up^ to down *)
    decide3 (RCUT F v)...
    apply oothc_cutn with (m:=n)...
    tensor [d^| F @ v |] [u^| F @ v |].
  Qed.
  
  Theorem CutCoherenceImpl B F G w n m:
    lengthUexp F n ->
    lengthUexp G m ->
    isOLFormula' F ->
    isOLFormula' G ->
    isWorldExp w ->
    seq (OLTheoryCut (max n m)) B [] (> [dual (BODY_RIMPLL F G w);dual (BODY_RIMPLR F G w)]).
   Proof with solveF.
    intros;simpl.
    solveLL.
    (* With cut we can change up^ to down *)
    decide3 (RCUT F w)...
    apply oothc_cutn with (m:=n)...
    tensor [d^| F @ w | ** u^| G @ w |; d^| G @ w |] [u^| F @ w |].

    decide3 (RCUT G w)...
    apply oothc_cutn with (m:=m)...
    unfold RCUT.
    tensor [d^| G @ w |] [d^| F @ w | ** u^| G @ w |; d| F @ w |].

    decide1 (d^| F @ w | ** u^| G @ w |).
    tensor [d| F @ w | ][ u| G @ w |].
  Qed.

  Theorem CutCoherenceArrow B FW w n:
    lengthUexp (FW w) n ->
    uniform FW ->
    isOLFormula' (FW w) ->
    isWorldExp w ->
    seq (OLTheoryCut n) B [] (> [dual (BODY_RARROWL FW w); dual (BODY_RARROWR FW w)]).
   Proof with solveF.
    intros;simpl.
    solveLL.
    (* With cut we can change up^ to down *)
    decide3 (RCUT (FW w) w)...
    apply oothc_cutn with (m:=n)...
    tensor [d^| (FW w) @ w |] [u^| (FW w) @ w |].
  Qed.
  
  Theorem CutCoherenceBang B F w n:
    lengthUexp F n ->
    isOLFormula' F ->
    isWorldExp w ->
    seq (OLTheoryCut n) B [] (> [dual (BODY_RBANGL F w); dual (BODY_RBANGR F w)]).
   Proof with solveF.
    intros;simpl.
    solveLL.
    decide1 (! d^| F @ w |).
    (* With cut we can change up^ to down *)
    decide3 (RCUT F w)...
    apply oothc_cutn with (m:=n)...
    tensor [ d^| F @ w |] (@nil oo) .
    decide2 (u^| F @ w |).
    intuition.
  Qed.

 Axiom OLSize: forall FX t t' n, uniform FX -> proper t -> proper t' -> lengthUexp (FX t) n -> lengthUexp (FX t') n .


  Theorem CutCoherenceAll B FX FX' w n:
    (* uniform (fun x : uexp => (FX' x) @ w) ->
    uniform (fun x : uexp => (FX x) @ w) -> *)
    uniform FX ->
    uniform FX' ->
    ext_eq FX FX' ->
    proper w ->
    lengthUexp (FX' (Var 0))  n ->
    (forall t, proper t -> isOLFormula ((FX' t) @ w)) ->
     seq (OLTheoryCut n) B [] (> [dual (BODY_RALLL FX' w); dual (BODY_RALLR FX w)]).
   Proof with solveF.
    intros;simpl. solveLL. 
    decide3 (RCUT (FX' x) w).
    apply oothc_cutn with (m:=n)...
    apply OLSize with (t:= (Var 0)) ;eauto using proper_VAR.
    tensor  [d^| (FX' x) @ w |] [E{ fun x0 => u^| (FX x0) @ w |}].
    
    decide1 (E{ fun x0 => u^| (FX x0) @ w |}).
    existential x.
    solveLL.
    rewrite H1...
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
    FLLInversionAll.
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
                   ( In (d| F1 @ w0 |) (LEncode Gamma) /\
                     seqN OLTheory n' (LEncode Gamma) (REncode (F @ w) :: LEncode L) (>> G)))
  .
    Proof.
    intros.
    FLLInversionAll.
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
      exact H1.
      rewrite <- H2 in H7.
      LLExact H7.
    }
  Qed.
  
  Theorem TheoryInclusion: forall F n , OLTheory F -> OLTheoryCut n F.
    intros.
    inversion H;subst;auto.
  Qed.

  
  Lemma rewL1 : forall th  F G D1 D2 L X, 
  Permutation D1 L ->
  seq th (LEncode G) (F::LEncode L ++ LEncode D2) X -> seq th (LEncode G) (F::LEncode (D1++D2)) X. 
  Proof.
  intros.
  assert(Permutation (LEncode D1) (LEncode L)) by apply (Permutation_map _ H).
  unfold LEncode. rewrite map_app.
  rewrite H1.
  exact H0.
  Qed.
  
  Lemma rewL2 : forall th  F G D1 D2 L X, 
  Permutation D2 L ->
  seq th (LEncode G) (F::LEncode D1 ++ LEncode L) X -> seq th (LEncode G) (F::LEncode (D1++D2)) X. 
  Proof.
  intros.
  assert(Permutation (LEncode D2) (LEncode L)) by apply (Permutation_map _ H).
  unfold LEncode. rewrite map_app.
  rewrite H1.
  exact H0.
  Qed.
 

  
  Ltac permMap :=
  match goal with
  | |- Permutation _ _ => unfold REncode;unfold LEncode; try rewrite !map_app;simpl;perm_simplify; fail "permMap failed"
  | |- _ => fail "permMap can't solve this system."
  end.
  

 Ltac  LLPermMap P :=
  match goal with
  | |- seq _ ?Gamma ?Delta _ =>
        let HP := fresh "H" in
        first
        [ assert (HP : Permutation Gamma P) by permMap; rewrite HP;clear HP
        | assert (HP : Permutation Delta P) by permMap; rewrite HP;clear HP]
 | |- seqN _ _ ?Gamma ?Delta _ =>
        let HP := fresh "H" in
        first
        [ assert (HP : Permutation Gamma P) by permMap; rewrite HP;clear HP
        | assert (HP : Permutation Delta P) by permMap; rewrite HP;clear HP]        
  end.

  Ltac LLExactMap H :=
   let G := type of H in
  match G with
  | seqN ?T _ ?Gamma ?Delta ?X =>
      match goal with
      | |- seqN T _ ?Gamma' ?Delta' X =>
            apply exchangeCCN with (CC := Gamma); auto; try permMap;
             apply exchangeLCN with (LC := Delta); auto; 
             try permMap
      end
  end; auto.
    
  Lemma NotFromLEncode : forall F L, 
    ~ IsPositiveAtom F -> In F (LEncode L) -> False.
 Proof with solveF.
   intros.
   apply in_map_iff in H0.
   destruct H0...
 Qed.
    
Lemma NotFromREncode  : forall F G L L', 
    ~ IsPositiveAtom F -> Remove F (REncode G :: LEncode L) L' -> False.
 Proof with solveF.
   intros.
   autounfold in H0. 
   apply Remove_inv_cons in H0.
   destruct H0.
   { destruct H0... }
      { destruct H0...
       apply Remove_In in H1.
       apply NotFromLEncode in H1... }
 Qed.
  
Lemma AppEncode: forall x0 x1 x2, Permutation (x2 ++ x1) (LEncode x0) ->  exists x3 l1' l2',
       Permutation x0 x3 /\ x3 = l1' ++ l2' /\
       LEncode l1' = x2 /\ LEncode l2' = x1.
 Proof.
   intros.
    apply Permutation_map_inv in H.     
    do 2 destruct H.
    symmetry in H.
    apply map_eq_app in H.
    do 3 destruct H.
    destruct H1.
    eexists;eexists;eexists;eauto.
 Qed.  
    

  Global Instance Forall_morph : 
    Proper (Permutation (A:=uexp) ==> Basics.flip Basics.impl) isOLFormulaL.
  Proof.
    unfold Proper; unfold respectful; unfold Basics.flip; unfold Basics.impl.
    intros.
    eapply Forall_Permute;eauto.
    symmetry;auto.
  Qed. 
  
Ltac simplPermuteMap :=   
     match goal with  
   | [ H: Permutation (map (fun x : uexp => d| x |) ?L)
       (?M ++ ?N) |- _ ] => 
        symmetry in H; apply AppEncode in H; destruct H as [x Hx];
        destruct Hx as [y Hy];destruct Hy as [z Hz];decompose [and] Hz;subst;clear Hz 
   | [ H: Permutation (LEncode ?L)(?M ++ ?N) |- _ ] => 
        symmetry in H; apply AppEncode in H; destruct H as [x' Hx'];
        destruct Hx' as [y' Hy'];destruct Hy' as [z' Hz'];decompose [and] Hz';subst;clear Hz'        
    end.
 
   
Ltac solveNoUPInDown :=  
try 
 match goal with  
   | [ H: In (u| ?F |) (map (fun x : uexp => d| x |) ?L) |- _ ] => 
       apply NoUPInPositiveLAtom' in H
    | [ H: LEncode ?L = [u| ?F |] |- _ ] => 
        apply map_eq_cons in H; do 2 destruct H
    end.
    
Ltac easyOLFormula :=
      match goal with  
      | [ Hl: _ |- _ (?F :: ?N) ] => 
              apply ForallCons;auto      
      | [ Hl: isOLFormulaL ?L |- isOLFormulaL (?L ++ ?N) ] => 
            apply ForallApp;auto  
     | [ H1: isOLFormulaL ?L,
         Hp: Permutation ?L (?x0 ++ ?x1) |- isOLFormulaL (?x1 ++ ?N) ] => 
            rewrite Hp in H1;apply ForallApp;[apply (ForallAppInv2 H1) | ] 
     | [ H1: isOLFormulaL ?L,
         Hp: Permutation ?L (?x0 ++ ?x1) |- isOLFormulaL (?x0 ++ ?N) ] => 
            rewrite Hp in H1;apply ForallApp;[apply (ForallAppInv1 H1) | ]
     | [ H1: isOLFormulaL ?L,
         Hp: Permutation ?L (?x0 ++ ?x1) |- isOLFormulaL ?x1  ] => 
            rewrite Hp in H1;apply (ForallAppInv2 H1) 
     | [ H1: isOLFormulaL ?L,
         Hp: Permutation ?L (?x0 ++ ?x1) |- isOLFormulaL ?x0 ] => 
            rewrite Hp in H1;apply (ForallAppInv1 H1)  
     | [ H1: isOLFormulaL ?L,
         Hp: Permutation ?L (?F :: ?x0) |- isOLFormulaL ?x0 ] => 
            rewrite Hp in H1;inversion H1;subst;auto  
     | [ H1: isOLFormulaL ?L,
         Hp: Permutation ?L (?F :: ?x0) |- Forall isOLFormula ?x0 ] => 
            rewrite Hp in H1;inversion H1;subst;auto 
     | [ H1: isOLFormulaL ?D,
         Hp: Permutation ?D (?x0 ++ ?x1) |- _ ?x1 ] => 
            rewrite Hp in H1;apply (ForallAppInv2 H1)
     | [ H1: isOLFormulaL ?D,
         Hp: Permutation ?D (?x0 ++ ?x1) |- _ ?x0 ] => 
            rewrite Hp in H1;apply (ForallAppInv1 H1)
     | [ H: _ (?x0 ++ ?x1) |- _ ?x0 ] => 
          apply (ForallAppInv1 H) 
     | [ H: _ (?x0 ++ ?x1) |- _ ?x1 ] => 
          apply (ForallAppInv2 H) 
     | [ H1: isOLFormulaL ?D,
         Hp: Permutation ?D (?F :: ?x0 ++ ?x1) |- _ ?x1 ] => 
            rewrite Hp in H1;inversion H1;subst;easyOLFormula
     | [ H1: isOLFormulaL ?D,
         Hp: Permutation ?D (?F :: ?x0 ++ ?x1) |- _ ?x0 ] => 
            rewrite Hp in H1;inversion H1;subst;easyOLFormula
    | [ H1: isOLFormulaL ?L, Hz: Permutation ?z (?y' ++ ?z'),
         Hp: Permutation ?L (?y ++ ?z) |- isOLFormulaL (?z' ++ ?N) ] => 
            rewrite Hp in H1;rewrite Hz in H1;apply ForallApp;[rewrite app_assoc in H1; apply (ForallAppInv2 H1) | ]                                            
    end;auto;try solveOLFormula.
    


Ltac easyF := try apply ForallApp;auto; try apply ForallCons;auto;try solveOLFormula;try easyOLFormula.

 (** None legal applications of rules are OK *)
Theorem NORightNotProvable : forall n Gamma  L ,
      isOLFormulaL Gamma -> 
      isOLFormulaL L ->  
      ~ seqN OLTheory n (LEncode Gamma)  (LEncode L) ( > [] ) .
 Proof with solveNoUPInDown; solveF;try easyOLFormula.
    induction n using strongind;intros...
    * intro Hc; inversion Hc...
    * intro; inversion H2...
      + (* from Linear *)
        apply Remove_In in H5.
        apply NotFromLEncode in H5...
      + (* from Classical *)
        apply NotFromLEncode in H5...
      + (* from Theory *)
        inversion H4... 
        - autounfold with enc in H6. 
          FLLInversionAll; CleanContext...
          
          simplPermuteMap...      
          simplPermuteMap...
        - autounfold with enc in H6. 
          FLLInversionAll; CleanContext... 
          
          { simplPermuteMap.
 
          assert(Hc: ~ seqN OLTheory n0 (LEncode Gamma)
                  (LEncode (z ++ [F0 @ w] ++ [G @ w])) 
                   (> [])).
          apply H... 
          apply Hc.
          LLExactMap H17. }
          
         rewrite <- H9 in H18.
         assert(Hc: ~ seqN OLTheory n0 (LEncode Gamma)
                  (LEncode (L ++ [F0 @ w] ++ [G @ w])) 
                   (> [])).
        apply H...          
        apply Hc.
        LLExactMap H18.
        -
        autounfold with enc in H6. 
        FLLInversionAll; CleanContext... 
        simplPermuteMap... 
        -
        autounfold with enc in H6. 
        FLLInversionAll; CleanContext... 
        
           { do 2 simplPermuteMap. 
             assert(Hc: ~ seqN OLTheory n (LEncode Gamma)
                  (LEncode (z' ++ [ G @ w]))
                   (> [])).
             apply H... 
             apply Hc.
             LLExactMap H20. }
        
        rewrite <- H9 in H8.
        simplPermuteMap.

         assert(Hc: ~ seqN OLTheory n (LEncode Gamma)
                  (LEncode (z ++ [ G @ w]))
                   (> [])).
         apply H...          
         apply Hc.
         LLExactMap H21.
        -
         autounfold with enc in H6. 
         FLLInversionAll; CleanContext... 
         simplPermuteMap...
        -
         autounfold with enc in H6. 
         FLLInversionAll; CleanContext... 
         simplPermuteMap.
          assert(Hc: ~ seqN OLTheory n0 (LEncode Gamma)
                  (LEncode (z ++ [ F0 @ v]))
                   (> [])).
         apply H...   
         apply Hc.
         LLExactMap H16. 
         
         rewrite <- H9 in H17.
         assert(Hc: ~ seqN OLTheory n0 (LEncode Gamma)
                  (LEncode (L ++ [ F0 @ v]))
                   (> [])).
         apply H...
         apply Hc.
         LLExactMap H17.
       -  
         autounfold with enc in H6. 
         FLLInversionAll; CleanContext... 
         simplPermuteMap...
        -
         autounfold with enc in H6. 
         FLLInversionAll; CleanContext... 
         simplPermuteMap.
         assert(Hc: ~ seqN OLTheory n0 (LEncode Gamma)
                  (LEncode (z ++ [ (FW w) @ w ]))
                   (> [])).
         apply H...          
         apply Hc.
         LLExactMap H17. 
         
         rewrite <- H10 in H18.
         assert(Hc: ~ seqN OLTheory n0 (LEncode Gamma)
                  (LEncode (L ++ [ (FW w) @ w ]))
                   (> [])).
         apply H...
         apply Hc.
         LLExactMap H18.
        -
         autounfold with enc in H6. 
         FLLInversionAll; CleanContext... 
         simplPermuteMap...
        -
         autounfold with enc in H6. 
         FLLInversionAll; CleanContext... 
         simplPermuteMap.
          assert(Hc: ~ seqN OLTheory n0 (LEncode (Gamma++[F0 @ w]))
                  (LEncode z)
                   (> [])).
          apply H...
          apply Hc.
          LLExactMap H14.
          
          rewrite <- H9 in H15.
          assert(Hc: ~ seqN OLTheory n0 (LEncode (Gamma++[F0 @ w]))
                  (LEncode L)
                   (> [])).
          apply H...
          apply Hc.
          LLExactMap H15.
        -
         autounfold with enc in H6. 
         FLLInversionAll; CleanContext... 
         simplPermuteMap...
        -
         autounfold with enc in H6. 
         FLLInversionAll; CleanContext... 
         simplPermuteMap.
          assert(Hc: ~ seqN OLTheory n0 (LEncode Gamma)
                          (LEncode (z ++ [ F0 @ w])) (> [])).
          apply H...
          apply Hc.
          LLExactMap H16.
          
          rewrite <- H9 in H17.
          assert(Hc: ~ seqN OLTheory n0 (LEncode Gamma)
                          (LEncode (L ++ [ F0 @ w])) (> [])).
          apply H...  
          apply Hc.
          LLExactMap H17.
        -
         autounfold with enc in H6. 
         FLLInversionAll; CleanContext... 
         simplPermuteMap.
          assert(Hc: ~ seqN OLTheory n (LEncode Gamma)
                          (LEncode (z ++ [ (FX t) @ w])) (> [])).
          apply H...  
          apply Hc.
          LLExactMap H19.
          
          rewrite <- H10 in H20.
          assert(Hc: ~ seqN OLTheory n (LEncode Gamma)
                          (LEncode (L ++ [ (FX t) @ w])) (> [])).
          apply H...
          apply Hc.
          LLExactMap H20.
        -
         autounfold with enc in H6. 
         FLLInversionAll; CleanContext... 
         simplPermuteMap...
 Qed.         

  
  (*********************)
  (* INVERSION LEMMA *)
  (*******************)

  Theorem RINITInv1:  forall n Gamma G v L F w0,
      isOLFormulaL  Gamma ->
      isOLFormulaL  L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RINIT F w0) ->
      (G = F /\ v = w0 /\ ( L = [ F @ w0]  \/ ( L = [] /\ In (d| F @ w0 |) (LEncode Gamma)))).
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
  Qed.
  
 Theorem RINITInv2:  forall n Gamma G v L F J w w0,
     isOLFormula (J @ w) ->
      isOLFormulaL  Gamma ->
      isOLFormulaL  L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (J @ w :: L)) (>> RINIT F w0) ->
      ( ( G = F /\ v = w0 /\ J = F /\ w = w0 /\  L = [])).
  Proof with solveF.
    intros.
    eapply FocusinRightAtom in H2...
    CleanContext.
    inversion H3...
    assert (L=[]).
    eapply map_eq_nil. symmetry in H7;eauto.
    split;eauto.
  Qed.
  
  
 Theorem BANGLInv1:  forall n Gamma G H w0 v L ,
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RBANGL H w0) ->
      (exists n' X,
          n = S (S (S n')) /\ Permutation L ((!! H) @ w0 :: X)
          /\ seqN OLTheory n' ((LEncode Gamma) ++ [d| H @ w0 |]) (REncode (G @ v) :: LEncode X) (> [])) \/
      (exists n',
          n = S (S (S n')) /\ In (d| (!! H) @ w0 |) (LEncode Gamma)
          /\ seqN OLTheory n' ((LEncode Gamma) ++ [d| H @ w0 |]) (REncode (G @ v) :: LEncode L) (> [])).
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H0;unfold BODY_RBANGL in H0.
 
    CleanContext.
    destruct H1;CleanContext.
    -
    FLLInversionAll.
    CleanContext.
    left.
    eexists n0;
    eexists x0;
    split;auto.
    - 
    FLLInversionAll.
    CleanContext.
    right.
    eexists n0;
    split;auto.    
  Qed.

 Theorem BANGLInv2:  forall n Gamma F G H w w0 v L ,
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (F @ w :: L)) (>> RBANGL H w0) ->
      (exists n',
          n = S (S (S n')) /\ F @ w = (!! H) @ w0
          /\ seqN OLTheory n' ((LEncode Gamma) ++ [d| H @ w0 |]) (REncode (G @ v) :: LEncode L) (> [])) \/
      (exists n' X,
          n = S (S (S n')) /\ Permutation L ((!! H) @ w0 :: X)
          /\ seqN OLTheory n' ((LEncode Gamma) ++ [d| H @ w0 |]) (REncode (G @ v) :: LEncode (F @ w :: X)) (> [])) \/
      (exists n',
          n = S (S (S n')) /\ In (d| (!! H) @ w0 |) (LEncode Gamma)
          /\ seqN OLTheory n' ((LEncode Gamma) ++ [d| H @ w0 |]) (REncode (G @ v) :: LEncode (F @ w :: L)) (> [])).
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H0;unfold BODY_RBANGL in H0.
 
    CleanContext.
    destruct H1;CleanContext.
    -
    FLLInversionAll.
    CleanContext.
    apply PProp_perm_select in H0.
    destruct H0;
    CleanContext...
    +
    left.
    assert(Permutation (LEncode L) (LEncode x0)) by apply (Permutation_map _ H1).
    rewrite <- H2 in H6.
    eexists n0;
    split;auto.
    +
    right. left.
    eexists n0;
    eexists x.
    split;auto.
    split;auto.
    rewrite H0 in H6;eauto.
    -
    FLLInversionAll.
    CleanContext.
    right. right.
    eexists n0;
    split;auto.    
  Qed.
 

 Theorem BANGRInv1:  forall n Gamma G H w0 v L ,
      isOLFormulaL Gamma -> isOLFormulaL L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RBANGR H w0) ->
      exists n' ,
          n = S (S (S n')) /\ L=[] /\ G = !! H /\ v = w0
          /\ seqN OLTheory n' (LEncode Gamma) ([u| H @ w0 |]) (> []) .
  Proof with solveF.
    intros.
    apply FocusinRightAtom in H2;auto;unfold BODY_RBANGR in H2.
    CleanContext.
    FLLInversionAll.
    symmetry in H2.
    apply map_eq_nil in H2.
    eexists n0;split; auto.
  Qed.


 Theorem BANGRInv2:  forall n Gamma F G H w w0 v L ,
       isOLFormula (F @ w) -> isOLFormulaL Gamma -> isOLFormulaL L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (F @ w :: L)) (>> RBANGR H w0) ->
      False.
  Proof.
    intros.
    apply FocusinRightAtom in H3;auto;unfold BODY_RBANGR in H3.
    CleanContext.
   
    inversion H4;subst.
    inversion H5.
  Qed.
  
 
 
  Theorem RIMPLLInv1:  forall n Gamma G F1 F2 w0 v L ,
  isOLFormulaL Gamma -> isOLFormulaL L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RIMPLL F1 F2 w0) ->
  ( 
(exists n' X1 X2, n = S (S (S (S n'))) /\ 
              Permutation  L ((F1 --o F2) @ w0 ::  (X1 ++ X2)) /\
              (seqN OLTheory n' (LEncode Gamma) (LEncode X1 ++[u| F1 @ w0 |]) (> []))  /\
              (seqN OLTheory n' (LEncode Gamma) ((u| G @ v | :: LEncode X2) ++ LEncode [F2 @ w0])) (> []) ) \/               
(exists n' X1 X2, n = S (S (S (S n'))) /\ In (d| (F1 --o F2) @ w0 |) (LEncode Gamma) /\ 
              Permutation L (X1 ++ X2) /\
              (seqN OLTheory n' (LEncode Gamma) (LEncode X1 ++ [u| F1 @ w0 |]) (> []))  /\
              (seqN OLTheory n' (LEncode Gamma) ((u| G @ v | :: LEncode X2) ++ LEncode [F2 @ w0])) (> []) )) .
  Proof with solveF.
  intros.
    apply FocusinLeftAtom in H1;unfold BODY_RIMPLL in H1.
 
    CleanContext.
    destruct H2;CleanContext.
  
    -
      FLLInversionAll.
      CleanContext.
      symmetry in H5.
      apply PProp_perm_select' in H5.
      destruct H5;CleanContext.
        
      +
      left.
      apply AppEncode in H3.
      do 3 destruct H3.
      decompose [and] H3;subst;clear H3.
      
      assert(seqN OLTheory n (map (fun x : uexp => d| x |) Gamma)
        (LEncode (x3 ++ [ F2 @ w0])) (> [])).
     LLExactMap H14.   
        
      assert(~ seqN OLTheory n (map (fun x : uexp => d| x |) Gamma)
        (LEncode (x3 ++ [ F2 @ w0])) (> [])).
      apply NORightNotProvable;auto.
      rewrite H4 in H1.
      assert(isOLFormulaL ((F1 --o F2) @ w0 :: x2 ++ x3)).
      apply (Forall_Permute H0 H1).
      inversion H5;subst.
      inversion H8;subst.
      inversion H10;subst.
      apply ForallApp;auto.
      solveForall. 
      contradiction.
      +
      left.
      apply AppEncode in H3.
      do 3 destruct H3.
      decompose [and] H3;subst;clear H3.
      rewrite H2 in H14.
      rewrite H4 in H1.
      
          
      eexists n;
      eexists x2; 
      eexists x3;split;auto.      
    -
      FLLInversionAll.
      CleanContext.
      
      symmetry in H5.
      apply PProp_perm_select' in H5.
      destruct H5;CleanContext.
      +
       apply AppEncode in H3.
       do 3 destruct H3.
       decompose [and] H3;subst;clear H3.
        assert(seqN OLTheory n (map (fun x : uexp => d| x |) Gamma)
        (LEncode (x2 ++ [ F2 @ w0])) (> [])).
        LLExactMap H14.   
        
      assert(~ seqN OLTheory n (map (fun x : uexp => d| x |) Gamma)
        (LEncode (x2 ++ [ F2 @ w0])) (> [])).
      apply NORightNotProvable;auto.
      
       assert(isOLFormulaL (x1 ++ x2)).
      apply (Forall_Permute H0 H4).
      

      apply in_map_iff in H1.
      destruct H1;CleanContext.
      inversion H1;subst.
      assert(isOLFormula ((F1 --o F2) @ w0)). 
      eapply (Utils.isFormulaIn H H6).
   
      inversion H7;subst.
      inversion H10;subst.
      apply ForallApp;auto.
      apply (Forall_app _ x1 x2);auto.
      contradiction.
      +
       right.
       apply AppEncode in H3.
       do 3 destruct H3.
       decompose [and] H3;subst;clear H3.
       rewrite H2 in H14.
       eexists n;
       eexists x1;
       eexists x2;split;auto.
 Qed.  
   

Theorem RIMPLLInv2:  forall n Gamma F G F1 F2 w w0 v L ,
isOLFormula (F @ w) ->
  isOLFormulaL Gamma -> isOLFormulaL L -> 
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (F @ w :: L)) (>> RIMPLL F1 F2 w0) ->
         ( 
(exists n' X1 X2, n = S (S (S (S n'))) /\ 
              F = (F1 --o F2)  /\  w = w0  /\ Permutation L (X1 ++ X2)  /\
              (seqN OLTheory n' (LEncode Gamma) (LEncode X1 ++ [u| F1 @ w0 |]) (> []))  /\
              (seqN OLTheory n' (LEncode Gamma) ((u| G @ v | :: LEncode X2) ++ [d| F2 @ w0 |])) (> []) ) \/               
(exists n' X1 X2, n = S (S (S (S n'))) /\  Permutation L ((F1 --o F2) @ w0 :: X1 ++ X2)  /\
              (seqN OLTheory n' (LEncode Gamma) (LEncode (F @ w :: X1) ++ [u| F1 @ w0 |]) (> []))  /\
              (seqN OLTheory n' (LEncode Gamma) ((u| G @ v | :: LEncode X2) ++ [d| F2 @ w0 |])) (> []) ) \/  
(exists n' X1 X2, n = S (S (S (S n'))) /\  Permutation L ((F1 --o F2) @ w0 :: X1 ++ X2)  /\
              (seqN OLTheory n' (LEncode Gamma) (LEncode X1 ++ [u| F1 @ w0 |]) (> []))  /\
              (seqN OLTheory n' (LEncode Gamma) ((u| G @ v | :: LEncode (F @ w :: X2)) ++ [d| F2 @ w0 |])) (> []) ) \/                                                    
(exists n' X1 X2, n = S (S (S (S n'))) /\ In (d| (F1 --o F2) @ w0 |) (LEncode Gamma) /\ 
              Permutation L (X1 ++ X2) /\
              (seqN OLTheory n' (LEncode Gamma) (LEncode (F @ w :: X1) ++ [u| F1 @ w0 |]) (> []))  /\
              (seqN OLTheory n' (LEncode Gamma) ((u| G @ v | :: LEncode X2) ++ [d| F2 @ w0 |])) (> []) ) \/
(exists n' X1 X2, n = S (S (S (S n'))) /\ In (d| (F1 --o F2) @ w0 |) (LEncode Gamma) /\ 
              Permutation L (X1 ++ X2) /\
              (seqN OLTheory n' (LEncode Gamma) (LEncode X1 ++ [u| F1 @ w0 |]) (> []))  /\
              (seqN OLTheory n' (LEncode Gamma) ((u| G @ v | :: LEncode (F @ w :: X2)) ++ [d| F2 @ w0 |])) (> []) ) ) .
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H2;unfold BODY_RIMPLL in H2.
 
    CleanContext.
    destruct H3;CleanContext.
    -
    FLLInversionAll.
    CleanContext. 
    apply PProp_perm_select in H2.
    destruct H2;CleanContext.
      +
      symmetry in H6.
      apply PProp_perm_select' in H6.
      destruct H6;CleanContext.
      ++
        apply AppEncode in H5.
        do 3 destruct H5;CleanContext.
        
        assert(seqN OLTheory n (map (fun x : uexp => d| x |) Gamma)
        (LEncode (x3 ++ [ F2 @ w0])) (> [])).
        LLExactMap H15.   
        
      assert(~ seqN OLTheory n (map (fun x : uexp => d| x |) Gamma)
        (LEncode (x3 ++ [ F2 @ w0])) (> [])).
      apply NORightNotProvable;auto.
      apply ForallApp;auto.
      rewrite H5 in H3.
      
      specialize (Forall_Permute H1 H3);intros.
      solveForall.
      rewrite H2 in H.
      inversion H;subst.
      inversion H9;subst.
      eauto.
      contradiction.
      ++ left. 
        apply AppEncode in H5.
        do 3 destruct H5;CleanContext.
        rewrite H4 in H15.
        rewrite H5 in H3.
        inversion H2;subst.    
        eexists n.
        eexists x2. 
        eexists x3;split;auto.
     + 
     symmetry in H6.
      apply PProp_perm_select' in H6.
      destruct H6;CleanContext.
      ++
        left.
        apply AppEncode in H5.
        do 3 destruct H5;CleanContext.
        
        assert(seqN OLTheory n (map (fun x : uexp => d| x |) Gamma)
        (LEncode (x4 ++ [ F2 @ w0])) (> [])).
        LLExactMap H15.   
        
      assert(~ seqN OLTheory n (map (fun x : uexp => d| x |) Gamma)
        (LEncode (x4 ++ [ F2 @ w0])) (> [])).
      apply NORightNotProvable;auto.
      apply ForallApp;auto.
      specialize (Forall_Permute H1 H3);intros.
      inversion H7;subst.
      assert(isOLFormulaL (F @ w :: x)). apply ForallCons;auto.
     assert(isOLFormulaL x0).
     symmetry in H2. 
     eapply (Forall_Permute H8 H2).
   
      assert(isOLFormulaL (x3 ++ x4)).
       eapply (Forall_Permute H9 H5).
     apply (Forall_app _ x3 x4);auto.
     
     assert(isOLFormulaL ((F1 --o F2) @ w0 :: x)).
     eauto using Forall_Permute.
     inversion H7;subst.
     inversion H10;subst.
      inversion H12;subst.
      eauto.
      contradiction.
      ++ right. 
        apply AppEncode in H5.
        do 3 destruct H5;CleanContext.
        rewrite H4 in H15.
        rewrite H5 in H2.
        apply PProp_perm_select' in H2.
        destruct H2;CleanContext. 
        assert(Permutation (LEncode x3) (LEncode (F @ w :: x1))).
        apply (Permutation_map _ H2).
        rewrite H7 in H14.        
        rewrite <- H6 in H3.
        left.
        eexists n;
        eexists x1; 
        eexists x4;split;auto.

        assert(Permutation (LEncode x4) (LEncode (F @ w :: x1))).
        apply (Permutation_map _ H2).
        rewrite H7 in H15.        
        rewrite <- H6 in H3.
        right. left.
        eexists n;
        eexists x3; 
        eexists x1;split;auto.
   -
   FLLInversionAll.
   CleanContext.
   symmetry in H6.
   apply PProp_perm_select' in H6.
   destruct H6;CleanContext.
      +
       assert(Permutation (x ++ N)
       (LEncode ([ F @ w ] ++ L))) by auto.
       
       apply AppEncode in H5.
        do 3 destruct H5;CleanContext.
        
        assert(seqN OLTheory n (map (fun x : uexp => d| x |) Gamma)
        (LEncode (x2 ++ [ F2 @ w0])) (> [])).
        LLExactMap H15.   
        
      assert(~ seqN OLTheory n (map (fun x : uexp => d| x |) Gamma)
        (LEncode (x2 ++ [ F2 @ w0])) (> [])).
      apply NORightNotProvable;auto.
      apply ForallApp;auto.
      assert(isOLFormulaL ([F @ w] ++ L)).
      apply ForallApp;auto.
      assert(isOLFormulaL (x1 ++ x2)).
      apply (Forall_Permute H7 H5).
      apply (Forall_app _ x1 x2);auto.
      
       apply in_map_iff in H2.
      destruct H2;CleanContext.
      inversion H2;subst.
      assert(isOLFormula ((F1 --o F2) @ w0)). 
      eapply (Utils.isFormulaIn H0 H7).
      
     inversion H8;subst.
     inversion H11;subst.
     eauto.
      contradiction.
      +
       right. right. right.  
       
       assert(Permutation (M ++ x)
       (LEncode ([ F @ w ] ++ L))) by auto.
       
       apply AppEncode in H5.
        do 3 destruct H5;CleanContext.
        
        apply PProp_perm_select' in H4.
        destruct H4;CleanContext. 
        rewrite H3 in H15.
        symmetry in H4.
        apply Permutation_map_inv in H4.
        destruct H4;CleanContext.
        symmetry in H4.
        apply map_eq_cons in H4.
        destruct H4;CleanContext. 
        inversion H8;subst.
        assert(Permutation (LEncode x1) (LEncode (F @ w :: x4))).
        apply (Permutation_map _ H7).
        rewrite H4 in H14.        
        left.
        rewrite H7 in H5.
        do 2 rewrite app_normalize_2  in H5.
        apply Permutation_cons_inv in H5.
         
        eexists n;
        eexists x4; 
        eexists x2;split;auto.
        
    
        rewrite H3 in H15.
        symmetry in H4.
        apply Permutation_map_inv in H4.
        destruct H4;CleanContext.
        symmetry in H4.
        apply map_eq_cons in H4.
        destruct H4;CleanContext. 
        inversion H8;subst.
        assert(Permutation (LEncode x2) (LEncode (F @ w :: x4))).
        apply (Permutation_map _ H7).
        rewrite H4 in H15.        
        right.
        rewrite H7 in H5.
        simpl in H5.

        apply Permutation_mid with (l1:=[]) in H5.
       
        eexists n;
        eexists x1; 
        eexists x4;split;auto.

  Qed.
   
 Theorem RIMPLRInv1:  forall n Gamma G F1 F2 w0 v L ,
 isOLFormulaL Gamma -> isOLFormulaL L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RIMPLR F1 F2 w0) ->
(exists n', n = S (S (S (S (S n')))) /\
               G = F1 --o F2 /\ v = w0 /\ 
              (seqN OLTheory n' (LEncode Gamma) (LEncode L ++ [d| F1 @ w0 |; u| F2 @ w0 |]) (> []))) .
  Proof with solveF. 
    intros.
    apply FocusinRightAtom in H1;auto;unfold BODY_RIMPLR in H1.
 
    CleanContext.
    FLLInversionAll.
    CleanContext.
    eexists n0.
    split;auto.
    split;auto.
    split;auto.
    rewrite <- app_assoc in H10.
    LLExact H10.
  Qed. 

 Theorem RIMPLRInv2:  forall n Gamma G F F1 F2 w w0 v L ,
 isOLFormula (F @ w) ->
 isOLFormulaL Gamma -> isOLFormulaL L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (F @ w :: L)) (>> RIMPLR F1 F2 w0) ->
(exists n', n = S (S (S (S (S n')))) /\ G = F1 --o F2 /\ v = w0 /\
              (seqN OLTheory n' (LEncode Gamma) (LEncode (F @ w :: L)  ++ [d| F1 @ w0 |; u| F2 @ w0 |]) (> []))) .
  Proof with solveF. 
    intros.
    apply FocusinRightAtom in H2;auto;unfold BODY_RIMPLR in H2.
 
    CleanContext.
    FLLInversionAll.
    CleanContext.
    eexists n0.
    split;auto.
    split;auto.
    split;auto.
    rewrite <- app_normalize_2 in H11.
    rewrite <- app_assoc in H11.
    LLExact H11.    
  Qed.   
  
 Theorem RTENSORLInv1:  forall n Gamma G F1 F2 w0 v L ,
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RTENSORL F1 F2 w0) ->
         (
(exists n' X, n = S (S (S (S (S n')))) /\ Permutation  L ((F1 *** F2) @ w0 :: X)  /\ 
(seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (X ++ [F1 @ w0] ++ [F2 @ w0])) (> []))) \/

(exists n', n = S (S (S (S (S n')))) /\ In (d| (F1 *** F2) @ w0 |) (LEncode Gamma) /\ 
seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (L ++ [F1 @ w0] ++ [F2 @ w0])) (> []))) .
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H;unfold BODY_RTENSORL in H.
 
    CleanContext.
    destruct H0;CleanContext.
    -
      FLLInversionAll.
      left.
      eexists n0.
      eexists x0;split;auto.
      split;eauto.
      unfold REncode.
      unfold LEncode.
      rewrite map_app.
      simpl. 
      LLExact H9.
    - 
      FLLInversionAll.
      right.  
      eexists n0;split;auto.
      split;auto.
      unfold LEncode.
      unfold REncode. 
      do 2 rewrite map_app.
      simpl. 
      LLExact H9. 
  Qed.
   
  Theorem RTENSORLInv2:  forall n Gamma F G F1 F2 w w0 v L ,
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (F @ w ::L)) (>> RTENSORL F1 F2 w0) ->
         (
(exists n', n = S (S (S (S (S n')))) /\  F = (F1 *** F2) /\ w = w0 /\ 
(seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (L ++ [F1 @ w0] ++ [F2 @ w0])) (> []))) \/

(exists n' X, n = S (S (S (S (S n')))) /\ Permutation L ((F1 *** F2) @ w0 :: X) /\ 
(seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: d| F @ w | :: LEncode (X ++ [F1 @ w0] ++ [F2 @ w0])) (> []))) \/ 

(exists n', n = S (S (S (S (S n')))) /\In (d| (F1 *** F2) @ w0 |) (LEncode Gamma) /\ 
seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) ::  d| F @ w | :: LEncode (L ++ [F1 @ w0] ++ [F2 @ w0])) (> []))) .
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H;unfold BODY_RTENSORL in H.
 
    CleanContext.
    destruct H0;CleanContext.
    -
    apply PProp_perm_select in H.
    destruct H;
    CleanContext...
      +
      left.
      FLLInversionAll.
      inversion H...
      assert(Permutation (LEncode L) (LEncode x0)) by apply (Permutation_map _ H1).
      rewrite <- H0 in H10.
      eexists n0;split;auto.
      split;eauto.
      split;eauto.
      LLExactMap H10.
      +
      FLLInversionAll.
      right. left.
      
      eexists n0.
      eexists x1.
      split;eauto.
      split;eauto.
      rewrite H in H10.
      LLExactMap H10.
    - 
      FLLInversionAll.
      right. right. 
      eexists n0;split;auto.
      split;auto.
      LLExactMap H9. 
  Qed.

    
  Theorem RTENSORRInv1:  forall n Gamma G F1 F2 v w0 L ,
      isOLFormulaL Gamma -> isOLFormulaL L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RTENSORR F1 F2 w0) ->
      exists n' M N,
          n = S (S (S (S n'))) /\ Permutation L (M ++ N) /\ G = F1 *** F2 /\ v = w0
          /\ seqN OLTheory n' (LEncode Gamma) (LEncode M ++ [u| F1 @ w0 |]) (> [])
          /\ seqN OLTheory n' (LEncode Gamma) (LEncode N ++ [u| F2 @ w0 |]) (> []) .
  Proof with solveF.
    intros.
    apply FocusinRightAtom in H1;auto;unfold BODY_RTENSORR in H1.
    CleanContext.
    FLLInversionAll.
    CleanContext.

    symmetry in H4.
    apply Permutation_map_inv in H4.
    destruct H4.
    destruct H1.
    symmetry in H1.
    apply map_eq_app in H1.
    do 2 destruct H1.
    destruct H1;subst.
    destruct H3;subst.
    do 3 eexists;
    split;eauto;
    split;eauto;
    split;eauto;
    split;eauto.
  Qed.

  
  Theorem RTENSORRInv2:  forall n Gamma F G F1 F2 v w w0 L ,
  isOLFormula (F @ w) -> 
      isOLFormulaL Gamma -> isOLFormulaL L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (F @ w :: L)) (>> RTENSORR F1 F2 w0) ->
      (exists n' X1 X2 ,
          n = S (S (S (S n'))) /\ Permutation L (X1 ++ X2) /\ G = F1 *** F2 /\  v = w0
          /\ seqN OLTheory n' (LEncode Gamma) (LEncode (F @ w :: X1) ++ [u| F1 @ w0 |]) (> [])
          /\ seqN OLTheory n' (LEncode Gamma) (LEncode X2 ++ [u| F2 @ w0 |]) (> [])) \/
     (exists n' X1 X2 ,
          n = S (S (S (S n'))) /\ Permutation L (X1 ++ X2) /\ G = F1 *** F2 /\ v = w0
          /\ seqN OLTheory n' (LEncode Gamma) (LEncode X1 ++ [u| F1 @ w0 |]) (> [])
          /\ seqN OLTheory n' (LEncode Gamma) (LEncode (F @ w :: X2) ++ [u| F2 @ w0 |]) (> [])) .
  Proof with solveF.
    intros.
    apply FocusinRightAtom in H2;auto;unfold BODY_RTENSORR in H2.
    CleanContext.
    
    FLLInversionAll.
    CleanContext.
    symmetry in H5.
    assert(d| F @ w | :: map (fun x : uexp => d| x |)  L = LEncode ( F @ w :: L)).
    simpl;auto.
    rewrite H2 in H5.
    apply Permutation_map_inv in H5.
    destruct H5 as [x H5'];destruct H5'.
    symmetry in H3.
    apply map_eq_app in H3.
    do 3 destruct H3.
    destruct H5;subst.
    symmetry in H4. 
    apply PProp_perm_select' in H4.
    destruct H4;subst;[left|right].
    *    
    do 2 destruct H3;subst.
    rewrite H3 in H13.    
    eexists n.
    eexists x.
    eexists x1;split;eauto.
    split;eauto. symmetry;auto.
    *    
    do 2 destruct H3;subst.
    rewrite H3 in H14.    
    eexists n.
    eexists x0.
    eexists x;split;eauto.
    split;eauto. symmetry;auto.    
Qed.


Theorem RCOPYInv1: forall n Gamma G v L F w0,
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>>RCOPY F w0) ->
      (exists n',
        n = S ( S ( S n')) /\ 
        seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode L) (> [])) \/
        
        (exists n', n = S ( S ( S n'))  /\In (d|  F @ w0 |) (LEncode Gamma) /\ 
        seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (L ++
        [ F @ w0])) (> [])).
  Proof with solveF.
      intros.
      apply FocusinLeftAtom in H.
      CleanContext.
      decompose [or] H0;clear H0;CleanContext.
      -
       FLLInversionAll.
       left.
       assert(Permutation (LEncode L) (LEncode (F @ w0 :: x0))) by apply (Permutation_map _ H).
       assert(seqN OLTheory n0 (LEncode Gamma)
       (u| G @ v | :: LEncode (F @ w0 :: x0)) (> [])).
       LLExactMap H8.
       rewrite <- H0 in H1. 
       eexists n0;split; eauto.
       -
        FLLInversionAll.
        right.
        eexists n0;split; eauto.
        split;auto.
        LLExactMap H8.  
 Qed.
 
 Theorem RCOPYInv2: forall n Gamma G v L J F w w0,
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (J @ w :: L)) (>>RCOPY F w0) ->
      (exists n',
        n = S ( S ( S n')) /\ F = J /\ w = w0 /\
        seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (J @ w :: L)) (> [])) \/
       (exists n',
        n = S ( S ( S n')) /\  
        seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (J @ w :: L)) (> []))  \/
        (exists n', n = S ( S ( S n'))  /\In (d|  F @ w0 |) (LEncode Gamma) /\ 
        seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode ((J @ w :: L) ++
        [ F @ w0])) (> [])).   
  Proof with solveF.
      intros.
      apply FocusinLeftAtom in H.
      CleanContext.
      decompose [or] H0;clear H0;CleanContext.
      -
        apply PProp_perm_select in H.
       destruct H;CleanContext.
       *
       left. 
       FLLInversionAll.
       inversion H;subst.
       assert(Permutation (LEncode L) (LEncode x0)) by apply (Permutation_map _ H1).
       rewrite <- H0 in H9.
       eexists n0;split; eauto.
       split; eauto.
       split; eauto.
       LLExactMap H9.
       *
       right. left.
       FLLInversionAll.
       assert(Permutation (LEncode L) (LEncode (F @ w0 :: x1))) by apply (Permutation_map _ H1).
       assert(Permutation (LEncode x0) (LEncode (J @ w :: x1))) by apply (Permutation_map _ H).
       rewrite  H2 in H9.
       eexists n0;split; eauto.
       simpl. rewrite H0.
       LLExactMap H9.
     -
     right. right.
     FLLInversionAll.
     eexists n0;split; eauto. 
     split; eauto.
     LLExactMap H8.    
 Qed.
  
  Theorem RALLLInv1: forall n Gamma G v L FX w0,
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RALLL FX w0) ->
      (exists n' X t,
        n = S (S ( S ( S n'))) /\  Permutation L ((ALL FX) @ w0 :: X) /\
         proper t /\ uniform_oo (fun x => d| (FX x) @ w0 |) /\
        seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (X ++
        [(FX t) @ w0 ])) (> [])) \/
        
        (exists n' t, n = S (S ( S ( S n')))  /\ In (d| (ALL FX) @ w0 |) (LEncode Gamma) /\ 
         proper t /\ uniform_oo (fun x  => d| (FX x) @ w0 |) /\
        seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (L ++
        [ (FX t) @ w0])) (> [])).
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H;unfold BODY_RALLL in H.
    CleanContext.
    destruct H0.
    -
    CleanContext.
    FLLInversionAll.
    left.
    unfold LEncode.
    eexists n.
    eexists x0. 
    exists t. 
    split; eauto.
       rewrite map_app.
       split; eauto.
 
    -
    CleanContext.
    FLLInversionAll.
    right.
    eexists n.
    exists t. 
    
    split; eauto.
     unfold LEncode.
     rewrite map_app.
split; eauto.     
  Qed.
 
 
   Theorem RALLLInv2: forall n Gamma G F w v L FX w0,
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (F @ w::L)) (>> RALLL FX w0) ->
       (exists n' t,
        n = S (S ( S ( S n'))) /\  F = ALL FX /\ w = w0 /\ 
         proper t /\ uniform_oo (fun x => d| (FX x) @ w0 |) /\
        seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (L ++
        [(FX t) @ w0 ])) (> [])) \/
        
      (exists n' X t,
        n = S (S ( S ( S n'))) /\  Permutation L ((ALL FX) @ w0 :: X) /\
         proper t /\ uniform_oo (fun x => d| (FX x) @ w0 |) /\
        seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode ((F @ w :: X) ++
        [(FX t) @ w0 ])) (> [])) \/
        
        (exists n' t, n = S (S ( S ( S n')))  /\ In (d| (ALL FX) @ w0 |) (LEncode Gamma) /\ 
         proper t /\ uniform_oo (fun x  => d| (FX x) @ w0 |) /\
        seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode ((F @ w :: L) ++
        [ (FX t) @ w0])) (> [])).
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H;unfold BODY_RALLL in H.
    CleanContext.
    destruct H0.
    -
    CleanContext.
    apply PProp_perm_select in H.
    destruct H;CleanContext.
    * left. 
      inversion H...
      FLLInversionAll. 
      CleanContext.
      unfold REncode.
      assert(Permutation (LEncode L) (LEncode x0)).
      eapply Permutation_map in H1. exact H1.
      rewrite <- H0 in H11. 
      eexists n;
      exists t; split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      LLExactMap H11.
    * right. left.
      assert(Permutation (LEncode x0) (LEncode (F @ w :: x1))).
      eapply Permutation_map in H. exact H.
      rewrite H2 in H0.
      FLLInversionAll.
      eexists n;
      eexists x1;
      exists t; 
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      LLExactMap H12.
    -
    right. right.
    CleanContext.
    FLLInversionAll.
    eexists n;
    exists t; 
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    LLExactMap H10.    
  Qed.
   
 Theorem RALLRInv1: forall n Gamma G v L FX w0,
 isOLFormulaL Gamma -> isOLFormulaL L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RALLR FX w0) ->
      (exists n',
        n = (S ( S ( S n'))) /\  G = ALL FX /\ v = w0 /\ uniform_oo
        (fun x => u| (FX x) @ w0 |) /\
        forall x,
          proper x -> seqN OLTheory n' (LEncode Gamma) (LEncode L) (> [u| (FX x) @ w0 |])).
  Proof with solveF.
    intros.
    apply FocusinRightAtom in H1;auto;unfold BODY_RALLR in H1.
    CleanContext.
    FLLInversionAll.
    eexists n0;split; eauto.     
  Qed.
 
  Theorem RALLRInv2: forall n Gamma G F v L FX w w0,
  isOLFormula (F @ w) ->
 isOLFormulaL Gamma -> isOLFormulaL L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (F @ w::L)) (>> RALLR FX w0) ->
      (exists n',
        n = (S ( S ( S n'))) /\  G = ALL FX /\ v = w0 /\ uniform_oo
        (fun x => u| (FX x) @ w0 |) /\
        forall x,
          proper x -> seqN OLTheory n' (LEncode Gamma) (d| F @ w |::LEncode L) (> [u| (FX x) @ w0 |])).
  Proof with solveF.
    intros.
    apply FocusinRightAtom in H2;auto;unfold BODY_RALLR in H2.
    CleanContext.
    FLLInversionAll.
    eexists n0;split; eauto.     
  Qed.
        
               
Theorem RARROWLInv1: forall n Gamma G v L FW w0,
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RARROWL FW w0) ->
      (exists n' X,
        n = S ( S ( S n')) /\ Permutation L ((ARROW FW) @ w0 :: X) /\
        seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (X ++
        [(FW w0) @ w0 ])) (> [])) \/
        
        (exists n', n = S ( S ( S n'))  /\In (d| (ARROW FW) @ w0 |) (LEncode Gamma) /\ 
        seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (L ++
        [ (FW w0) @ w0])) (> [])).
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H;unfold BODY_RARROWL in H.
    CleanContext.
    destruct H0.
    -
    CleanContext.
    FLLInversionAll.
    left.
    eexists n0.
    eexists x0;split; eauto.
       split; eauto.
    LLExactMap H8.
    -
    CleanContext.
    
FLLInversionAll.
    right.
    eexists n0;split; eauto.
     unfold LEncode.
     rewrite map_app.
split; eauto.     
  Qed.
    
Theorem RARROWLInv2: forall n Gamma F G w v L FW w0,
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (F @ w :: L)) (>> RARROWL FW w0) ->
(exists n', n = S ( S ( S n')) /\ F  = (ARROW FW) /\ w = w0 /\ 
(seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (L ++ [(FW w0) @ w0])) (> []))) \/
(exists n' Y, n = S ( S ( S n')) /\ Permutation L ((ARROW FW) @ w0 :: Y) /\ 
(seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode ((F @ w :: Y) ++ [(FW w0) @ w0])) (> []))) \/ 
(exists n', n = S ( S ( S n')) /\In (d| (ARROW FW) @ w0 |) (LEncode Gamma) /\ 
seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode ((F @ w ::L) ++ [(FW w0) @ w0])) (> [])) .

  Proof with solveF.
 intros.
    apply FocusinLeftAtom in H;unfold BODY_RARROWL in H.
 
    CleanContext.
    destruct H0;CleanContext.
    -
    apply PProp_perm_select in H.
    destruct H;
    CleanContext...
      +
      FLLInversionAll.
      left.
      inversion H...
      assert(Permutation (LEncode L) (LEncode x0)) by apply (Permutation_map _ H1).
      rewrite <- H0 in H9.
      eexists n0;split;auto.
      split;eauto.
      split;eauto.
      LLExactMap H9.
      +
      FLLInversionAll.
      CleanContext.
      right. left.
      rewrite H in H9.
      eexists n0.
      eexists x1;split;auto.
      split;eauto.
      
      LLExactMap H9.
    - 
      FLLInversionAll.
      right. right. 
      eexists n0;split;auto.
      split;auto.
      LLExactMap H8. 
  Qed.
     
  Theorem RARROWRInv1: forall n Gamma G v L FW w0,
  isOLFormulaL Gamma -> isOLFormulaL L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RARROWR FW w0) ->
      exists n',
        n = S ( S ( S n')) /\
        G = (ARROW FW) /\ v = w0 /\
        seqN OLTheory n' (LEncode Gamma) (LEncode L ++
        [u| (FW w0) @ w0 |]) (> []) .
  Proof with solveF.
    intros.
    apply FocusinRightAtom in H1;auto;unfold BODY_RARROWR in H1.
    CleanContext.
    FLLInversionAll.
    CleanContext.
    
    eexists;split; eauto.
  Qed.
 
   Theorem RARROWRInv2: forall n Gamma F G v L FW w w0,
    isOLFormula (F @ w) ->
  isOLFormulaL Gamma -> isOLFormulaL L ->
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (F @ w :: L)) (>> RARROWR FW w0) ->
      exists n',
        n = S ( S ( S n')) /\
        G = (ARROW FW) /\ v = w0 /\
        seqN OLTheory n' (LEncode Gamma) ((d| F @ w | :: LEncode L) ++
        [u| (FW w0) @ w0 |]) (> []) .
  Proof with solveF.  
    intros.
    apply RARROWRInv1 in H2;auto;unfold BODY_RARROWR in H2.
  Qed.
  
Theorem RATLInv1:  forall n Gamma G F w0 w1 v L ,
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RATL F w1 w0) ->
         (
(exists n' X, n = (S (S (S n'))) /\ Permutation  L ((F AT w1) @ w0 :: X)  /\ 
  (seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (X ++ [F @ w1])) (> []))) \/
(exists n', n = (S (S (S n'))) /\ In (d| (F AT w1) @ w0|) (LEncode Gamma) /\ 
  seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (L ++ [F @ w1])) (> []))) .
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H;unfold BODY_RATL in H.
 
    CleanContext.
    destruct H0;CleanContext.
    -
      FLLInversionAll. CleanContext.
      left.
      eexists n0.
      eexists x0;split;auto.
      split;eauto.
      unfold REncode.
      unfold LEncode.
      rewrite map_app.
      LLExact H8.
    - 
      FLLInversionAll.
      right.  
      eexists n0;split;auto.
      split;auto.
      unfold LEncode.
      unfold REncode. 
      rewrite map_app.
      LLExact H8. 
  Qed.
  
  
  Theorem RATLInv2:  forall n Gamma F G J w w0 w1 v L ,
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (J @ w ::L)) (>> RATL F w1 w0) ->
         (
(exists n', n = (S (S (S n'))) /\ J = (F AT w1)  /\ w = w0 /\ 
  (seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode (L ++ [F @ w1])) (> []))) \/
(exists n' Y, n = (S (S (S n'))) /\ Permutation L ((F AT w1) @ w0:: Y) /\ 
  (seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode ((J @ w :: Y) ++ [F @ w1])) (> []))) \/ 
(exists n', n = (S (S (S n'))) /\In (d| (F AT w1) @ w0 |) (LEncode Gamma) /\ 
  seqN OLTheory n' (LEncode Gamma) (REncode (G @ v) :: LEncode ((J @ w ::L) ++ [F @ w1])) (> []))) .
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H;unfold BODY_RATL in H.
 
    CleanContext.
    destruct H0;CleanContext.
    -
    apply PProp_perm_select in H.
    destruct H;
    CleanContext...
      +
      FLLInversionAll.
      left.
      inversion H...
      assert(Permutation (LEncode L) (LEncode x0)) by apply (Permutation_map _ H1).
      rewrite <- H0 in H9.
      eexists n0;split;auto.
      split;eauto.
      split;eauto.
      LLExactMap H9.
      +
      FLLInversionAll. CleanContext.
      right. left.
      rewrite H in H9.
      eexists n0.
      eexists x1;split;auto.
      split;eauto.
      LLExactMap H9.
    - 
      FLLInversionAll.
      right. right. 
      eexists n0;split;auto.
      split;auto.
      LLExactMap H8. 
  Qed.
   
   Theorem RATRInv1:  forall n Gamma G F w0 w1 v L ,
      isOLFormulaL Gamma -> 
      isOLFormulaL L -> 
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RATR F w1 w0) ->
         ( (exists n', n = S (S (S n')) /\
      G = F AT w1 /\ v = w0 /\ seqN OLTheory n' (LEncode Gamma) (LEncode L ++ [u| F @ w1 |]) (> []))) .
  Proof with solveF.
    intros.
    apply FocusinRightAtom in H1;auto;unfold BODY_RATR in H1.
 
    CleanContext. 
    FLLInversionAll.
    eexists n0;split;auto.
  Qed.
   
   Theorem RATRInv2:  forall n Gamma G F J w w0 w1 v L ,
     isOLFormula (J @ w) ->
      isOLFormulaL Gamma -> 
      isOLFormulaL L -> 
      seqN OLTheory n (LEncode Gamma) (REncode (G @ v) :: LEncode (J @ w ::L)) (>> RATR F w1 w0) ->
         (
(exists n', n = S (S (S n')) /\
      G = F AT w1 /\ v = w0 /\ seqN OLTheory n' (LEncode Gamma) (LEncode (J @ w ::L) ++ [u| F @ w1 |]) (> []))) .
  Proof with solveF.
    intros.
    apply RATRInv1 in H2...

  Qed.
  
 
 Ltac LLExactMap' H :=
  let G := type of H in
  match G with
  | seq ?T ?Gamma ?Delta ?X =>
      match goal with
      | |- seq T ?Gamma' ?Delta' X =>
            apply exchangeCC with (CC := Gamma); auto; try permMap;
             apply exchangeLC with (LC := Delta); auto; 
             try permMap
      end
  end; auto.
       
   Ltac solveBANGR :=
    match goal with
    | [ H: seqN OLTheory ?n ?G (REncode ?F1 :: LEncode (?F2 :: ?L)) (>> RBANGR ?F3 ?w) |- _ ] => 
        apply BANGRInv2 in H;auto;
        contradiction         
    end.

Ltac solveBANGL1 := 
 match goal with 
  | [  H1 : seqN _ ?x (LEncode ?Gamma ++ [d| ?F @ ?w1 |]) (REncode (?FC @ ?w) :: LEncode ?x0 )(> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      IH: CutDefinition ?n' ?h ,
       H: Permutation ?D2 ((!! ?F) @ ?w1 :: ?x0) 
     |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         apply (rewL2 _ _ H);auto;decide3 (RBANGL F w1);autounfold with enc;
         tensor [d| (!! F) @ w1 |]  (G :: LEncode D1 ++ LEncode x0);
         LLPermMap(LEncode (Gamma ++ [ F @ w1 ]));
         LLPermMap(G :: LEncode (D1 ++ x0));
         eapply IH with (h1:=S n0) (h2:=x) (m:=S n0+x) (w:=w) (FCut:=FC);solveF;
         [ | LLPermMap([d| F @ w1 |] ++ LEncode Gamma);
             apply weakeningGenN;
             LLExactMap H2 | LLExactMap H1 | ]  
    end.
 
Ltac solveBANGL2 :=
      match goal with 
  | [  H1 : seqN _ ?x (LEncode ?Gamma ++ [d| ?F @ ?w1 |]) (REncode (?FC @ ?w) :: LEncode ?x0 )(> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      IH: CutDefinition ?n' ?h   
     |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         decide3 (RBANGL F w1);autounfold with enc;
         tensor  (@nil oo) (G :: LEncode (D1 ++ D2));
         LLPermMap(LEncode (Gamma ++ [ F @ w1 ]));
         eapply IH with (h1:=S n0) (h2:=x) (m:=S n0+x) (w:=w) (FCut:=FC);solveF;
         [ LLPermMap([d| F @ w1 |] ++ LEncode Gamma);
             apply weakeningGenN;
             LLExactMap H2 | LLExactMap H1 | ] 
    end.
    
Ltac solveBANGL :=
    match goal with  
    | [ H: seqN OLTheory ?m ?G (?FC :: LEncode ?D2) (>> RBANGL ?F ?w1) |- _ ] => 
        apply BANGLInv1 in H;auto;
        decompose [or] H;clear H;CleanContext;[solveBANGL1;try easyF | solveBANGL2;try easyF] 
    end.
    
   
   Ltac solveINIT :=
  match goal with
    | [ H: seqN OLTheory ?m ?G (REncode ?F :: LEncode ?D2) ?X |-
           seq (OLTheoryCut ?n) ?G (REncode ?F :: LEncode ?D2) ?X ] => 
         apply WeakTheory with (theory:= OLTheory);
         auto using TheoryInclusion;
         apply seqNtoSeq in H;
         exact H
    | [ H: ?FC :: ?D1 = [?F] |- _ ] => 
         inversion H;subst;simpl;solveINIT
    | [ H: seqN OLTheory ?m ?G (REncode ?F :: LEncode (?FC::?D1)) (>> RINIT ?F1 ?w) |- _ ] => 
        apply RINITInv1 in H;auto; 
        decompose [and or] H;subst;solveF;solveINIT          
    end.
 
Ltac solveRTENSORR1 :=
    match goal with 
  | [ Hseq2 : seqN _ (S ?n1) ?G (REncode (?FCut @ ?w) :: LEncode ?D2) (> []),
        H1: seqN _ ?x ?G (LEncode ?x1 ++ [u| ?G0 @ ?w0 |]) (> []),
        H2: seqN _ ?x ?G (LEncode (?FCut @ ?w :: ?x0) ++ [u| ?F1 @ ?w0 |]) (> []),
        IH: CutDefinition ?n' ?h
        |- seq _ ?G (REncode (?F1 @ ?w0) :: LEncode (?x0 ++ ?D2)) (> []) ] => 
        eapply IH with (h1:=x) (h2:=S n1) (m:=x+S n1) (w:=w) (FCut:=FCut);solveF;[ | |
        LLExactMap H2] 
    | [ H: seqN _ ?x ?G
       (LEncode ?x1 ++ [u| ?G0 @ ?w0 |]) 
       (> []) |- seq ?th ?G (LEncode (?x0 ++ ?x1) ++ LEncode ?D2) (>> u| ?F1 @ ?w0 | ** u| ?G0 @ ?w0 |) ] => 
         tensor (LEncode x0++ LEncode D2) (LEncode x1); try permMap;[LLPermMap(REncode ( F1 @ w0):: LEncode (x0 ++ D2));solveRTENSORR1 | apply WeakTheory with (theory:= OLTheory);
        auto using TheoryInclusion; apply seqNtoSeq in H; LLExactMap' H]
       | [ H: Permutation ?D1 (?x0 ++ ?x1) |- seq ?th ?G (REncode ((?F1 *** ?G0) @ ?w0) :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         apply (rewL1 _ _ H);decide3 (RTENSORR F1 G0 w0);autounfold with enc;
         tensor [u| (F1 *** G0) @ w0 |]  (LEncode (x0 ++ x1)++ LEncode D2);auto;solveRTENSORR1         
    end.
    
 Ltac solveRTENSORR2 :=
       match goal with 
     | [ Hseq2 : seqN _ (S ?n1) ?G (REncode (?FCut @ ?w) :: LEncode ?D2) (> []),
        H1: seqN _ ?x ?G (LEncode ?x0 ++ [u| ?F1 @ ?w0 |]) (> []),
        H2: seqN _ ?x ?G (LEncode (?FCut @ ?w :: ?x1) ++ [u| ?G0 @ ?w0 |]) (> []),
        IH: CutDefinition ?n' ?h
        |- seq _ ?G (REncode (?G0 @ ?w0) :: LEncode (?x1 ++ ?D2)) (> []) ] => 
        eapply IH with (h1:=x) (h2:=S n1) (m:=x+S n1) (w:=w) (FCut:=FCut);solveF;[ | |
        LLExactMap H2]        
    | [ H: seqN _ ?x ?G
       (LEncode ?x0 ++ [u| ?F1 @ ?w0 |]) 
       (> []) |- seq ?th ?G (LEncode (?x0 ++ ?x1) ++ LEncode ?D2) (>> u| ?F1 @ ?w0 | ** u| ?G0 @ ?w0 |) ] => 
         tensor (LEncode x0) (LEncode x1++ LEncode D2); try permMap;[ apply WeakTheory with (theory:= OLTheory);
        auto using TheoryInclusion; apply seqNtoSeq in H; LLExactMap' H | LLPermMap(REncode ( G0 @ w0):: LEncode (x1 ++ D2));solveRTENSORR2]         
    
     | [ H: Permutation ?D1 (?x0 ++ ?x1) |- seq ?th ?G (REncode ((?F1 *** ?G0) @ ?w0) :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         apply (rewL1 _ _ H);decide3 (RTENSORR F1 G0 w0);autounfold with enc;
         tensor [u| (F1 *** G0) @ w0 |]  (LEncode (x0 ++ x1)++ LEncode D2);auto;solveRTENSORR2 end.
 

               
 Ltac solveRTENSORR :=
  match goal with   

    | [ H: seqN OLTheory ?m ?G (REncode ?F :: LEncode (?FC::?D1)) (>> RTENSORR ?F1 ?G0 ?w0) |- _ ] => 
        apply RTENSORRInv2 in H;auto;
        decompose [or] H;clear H;CleanContext;[solveRTENSORR1;try easyF | solveRTENSORR2;try easyF]          
    end.

 Ltac solveRARROWL1 := 
 match goal with 
  | [  H1 : seqN _ ?x _ (REncode (?FC @ ?w) :: LEncode (?x0 ++ [(?FW ?w1) @ ?w1]))(> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      IH: CutDefinition ?n' ?h ,
       H: Permutation ?D2 ((ARROW ?FW) @ ?w1 :: ?x0) 
     |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         apply (rewL2 _ _ H);auto;decide3 (RARROWL FW w1);autounfold with enc;
         tensor [d| (ARROW FW) @ w1 |]  (G :: LEncode D1 ++ LEncode x0);
         LLPermMap(G :: LEncode (D1 ++ (x0++[(FW w1) @ w1])));
          eapply IH with (h1:=S n0) (h2:=x) (m:=S n0 + x) (w:=w) (FCut:=FC);solveF 
    end.
    
 Ltac solveRARROWL2 := 
       match goal with 
 | [  H1 : seqN _ ?x _ (REncode (?FC @ ?w) :: LEncode (?x0 ++ [(?FW ?w1) @ ?w1]))(> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      IH: CutDefinition ?n' ?h
      |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         decide3 (RARROWL FW w1);autounfold with enc;
         tensor (@nil oo)  (G :: LEncode (D1 ++ D2));autounfold with enc;
         LLPermMap(G:: LEncode (D1 ++ (D2++[(FW w1) @ w1])));
         eapply IH with (h1:=S n0) (h2:=x) (m:=S n0 + x) (w:=w) (FCut:=FC);solveF   
 end.


 Ltac solveRARROWL :=   
   match goal with  
    | [ H: seqN OLTheory ?m ?G (?FC :: LEncode ?D2) (>> RARROWL ?FW ?w1) |- _ ] => 
        apply RARROWLInv1 in H;auto; 
        decompose [or] H;clear H;CleanContext;[solveRARROWL1;try easyF | solveRARROWL2;try easyF] 
    end.
    
   
Ltac solveRTENSORL1 :=
   match goal with 
  | [ H1 : seqN _ ?x _ (REncode (?FC @ ?w) :: LEncode (?x0 ++ [?F @ ?w1] ++ [?G1 @ ?w1]))(> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      IH: CutDefinition ?n' ?h ,
       H: Permutation ?D2 ((?F *** ?G1) @ ?w1 :: ?x0) 
     |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         apply (rewL2 _ _ H);auto;decide3 (RTENSORL F G1 w1);autounfold with enc;
         tensor [d| (F *** G1) @ w1 |]  (G :: LEncode D1 ++ LEncode x0);
         LLPermMap (G :: LEncode (D1 ++ (x0++[F @ w1] ++ [G1 @ w1])));
         eapply IH with (h1:=S n0) (h2:=x) (m:= S n0 + x) (w:=w) (FCut:=FC);solveF        
    end.
    
 Ltac solveRTENSORL2 :=
       match goal with 
    | [ H1 : seqN _ ?x _ (REncode (?FC @ ?w) :: LEncode (?x0 ++ [?F @ ?w1] ++ [?G1 @ ?w1]))(> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      IH: CutDefinition ?n' ?h
      |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         decide3 (RTENSORL F G1 w1);autounfold with enc;
         tensor (@nil oo)  (G :: LEncode (D1 ++ D2));
         LLPermMap (G :: LEncode (D1 ++ (D2++[F @ w1] ++ [G1 @ w1])));
         eapply IH with (h1:=S n0) (h2:=x) (m:= S n0 + x) (w:=w) (FCut:=FC);solveF 
     end.
          
 Ltac solveRTENSORL :=
    match goal with   

    | [ H: seqN OLTheory ?m ?G (REncode ?FC :: LEncode ?D2) (>> RTENSORL ?F ?G1 ?w1) |- _ ] => 
        apply RTENSORLInv1 in H;auto;
        decompose [or] H;clear H;CleanContext;[solveRTENSORL1;try easyF | solveRTENSORL2;try easyF]       
    end.
    
 Ltac solveRATL1 :=  
 match goal with 
  | [  H1 : seqN _ ?x _ (REncode (?FC @ ?w) :: LEncode (?x0 ++ [?F @ ?v0]))(> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      IH: CutDefinition ?n' ?h ,
       H: Permutation ?D2 ((?F AT ?v0) @ ?w1 :: ?x0) 
     |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         apply (rewL2 _ _ H);auto;decide3 (RATL F v0 w1);autounfold with enc;
         tensor [d| (F AT v0) @ w1 |]  (G :: LEncode D1 ++ LEncode x0);
         LLPermMap(G :: LEncode (D1 ++ (x0++[F @ v0])));
          eapply IH with (h1:=S n0) (h2:=x) (m:=S n0 + x) (w:=w) (FCut:=FC);solveF 
    end.

 Ltac solveRATL2 :=  
       match goal with 
 | [  H1 : seqN _ ?x _ (REncode (?FC @ ?w) :: LEncode (?x0 ++ [?F @ ?v0]))(> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      H3: In (d| (?F AT ?v0) @ ?w1 |) ?Gamma,
      IH: CutDefinition ?n' ?h
      |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         decide3 (RATL F v0 w1);autounfold with enc;
         tensor (@nil oo)  (G :: LEncode (D1 ++ D2));
         LLPermMap(G:: LEncode (D1 ++ (D2++[F @ v0])));
         eapply IH with (h1:=S n0) (h2:=x) (m:=S n0 + x) (w:=w) (FCut:=FC);solveF   
    end.

       
 Ltac solveRATL :=    
match goal with  
    | [ H: seqN OLTheory ?m ?G (?FC :: LEncode ?D2) (>> RATL ?F ?v0 ?w1) |- _ ] => 
        apply RATLInv1 in H;auto;
        decompose [or] H;clear H;CleanContext;[solveRATL1;try easyF | solveRATL2;try easyF]     
    end.
  
   
Ltac solveRIMPR :=
  match goal with   
  | [ H1 : seqN _ ?x ?G (LEncode (?FCut @ ?w :: ?D1) ++ [d| ?F1 @ ?w0 |; u| ?G0 @ ?w0 |])(> []),
      H2 : seqN _ (S ?n1) ?G (REncode (?FCut @ ?w) :: LEncode ?D2)(> []),
      IH: CutDefinition ?n' ?h 
      |- seq ?th ?G (REncode ((?F1 --o ?G0) @ ?w0) :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         decide3 (RIMPLR F1 G0 w0);autounfold with enc;
         tensor [u| (F1 --o G0) @ w0 |]  (LEncode (D1 ++ D2));auto;
         LLPermMap(REncode ( G0 @ w0):: LEncode ((D1 ++ [F1 @ w0]) ++ D2));
         eapply IH with (h1:=x) (h2:=S n1) (m:=x+S n1) (w:=w) (FCut:=FCut);solveF;[ | | LLExactMap H1 ]         
 
  | [ H: seqN OLTheory ?m ?G (REncode ?F :: LEncode (?FC::?D1)) (>> RIMPLR ?F1 ?G0 ?w0) |- _ ] => 
        apply RIMPLRInv2 in H;auto;CleanContext;solveRIMPR         
    end;try easyF.
    
Ltac solveRATR := 
   match goal with  
    | [ H1 : seqN _ ?x ?G (LEncode (?FCut @ ?w :: ?D1) ++ [u| ?F1 @ ?v0 |])(> []),
      H2 : seqN _ (S ?n1) ?G (REncode (?FCut @ ?w) :: LEncode ?D2)(> []),
      IH: CutDefinition ?n' ?h
     |- seq ?th ?G (REncode ((?F1 AT ?v0) @ ?w0) :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         decide3 (RATR F1 v0 w0);autounfold with enc;
         tensor [u| (F1 AT v0) @ w0 |]  (LEncode (D1 ++ D2));auto;
         LLPermMap(REncode ( F1 @ v0):: LEncode (D1 ++ D2));
         eapply IH with (h1:=x) (h2:=S n1) (m:=x+S n1) (w:=w) (FCut:=FCut);solveF;[ | LLExactMap H1 ] 
         
    | [ H: seqN OLTheory ?m ?G (REncode ?F :: LEncode (?FC::?D1)) (>> RATR ?F1 ?v0 ?w0) |- _ ] => 
        apply RATRInv2 in H;auto;CleanContext;solveRATR         
    end;try easyF.


Ltac solveRARROWR :=    
    match goal with 
  | [ H1 : seqN _ ?x ?G ((d| ?FCut @ ?w | :: LEncode ?D1) ++ [u| (?FW ?w0) @ ?w0 |])(> []),
      H2 : seqN _ (S ?n1) ?G (REncode (?FCut @ ?w) :: LEncode ?D2)(> []),
      IH: CutDefinition ?n' ?h
     |- seq ?th ?G (REncode ((ARROW ?FW) @ ?w0) :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         decide3 (RARROWR FW w0);autounfold with enc;
         tensor [u| (ARROW FW) @ w0 |]  (LEncode (D1 ++ D2));auto;
         LLPermMap(REncode ((FW w0) @ w0):: LEncode (D1 ++ D2));
         eapply IH with (h1:=x) (h2:=S n1) (m:=x+S n1) (w:=w) (FCut:=FCut);solveF;[ | LLExactMap H1 ] 
   | [ H: seqN OLTheory ?m ?G (REncode ?F :: LEncode (?FC::?D1)) (>> RARROWR ?FW ?w0) |- _ ] => 
        apply RARROWRInv2 in H;auto;CleanContext;solveRARROWR       
    end;try easyF.
    
 
 Ltac solveRALLR := 
  match goal with 
  | [ H1 : seqN _ ?x ?G ((d| ?FCut @ ?w | :: LEncode ?D1) ++ [u| (?FX ?x0) @ ?w0 |])(> []),
      H2 : seqN _ (S ?n1) ?G (REncode (?FCut @ ?w) :: LEncode ?D2)(> []),
      IH: CutDefinition ?n' ?h
     |- seq ?th ?G (LEncode (?D1 ++ ?D2) ++ [u| (?FX ?x0) @ ?w0 |]) (> []) ] => 
        LLPermMap(REncode ((FX x0) @ w0):: LEncode (D1 ++ D2));
      eapply IH with (h1:=x) (h2:=S n1) (m:=x+S n1) (w:=w) (FCut:=FCut);solveF;[ | LLExactMap H1 ] 
  | [ pX: proper ?x, H: forall x0, proper x0 -> _ |- _ ] => 
         specialize (H x pX);inversion H;subst;CleanContext;solveRALLR
 | [ H : _
     |- seq ?th ?G (REncode ((ALL ?FX) @ ?w0) :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         decide3 (RALLR FX w0);autounfold with enc;
         tensor [u| (ALL FX) @ w0 |]  (LEncode (D1 ++ D2));auto;solveRALLR
  | [ H: seqN OLTheory ?m ?G (REncode ?F :: LEncode (?FC::?D1)) (>> RALLR ?FX ?w0) |- _ ] => 
        apply RALLRInv2 in H;auto;CleanContext;solveRALLR      

  end;try easyF.
  
  Ltac solveRALLL1 :=  
     match goal with 
  | [  H1 : seqN _ ?x _ (REncode (?FC @ ?w) :: LEncode (?x0 ++ [(?FX ?x1)@ ?w1]))(> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      IH: CutDefinition ?n' ?h , H3: proper ?x1,
       H: Permutation ?D2 ((ALL ?FX) @ ?w1 :: ?x0) 
     |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         apply (rewL2 _ _ H);auto;decide3 (RALLL FX w1);autounfold with enc;
         tensor [d| (ALL FX) @ w1 |]  (G :: LEncode D1 ++ LEncode x0);
         existential x1;
         LLPermMap(G :: LEncode (D1 ++ (x0++[(FX x1) @ w1 ])));
         eapply IH with (h1:=S n0) (h2:=x) (m:=S n0 + x) (w:=w) (FCut:=FC);solveF
    end.

 Ltac solveRALLL2 := 
       match goal with 
 | [  H1 : seqN _ ?x _ (REncode (?FC @ ?w) :: LEncode (?D2 ++ [(?FX ?x1)@ ?w1]))(> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      H3: In (d| (ALL ?FX) @ ?w1 |) ?Gamma,
      IH: CutDefinition ?n' ?h
      |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         decide3 (RALLL FX w1);autounfold with enc;tensor (@nil oo)  (G :: LEncode (D1 ++ D2));
         existential x1;
         LLPermMap(G:: LEncode (D1 ++ (D2++[(FX x1) @ w1])));
         eapply IH with (h1:=S n0) (h2:=x) (m:=S n0 + x) (w:=w) (FCut:=FC);solveF   
    end.

 Ltac solveRALLL := 
  match goal with
  | [ H: seqN OLTheory ?m ?G (REncode ?F :: LEncode ?D) (>> RALLL ?FX ?w0) |- _ ] => 
      apply RALLLInv1 in H;auto;
      decompose [or] H;clear H; CleanContext;[solveRALLL1;try easyF | solveRALLL2;try easyF] 
  end.
    

Ltac solveRCOPY1 := 
  match goal with 
  | [  H1 : seqN _ (S ?n1) _ (REncode (?FC @ ?w) :: LEncode ?D2)(> []),
       H2 : seqN _ ?x _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
       IH: CutDefinition ?n' ?h  |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
       eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w) (FCut:=FC);solveF
    end.
   

Ltac solveRCOPY2 := 
  match goal with 
  | [  H1 : seqN _ (S ?n1) _ (REncode (?FC @ ?w) :: LEncode ?D2)(> []),
       H2 : seqN _ ?x _  (?G :: LEncode ((?FC @ ?w :: ?D1) ++ [?F1 @ ?w1]))(> []),
       IH: CutDefinition ?n' ?h |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
          decide3 (RCOPY F1 w1);autounfold with enc;
         tensor (@nil oo)  (G :: LEncode (D1 ++ D2));
          LLPermMap(G :: LEncode ((D1 ++ [F1 @ w1]) ++ D2 ));
       eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w) (FCut:=FC);solveF
    end.
    
  Ltac solveRCOPY1' := 
  match goal with 
  | [  H1 : seqN _ ?x _ (REncode (?FC @ ?w) :: LEncode ?D2 )(> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      IH: CutDefinition ?n' ?h 
     |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
          eapply IH with (h1:=S n0) (h2:=x) (m:=S n0 + x) (w:=w) (FCut:=FC);solveF

    end.
   

Ltac solveRCOPY2' := 
match goal with 
  | [  H1 : seqN _ ?x _ (REncode (?FC @ ?w) :: LEncode (?D2 ++ [?F @ ?w1]) )(> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      IH: CutDefinition ?n' ?h 
     |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
          decide3 (RCOPY F w1);autounfold with enc;
         tensor (@nil oo)  (G :: LEncode (D1 ++ D2));
          LLPermMap(G :: LEncode (D1 ++ (D2 ++ [ F @ w1])));
       eapply IH with (h1:=S n0) (h2:=x) (m:=S n0 + x) (w:=w) (FCut:=FC);solveF
    end.
    
 Ltac solveRCOPY :=    
   match goal with  
    | [ H: seqN OLTheory ?m ?G (?FC :: LEncode ?D2) (>> RCOPY ?F1 ?w1) |- _ ] => 
        apply RCOPYInv1 in H;auto;
        decompose [or] H;clear H;CleanContext;[solveRCOPY1;try easyF | solveRCOPY2;try easyF]   
    end.

Ltac solveRCOPY' := 
 match goal with 
| [ H: seqN OLTheory ?m ?G (?FC :: LEncode ?D2) (>> RCOPY ?F ?w1) |- _ ] => 
        apply RCOPYInv1 in H;auto;
        decompose [or] H;clear H;CleanContext;[solveRCOPY1';try easyF | solveRCOPY2';try easyF]   
end.



  Ltac solveRIMPLL1 := 
      match goal with 
  | [ H0 : seqN OLTheory ?x _ ((u| ?FC @ ?w | :: LEncode ?x1) ++ LEncode [?G1 @ ?w1]) (> []),  
      H1 : seqN OLTheory ?x _ (LEncode ?x0 ++ [u| ?F @ ?w1 |]) (> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      IH: CutDefinition ?n' ?h, 
       H: Permutation ?D2 (_ :: ?x0 ++ ?x1)
     |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
         apply (rewL2 _ _ H);auto;decide3 (RIMPLL F G1 w1);autounfold with enc;
         tensor [d| (F --o G1) @ w1 |]  (G :: LEncode D1 ++ LEncode (x0 ++ x1));
        tensor (LEncode x0)  (G :: LEncode (D1++x1)); 
        [permMap |
         apply WeakTheory with (theory:= OLTheory);auto; 
         apply seqNtoSeq in H1;
         LLExactMap' H1 |
         LLPermMap (G :: LEncode (D1 ++ (x1 ++ [G1 @ w1]))); 
          eapply IH with (h1:=S n0) (h2:=x) (m:=S n0 + x ) (w:=w) (FCut:=FC);solveF;
          [ | LLExactMap H0] 
          ] 
    end. 
   

Ltac solveRIMPLL2 := 
  match goal with 
 | [  H0 : seqN OLTheory ?x _ ((u| ?FC @ ?w | :: LEncode ?x1) ++ LEncode [?G1 @ ?w1]) (> []),  
      H1 : seqN OLTheory ?x _ (LEncode ?x0 ++ [u| ?F @ ?w1 |]) (> []),
      H2 : seqN _ (S ?n0) _  (?G :: LEncode ((?FC @ ?w) :: ?D1))(> []),
      H3: In (d| (?F --o ?G1) @ ?w1 |) ?Gamma,
      H4: Permutation ?D2 (?x0 ++ ?x1),
      IH: CutDefinition ?n' ?h
      |- seq _ _ (?G :: LEncode (?D1 ++ ?D2)) (> []) ] => 
          apply (rewL2 _ _ H4);
          decide3 (RIMPLL F G1 w1);
          tensor (@nil oo)  (G :: LEncode D1 ++ LEncode (x0 ++ x1));
          tensor (LEncode x0)  (G :: LEncode (D1++x1));[ permMap |
          apply WeakTheory with (theory:= OLTheory);solveF;
          apply seqNtoSeq in H1;
          LLExactMap' H1 |
          LLPermMap (G :: LEncode (D1 ++ (x1 ++ [G1 @ w1])));
          eapply IH with (h1:=S n0) (h2:=x) (m:=S n0 + x ) (w:=w) (FCut:=FC);solveF;
          [ | LLExactMap H0 ] ]
  end.         
    
 Ltac solveRIMPLL :=    
   match goal with  
    | [ H: seqN OLTheory ?m ?G (REncode ?FC :: LEncode ?D) (>> RIMPLL ?F ?G1 ?w1) |- _ ] => 
      apply RIMPLLInv1 in H;auto;
      decompose [or] H;clear H;CleanContext;[ solveRIMPLL1;try easyF | solveRIMPLL2;try easyF ]   
    end.


 Lemma LEncIsNotAsyncL : forall L, isNotAsyncL (LEncode L).
 Proof.
    induction L. 
    * 
    compute. eauto.
    *
    simpl.
    apply ForallCons;auto.
    intro Hn. inversion Hn.
 Qed.   
 
  Lemma NilIsNotAsyncL : isNotAsyncL [].
 Proof.
   unfold isNotAsyncL. easy.
 Qed. 
 
  Lemma REncIsNotAsync : forall G, Notasynchronous (REncode G).
 Proof.
    intros. 
    autounfold.
    assert(~ asynchronous (u| G |)).
    intro Hc; inversion Hc.
    intuition.
 Qed. 
 
   Lemma EncIsNotAsyncL : forall G L, isNotAsyncL (REncode G::LEncode L).
 Proof.
    intros.
    constructor;auto.
    apply REncIsNotAsync.
    apply LEncIsNotAsyncL.
 Qed.
 
  Lemma LEncIsFormulaL : forall L, isFormulaL (LEncode L).
 Proof.
    induction L. 
    * 
    compute. easy.
    *
    simpl.
    apply ForallCons;auto.
 Qed.   
 
  Lemma REncIsFormula : forall G, isFormula (REncode G).
 Proof.
    intros. 
    assert(isFormula (u| G |)) by constructor.
    intuition.
 Qed. 
 
  Lemma EncIsFormulaL : forall G L, isFormulaL (REncode G::LEncode L).
 Proof.
    intros.
    constructor;auto.
    apply REncIsFormula.
    apply LEncIsFormulaL.
 Qed. 
 
 Hint Resolve NilIsNotAsyncL LEncIsNotAsyncL REncIsNotAsync EncIsNotAsyncL LEncIsFormulaL REncIsFormula EncIsFormulaL :core. 
 
  Theorem AbsorptionAtom' :  forall n B M A X , In (d| A |) B -> seqN OLTheory n B  (d| A | :: M) X -> seqN OLTheory n B M X.
    Proof with solveF.
      induction n;intros ;inversion H0;subst;eauto;clear H0...
      + (* tensor: A+ is in N or in M0 *)
        symmetry in H2.
        apply PProp_perm_select' in H2.
        destruct H2.
        ++ (* A+  in H0 *)
          do 2 destruct H0.
          rewrite H0 in H3.
          apply IHn in H3...
          rewrite <- H1.
          tensor.
        ++ (* A+ in N *)
          do 2 destruct H0.
          rewrite H0 in H4.
          apply IHn in H4...
          rewrite <- H1.
          tensor.
      + (*dec1 *)
        apply IHn in H2...
        eapply in_cons with (a:=F)in H.
       apply in_or_app.
        firstorder.
      + (*dec1 *)
      inversion H3;subst;eauto.
    Qed.
 
  Lemma OLTheoryIsFormula: forall P, OLTheory P -> isFormula P.
  Proof.
   intros.
   inversion H;subst;autounfold with enc;eauto;
   try constructor;try solve constructor;eauto.
   all:
    constructor;
    [do 2 constructor;inversion H1;subst;solveF 
    | intros;inversion H1;subst;solveF].  
   Qed.
  
   Lemma OLTheoryCutIsFormula: forall n P, (OLTheoryCut n) P -> isFormula P.
  Proof.
   intros.
   inversion H;subst; eauto;
   try constructor;try solve constructor;eauto using OLTheoryIsFormula.
   Qed.
  
  Hint Immediate OLTheoryIsFormula OLTheoryCutIsFormula: core.
  
  Lemma CuteRuleNBound : forall h n B L X ,  seqN (OLTheoryCut n) h B L X ->
                                             forall m, n<=m -> seq (OLTheoryCut m) B L X .
  Proof with solveF.
    induction h using strongind ; intros.
    inversion H ...
    inversion H0;solveF;
      repeat match goal with
             | [ Hs : seqN (OLTheoryCut n) h ?B1 ?N1 ?X1 |- _] =>
               let Hs1 := fresh in
               assert (Hs1 : seq (OLTheoryCut m) B1 N1 X1) by
                   (
                     eapply H  with (m:= h) (n:= n)  (m0:=m) (B:= B1);solveF 
                   );clear Hs
             end;solveLL;auto.

    rewrite H3. tensor M N...
    decide1 F;eauto ...
    decide2 F;eauto ...  
    decide3 F;eauto ...
    inversion H3... 
    apply oothc_cutn with (m:= m0)...
    existential t.
    apply H4 in properX.
    eapply H with (m0:=m) in properX... 
  Qed.

  Lemma CuteRuleNBound' : forall n B L X ,
      seq (OLTheoryCut n)  B L X ->
      forall m, n<=m -> seq (OLTheoryCut m) B L X .
  Proof.
    intros.
    apply seqtoSeqN in H. destruct H.
    eapply CuteRuleNBound;eauto.
  Qed.
  
  Ltac solveOLFormula' :=
      match goal with                 
         | [ Hf: isOLFormula (_ (_ ?F ?G) ?w) |- isOLFormula' ?F ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;auto                                           
     
         | [ Hf: isOLFormula (_ (_ ?F ?G) ?w) |- isOLFormula' ?G ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;auto                                           

        | [ Hf:  isOLFormula (_(_ ?F) ?w)|- isOLFormula' ?F ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;auto 
            
        | [ Hf:  isOLFormula (_(_ ?F) ?w)|- isWorldExp ?w ] => 
            inversion Hf as [z1 z2 Z3];subst;auto 
                
         | [ Hf: isOLFormula (_ (_ ?F ?v) ?w) |- isWorldExp ?v ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;auto  

         | [ Hf: isOLFormula (_ (_ ?F ?G) ?w) |- isWorldExp ?w ] => 
            inversion Hf as [z1 z2 Z3];subst;inversion Z3;subst;auto 
         | [ Hf:_ |- isFormula ((_ ?F ?w))   ] => 
                constructor;auto  
         | [ Hf:_ |- isFormula ((_ ?F ?w)^)   ] => 
                constructor;auto                                               
         | [ Hf:_ |- isFormula ((_ ?F1 ?F2 ?w))   ] => 
                constructor;auto
         | [ Hf:_ |- isFormula ((_ ?F1 ?F2 ?w)^)   ] => 
                constructor;auto  
          | [ Hf:_ |- isFormulaL [(_ ?F1 ?F2 ?w)]   ] => 
                constructor;constructor;auto
         | [ Hf:_ |- isFormulaL [(_ ?F1 ?F2 ?w)^]   ] => 
                constructor;constructor;auto     
         | [ Hf:_ |- isFormulaL [(_ ?F ?w)]   ] => 
                constructor;constructor;auto
         | [ Hf:_ |- isFormulaL [(_ ?F ?w)^]   ] => 
                constructor;constructor;auto    
                
                                                          
     end.
         
  Theorem RTENSOR_PRINCIPAL  : forall Gamma D1 D2 F1 F2 G v w n n' x1 x2,  
        n' <= n ->  
        lengthUexp (F1 *** F2) n' ->
        isOLFormula ((F1 *** F2) @ w) ->
        seqN OLTheory x1 (LEncode Gamma) (LEncode D2) (>> BODY_RTENSORR F1 F2 w ) ->
        seqN OLTheory x2 (LEncode Gamma) (REncode (G @ v) :: LEncode D1) (> [BODY_RTENSORL F1 F2 w]) ->
        seq (OLTheoryCut (pred n)) (LEncode Gamma) (REncode (G @ v) :: LEncode (D1 ++ D2))(> []).
  Proof with subst;auto;eauto;try solveOLFormula'.
    intros.       
    inversion H0...

    assert(CCT: seq (OLTheoryCut (Nat.max n1 n2)) (LEncode Gamma) []
         (> [(BODY_RTENSORR F1 F2 w) ^; (BODY_RTENSORL F1 F2 w) ^])).
    apply CutCoherenceTensor...
    assert(BR: seq (OLTheoryCut ((Nat.max n1 n2))) 
            (LEncode Gamma) (LEncode D2) (>> BODY_RTENSORR F1 F2 w)).
    apply WeakTheory with (theory:= OLTheory)...
    apply seqNtoSeq in H2.
    LLExactMap' H2.
    
    apply seqtoSeqN in BR.
    destruct BR as [nr BR].
    apply seqtoSeqN in CCT.
    destruct CCT as [nc CCT].

    assert(HCUT1:seq (OLTheoryCut ((Nat.max n1 n2))) (LEncode Gamma)
                   ([]++LEncode D2) (> [dual (BODY_RTENSORL F1 F2 w)])).
                   
   refine (GeneralCut _ _ _ _ _ _ _ _ _ _ CCT BR)... 
   rewrite app_nil_l in HCUT1.
   
   assert(BL:seq (OLTheoryCut (Nat.max n1 n2)) (LEncode Gamma)
          (REncode (G @ v) :: LEncode D1)
          (>> BODY_RTENSORL F1 F2 w)).
   release.
           
   apply WeakTheory with (theory:= OLTheory)...
   apply seqNtoSeq in H3.
   LLExactMap' H3.
     
   apply seqtoSeqN in HCUT1. 
   destruct HCUT1 as [nh HCUT1].
   apply seqtoSeqN in BL.
   destruct BL as [nl BL].

  assert(HCUT2:seq (OLTheoryCut (Nat.max n1 n2)) (LEncode Gamma)
  (LEncode D2++(REncode (G @ v) :: LEncode D1)) (> [])).
    
  refine (GeneralCut _ _ _ _ _ _ _ _ _ _ HCUT1 BL)...
  LLPermMap(LEncode D2 ++ REncode (G @ v) :: LEncode D1).
  eapply CuteRuleNBound' with (n:=(Nat.max n1 n2));auto.
  lia.    
  Qed.
  
  Theorem RIMPL_PRINCIPAL  : forall Gamma D1 D2 F1 F2 G v w n n' x1 x2,  
        n' <= n ->  
        lengthUexp (F1 --o F2) n' ->
        isOLFormula ((F1 --o F2) @ w) ->
        seqN OLTheory x1 (LEncode Gamma) (LEncode D2) (> [BODY_RIMPLR F1 F2 w] ) ->
        seqN OLTheory x2 (LEncode Gamma) (REncode (G @ v) :: LEncode D1) (>> BODY_RIMPLL F1 F2 w) ->
        seq (OLTheoryCut (pred n)) (LEncode Gamma) (REncode (G @ v) :: LEncode (D1 ++ D2))(> []).
  Proof with subst;auto;eauto;try solveOLFormula'.
    intros.
    inversion H0...
    assert(CCI: seq (OLTheoryCut (Nat.max n1 n2)) (LEncode Gamma) []
         (> [(BODY_RIMPLL F1 F2 w) ^; (BODY_RIMPLR F1 F2 w) ^])).
    apply CutCoherenceImpl...
    
    assert(BL: seq (OLTheoryCut ((Nat.max n1 n2))) 
            (LEncode Gamma) (REncode (G @ v) :: LEncode D1)
            (>> BODY_RIMPLL F1 F2 w)).
    apply WeakTheory with (theory:= OLTheory)...
    apply seqNtoSeq in H3.
    LLExactMap' H3.
    
    
    apply seqtoSeqN in BL.
    destruct BL as [nl BL].
    apply seqtoSeqN in CCI.
    destruct CCI as [nc CCI].

    assert(HCUT1:seq (OLTheoryCut ((Nat.max n1 n2))) (LEncode Gamma)
                   ([]++REncode (G @ v) :: LEncode D1) (> [dual (BODY_RIMPLR F1 F2 w)])).
               
   refine (GeneralCut _ _ _ _ _ _ _ _ _ _ CCI BL)...
   rewrite app_nil_l in HCUT1.
   
   assert(BR:seq (OLTheoryCut (Nat.max n1 n2)) (LEncode Gamma)
          (LEncode D2) (>> BODY_RIMPLR F1 F2 w)).
   release.
           
   apply WeakTheory with (theory:= OLTheory)...
   apply seqNtoSeq in H2.
   LLExactMap' H2.
     
   apply seqtoSeqN in HCUT1. 
   destruct HCUT1 as [nh HCUT1].
   apply seqtoSeqN in BR.
   destruct BR as [nr BR].

  assert(HCUT2:seq (OLTheoryCut (Nat.max n1 n2)) (LEncode Gamma)
  ((REncode (G @ v) :: LEncode D1) ++ LEncode D2) (> [])).
    
  refine (GeneralCut _ _ _ _ _ _ _ _ _ _ HCUT1 BR)...
  LLPermMap((REncode (G @ v) :: LEncode D1) ++ LEncode D2).
  eapply CuteRuleNBound' with (n:=(Nat.max n1 n2));auto.
  lia.    
  Qed.

 Theorem RAT_PRINCIPAL  : forall Gamma D1 D2 F G v v0 w n n' x1 x2,  
        n' <= n ->  
        lengthUexp (F AT v0) n' ->
        isOLFormula ((F AT v0) @ w) ->
        seqN OLTheory x1 (LEncode Gamma) (LEncode D2) (> [BODY_RATR F v0] ) ->
        seqN OLTheory x2 (LEncode Gamma) (REncode (G @ v) :: LEncode D1) (>> BODY_RATL F v0) ->
        seq (OLTheoryCut (pred n)) (LEncode Gamma) (REncode (G @ v) :: LEncode (D1 ++ D2))(> []).
  Proof with subst;auto;eauto;try solveOLFormula'.
    intros.
    inversion H0...
    
    assert(CCA: seq (OLTheoryCut n1) (LEncode Gamma) []
         (> [(BODY_RATL F v0) ^; (BODY_RATR F v0) ^])).
    apply CutCoherenceAt...
   
    assert(BL: seq (OLTheoryCut n1) 
            (LEncode Gamma) (REncode (G @ v) :: LEncode D1)
            (>> BODY_RATL F v0)).
    apply WeakTheory with (theory:= OLTheory)...
    apply seqNtoSeq in H3.
    LLExactMap' H3.
    
    
    apply seqtoSeqN in BL.
    destruct BL as [nl BL].
    apply seqtoSeqN in CCA.
    destruct CCA as [nc CCA].

    assert(HCUT1:seq (OLTheoryCut n1) (LEncode Gamma)
                   ([]++REncode (G @ v) :: LEncode D1) (> [dual (BODY_RATR F v0)])).
               
   refine (GeneralCut _ _ _ _ _ _ _ _ _ _ CCA BL)...
   rewrite app_nil_l in HCUT1.
   
   assert(BR:seq (OLTheoryCut n1) (LEncode Gamma)
          (LEncode D2) (>> BODY_RATR F v0)).
   release.
           
   apply WeakTheory with (theory:= OLTheory)...
   apply seqNtoSeq in H2.
   LLExactMap' H2.
     
   apply seqtoSeqN in HCUT1. 
   destruct HCUT1 as [nh HCUT1].
   apply seqtoSeqN in BR.
   destruct BR as [nr BR].

  assert(HCUT2:seq (OLTheoryCut n1) (LEncode Gamma)
  ((REncode (G @ v) :: LEncode D1) ++ LEncode D2) (> [])).
    
  refine (GeneralCut _ _ _ _ _ _ _ _ _ _ HCUT1 BR)...
  LLPermMap((REncode (G @ v) :: LEncode D1) ++
           LEncode D2).
  eapply CuteRuleNBound' with (n:=n1);auto.
  lia.    
  Qed.
  
  Theorem RARROW_PRINCIPAL  : forall Gamma D1 D2 FW FW0 G v w n n' x1 x2,  
        n' <= n ->  
        uniform FW0 ->
        uniform FW ->
        ext_eq FW0 FW ->
        lengthUexp (ARROW FW0) n' ->
        isOLFormula ((ARROW FW0) @ w) ->
        seqN OLTheory x1 (LEncode Gamma) (LEncode D2) (> [BODY_RARROWR FW0 w] ) ->
        seqN OLTheory x2 (LEncode Gamma) (REncode (G @ v) :: LEncode D1) (>> BODY_RARROWL FW w) ->
        seq (OLTheoryCut (pred n)) (LEncode Gamma) (REncode (G @ v) :: LEncode (D1 ++ D2))(> []).
  Proof with subst;auto;eauto;try solveOLFormula'. 
    intros.
    inversion H3...
    inversion H4...
    inversion H12...
    apply lbindEq in H7;auto.
    apply lbindEq in H10;auto.
    assert(isOLFormula' (FW1 w)) by auto.
    rewrite H2 in H7.
    rewrite H2 in H10.
    rewrite H10 in H15...
    rewrite H7 in H9...
   
    
    
    assert(CCA: seq (OLTheoryCut n1) (LEncode Gamma) []
         (> [(BODY_RARROWL FW w) ^; (BODY_RARROWR FW w) ^])).
    apply CutCoherenceArrow...
    apply OLSize with (t:= (t_world ID));eauto.
  
    assert(BL: seq (OLTheoryCut n1) 
            (LEncode Gamma) (REncode (G @ v) :: LEncode D1)
            (>> BODY_RARROWL FW w)).
    apply WeakTheory with (theory:= OLTheory)...
    apply seqNtoSeq in H6.
    LLExactMap' H6.
    
    
    apply seqtoSeqN in BL.
    destruct BL as [nl BL].
    apply seqtoSeqN in CCA.
    destruct CCA as [nc CCA].

    assert(HCUT1:seq (OLTheoryCut n1) (LEncode Gamma)
                   ([]++REncode (G @ v) :: LEncode D1) (> [dual (BODY_RARROWR FW w)])).
               
   refine (GeneralCut _ _ _ _ _ _ _ _ _ _ CCA BL)...
   rewrite app_nil_l in HCUT1.
   
   assert(BR:seq (OLTheoryCut n1) (LEncode Gamma)
          (LEncode D2) (>> BODY_RARROWR FW w)).
   release.
   autounfold with enc.
   rewrite <- H2...       
   fold (BODY_RARROWR FW0 w).
   apply WeakTheory with (theory:= OLTheory)...
   apply seqNtoSeq in H5.
   LLExactMap' H5.
     
   apply seqtoSeqN in HCUT1. 
   destruct HCUT1 as [nh HCUT1].
   apply seqtoSeqN in BR.
   destruct BR as [nr BR].

  assert(HCUT2:seq (OLTheoryCut n1) (LEncode Gamma)
  ((REncode (G @ v) :: LEncode D1) ++ LEncode D2) (> [])).
    
  refine (GeneralCut _ _ _ _ _ _ _ _ _ _ HCUT1 BR)...
  LLPermMap((REncode (G @ v) :: LEncode D1) ++
           LEncode D2).
  eapply CuteRuleNBound' with (n:=n1);auto.
  lia.    
Qed.


 Theorem RBANG_PRINCIPAL  : forall Gamma D F G v w n n' x1 x2,  
        n' <= n ->  
        lengthUexp (!! F) n' ->
        isOLFormula ((!! F) @ w) ->
        seqN OLTheory x1 (LEncode Gamma) [] (>> BODY_RBANGR F w ) ->
        seqN OLTheory x2 (LEncode Gamma) (REncode (G @ v) :: LEncode D) (> [BODY_RBANGL F w]) ->
        seq (OLTheoryCut (pred n)) (LEncode Gamma) (REncode (G @ v) :: LEncode D)(> []).
  Proof with subst;auto;eauto;try solveOLFormula'.
    intros. 
    inversion H0...
    assert(CCB: seq (OLTheoryCut n1) (LEncode Gamma) []
         (> [(BODY_RBANGL F w) ^; (BODY_RBANGR F w) ^])).
    apply CutCoherenceBang...
  
    assert(BL: seq (OLTheoryCut n1) 
            (LEncode Gamma) (REncode (G @ v) :: LEncode D)
            (>> BODY_RBANGL F w)).
    apply WeakTheory with (theory:= OLTheory)...
    release.
    apply seqNtoSeq in H3.
    LLExactMap' H3.
    
    
    apply seqtoSeqN in BL.
    destruct BL as [nl BL].
    apply seqtoSeqN in CCB.
    destruct CCB as [nc CCB].

    assert(HCUT1:seq (OLTheoryCut n1) (LEncode Gamma)
                   ([]++REncode (G @ v) :: LEncode D) (> [dual (BODY_RBANGR F w)])).
               
   refine (GeneralCut _ _ _ _ _ _ _ _ _ _ CCB BL)...
   rewrite app_nil_l in HCUT1.
   
  
   assert(BR:seq (OLTheoryCut n1) (LEncode Gamma)
          [] (>> BODY_RBANGR F w)).
   apply WeakTheory with (theory:= OLTheory)...
   apply seqNtoSeq in H2.
   LLExactMap' H2.
     
   apply seqtoSeqN in HCUT1. 
   destruct HCUT1 as [nh HCUT1].
   apply seqtoSeqN in BR.
   destruct BR as [nr BR].

  assert(HCUT2:seq (OLTheoryCut n1) (LEncode Gamma)
  ((REncode (G @ v) :: LEncode D) ++ []) (> [])).
    
  refine (GeneralCut _ _ _ _ _ _ _ _ _ _ HCUT1 BR)...
  rewrite app_nil_r in HCUT2.
  eapply CuteRuleNBound' with (n:=n1);auto.
  lia.    
  Qed.

   
 Theorem RALL_PRINCIPAL  : forall Gamma D1 D2 FX FX0 G v w n n' x1 x2,  
        n' <= n ->  
        uniform FX ->
        uniform FX0 ->
        ext_eq FX0 FX ->
        lengthUexp (ALL FX0) n' ->
        isOLFormula ((ALL FX0) @ w) ->
        proper w ->
        seqN OLTheory x1 (LEncode Gamma) (LEncode D2)(> [BODY_RALLR FX0 w] )   ->
        seqN OLTheory x2 (LEncode Gamma) (REncode (G @ v) :: LEncode D1) (>> BODY_RALLL FX w) ->
        seq (OLTheoryCut (pred n)) (LEncode Gamma) (REncode (G @ v) :: LEncode (D1 ++ D2))(> []).
  Proof with subst;eauto using proper_VAR; try solveOLFormula'.
    intros. 
    inversion H3...
    inversion H4...
    inversion H13...
    apply lbindEq in H8...
    apply lbindEq in H11... 
    rewrite H8 in H10...
    
    rewrite H2 in H10...
    
     assert(CCA: seq (OLTheoryCut n1) (LEncode Gamma) []
         (> [(BODY_RALLL FX w) ^; (BODY_RALLR FX0 w) ^])).
    apply CutCoherenceAll...
    intros. constructor...
    assert(isOLFormula' (FX2 t)) by auto.
    rewrite H11 in H17...
    rewrite H2 in H17...
    
    assert(BR:seq (OLTheoryCut n1) (LEncode Gamma)
          (LEncode D2) (>> BODY_RALLR FX0 w)).
   apply WeakTheory with (theory:= OLTheory)...
   release.
   apply seqNtoSeq in H6.
   LLExactMap' H6.
   
   assert(BL: seq (OLTheoryCut n1) 
            (LEncode Gamma) (REncode (G @ v) :: LEncode D1)
            (>> BODY_RALLL FX w)).
            
    apply WeakTheory with (theory:= OLTheory)...
    apply seqNtoSeq in H7.
    LLExactMap' H7.
    
   apply seqtoSeqN in BR.
    destruct BR as [nr BR].
    apply seqtoSeqN in BL.
   destruct BL as [nl BL].
    apply seqtoSeqN in CCA.
    destruct CCA as [na CCA].
    
    assert(HCUT1:seq (OLTheoryCut n1) (LEncode Gamma)
                   ([]++REncode (G @ v) :: LEncode D1) (> [dual (BODY_RALLR FX0 w)])).
               
   refine (GeneralCut _ _ _ _ _ _ _ _ _ _ CCA BL)... 
   solveUniform.
   solveUniform.
   solveUniform.
   rewrite app_nil_l in HCUT1.
 
  apply seqtoSeqN in HCUT1.
  destruct HCUT1 as [nc HCUT1].

  assert(HCUT2:seq (OLTheoryCut n1) (LEncode Gamma)
  ((REncode (G @ v) :: LEncode D1) ++ LEncode D2) (> [])).
    
  refine (GeneralCut _ _ _ _ _ _ _ _ _ _ HCUT1 BR)...
   solveUniform.
   solveUniform.
  LLPermMap ((REncode (G @ v) :: LEncode D1) ++ LEncode D2).
  eapply CuteRuleNBound' with (n:=n1);auto.
  lia.    
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
  Proof with autounfold with enc;solveF; try easyF.
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
    
    +
     assert (h1 = 0) by lia...
     inversion Hseq1.
    + 
     assert(IH : CutDefinition n' h) by auto; clear H.
     (* Let's analyze Hseq1 -- the left premise in the cut rule *)
     inversion Hseq1...
     - apply NotFromREncode in H0... (* cannot be from the linear context *)
     - apply NotFromLEncode in H0... (* cannot be from the classical context *)
     - (* Now HSeq2 -- the right premise *)
       inversion Hseq2...
       apply NotFromREncode in H3... (* cannot be from the linear context *) 
       apply NotFromLEncode in H3... (* cannot be from the classical context *) 

    (* By case analysis on the rules applied in each case *)
  (* INIT LEFT
  | TENSORL LEFT
  | TENSORR LEFT
  | IMPLL LEFT
  | IMPLr LEFT
  | ATL LEFT
  | ATR LEFT
  | ARROWL LEFT 
  | ARROWR LEFT 
  | BANGL LEFT 
  | BANGR LEFT
  | COPY
  | ALLL LEFT 
  | ALLR LEFT  *)
  
    inversion H;solveF; 
    (* The cases such that INIT, BANGR and COPY are in Hseq1 do not depends on Hseq2 *)
    only 1 : solveINIT; 
    only 10: solveBANGR; 
    only 10: solveRCOPY;

    inversion H2;solveF;
    try solveBANGL;
    try solveRTENSORR;
    try solveRTENSORL;
    try solveRATR;
    try solveRATL;
    try solveRARROWR;
    try solveRARROWL;
    try solveRALLR;
    try solveRALLL;
    try solveRIMPR;
    try solveRIMPLL;try solveRCOPY'.

  (*  Set Ltac Profiling.
    Show Ltac Profile. *)
    
    (* TENSOR LEFT in Hseq1 *)
    {
    apply RINITInv1 in H4...
    decompose [and or] H7;subst;clear H7.
    * 
     apply WeakTheory with (theory:= OLTheory)...
     apply seqNtoSeq in Hseq1.
     LLExactMap' Hseq1.
    *
     apply RTENSORLInv2 in H1...
     decompose [or] H1;CleanContext;clear H1.
     -
      decide3 ( RTENSORL F1 G0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ [])).   
      rewrite app_nil_r.
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H7.
      LLExactMap' H7.
     - 
     apply (rewL1 _ _ H3).
     decide3 ( RTENSORL F1 G0 w0)...
     tensor ([d| (F1 *** G0) @ w0 |])  (REncode (G @ v) :: LEncode (x0 ++ [])).
     LLPermMap (REncode (G @ v) :: LEncode ((x0 ++ [F1 @ w0] ++ [G0 @ w0])++[])).
     
     eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
     - 
     decide3 ( RTENSORL F1 G0 w0)...
     tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ [])).
     LLPermMap (REncode (G @ v) :: LEncode ((Delta1 ++ [F1 @ w0] ++ [G0 @ w0])++[])).

     eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
   
    }
    {
     apply RTENSORRInv1 in H4...
     do 3 destruct H4.
     decompose [and] H4;subst;clear H4...
     
     apply RTENSORLInv2 in H1...
     decompose [or] H1;CleanContext;clear H1.
     -
     (* TENSOR IS PRINCIPAL *)
     inversion H3...
     apply (rewL2 _ _ H9).
     LLPermMap(REncode (G @ v) :: LEncode (Delta1 ++ (x0 ++ x1))). 
     
     eapply RTENSOR_PRINCIPAL with (F1:=F1) (F2:=G0) (n':=n') (w:=w0)...
     LLPermMap( LEncode x0 ++ LEncode x1).
     tensor;[ exact H11 | exact H13].
     solveLL.  
     LLPermMap (REncode (G @ v) :: LEncode (Delta1 ++ [F1 @ w0] ++ [G0 @ w0])).
     exact H7.
  -
     apply (rewL1 _ _ H3).
          
     decide3 ( RTENSORL F1 G0 w0)...
     tensor ([d| (F1 *** G0) @ w0 |])  (REncode (G @ v)::LEncode x3++LEncode Delta2).
     LLPermMap (REncode (G @ v) :: 
              LEncode ((x3 ++ [ F1 @ w0 ] ++ [ G0 @ w0]) ++ Delta2)).  
      eapply IH with (h1:=x2) (h2:=S (S (S (S (S x))))) (m:=x2 + S (S (S (S (S x))))) (w:=w1) (FCut:=(F *** G1))...
     -
     decide3 ( RTENSORL F1 G0 w0)...
     tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
     LLPermMap (REncode (G @ v) :: 
            LEncode ((Delta1 ++ [ F1 @ w0 ] ++ [ G0 @ w0]) ++ Delta2)).     
     eapply IH with (h1:=x2) (h2:=S (S (S (S (S x))))) (m:=x2 + S (S (S (S (S x))))) (w:=w1) (FCut:=(F *** G1))...

     }   
       {
       apply RIMPLRInv1 in H4;auto. 
       
       apply RTENSORLInv2 in H1.
       decompose [or] H1;CleanContext;clear H1.
       - discriminate H4.
       -
       apply (rewL1 _ _ H4).
       decide3 (RTENSORL F1 G0 w0)...
       tensor [d| (F1 *** G0) @ w0 |]  (REncode (G @ v) :: LEncode x0 ++ LEncode Delta2)...
         
       LLPermMap(REncode (G @ v):: LEncode ((x0 ++ [F1 @ w0]++[G0 @ w0]) ++ Delta2)).
       eapply IH with (h1:=x) (h2:=S (S (S (S (S (S x1)))))) (m:=x+S(S (S (S (S (S x1)))))) (w:=w1) (FCut:=F --o G1)...                   
        - 
        decide3 (RTENSORL F1 G0 w0)...
        tensor(@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2))...
         
        LLPermMap(REncode (G @ v) :: LEncode ((Delta1 ++ [F1 @ w0]++[G0 @ w0]) ++ Delta2)).
          
          eapply IH with (h1:=x) (h2:=S (S (S (S (S (S x0)))))) (m:=x+S(S (S (S (S (S x0)))))) (w:=w1) (FCut:=F --o G1)...                     
        }
        {
     apply RATRInv1 in H4...
     CleanContext.
     apply RTENSORLInv2 in H1. 
     decompose [or] H1;CleanContext;clear H1.
     - discriminate H3.
     -
     apply (rewL1 _ _ H3).
     decide3 (RTENSORL F1 G0 w0)...
     tensor [d| (F1 *** G0) @ w0 |]  (REncode (G @ v) :: LEncode x1 ++ LEncode Delta2)...
     LLPermMap(REncode (G @ v):: LEncode ((x1 ++ [F1 @ w0] ++[G0 @ w0]) ++ Delta2)) .
     eapply IH with (h1:=x0) (h2:=(S (S (S (S x))))) (m:=x0+(S (S (S (S x))))) (w:=w1) (FCut:=F AT v0)...                     
     - 
     decide3 (RTENSORL F1 G0 w0)...
     tensor(@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2))...
     LLPermMap(REncode (G @ v):: LEncode ((Delta1 ++ [F1 @ w0]++[G0 @ w0]) ++ Delta2)) .
     eapply IH with (h1:=x0) (h2:=(S (S (S (S x))))) (m:=x0+(S (S (S (S x))))) (w:=w1) (FCut:=F AT v0)...                     
      }
       
      {    
         apply RARROWRInv1 in H4;auto.
         CleanContext.
         apply RTENSORLInv2 in H1. 
         decompose [or] H1;CleanContext;clear H1.
         - discriminate H3.
         -
         apply (rewL1 _ _ H3).
         decide3 (RTENSORL F1 G0 w0)...
         tensor [d| (F1 *** G0) @ w0 |]  (REncode (G @ v) :: LEncode x1 ++ LEncode Delta2)...
           
         LLPermMap(REncode (G @ v)
                                 :: LEncode ((x1 ++ [F1 @ w0] ++[G0 @ w0]) 
                                 ++ Delta2)).
         eapply IH with (h1:=x0) (h2:=(S (S (S (S x))))) (m:=x0+(S (S (S (S x))))) (w:=w1) (FCut:=ARROW FW)...                     
        - 
        decide3 (RTENSORL F1 G0 w0)...
        tensor(@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2))...
         
        LLPermMap(REncode (G @ v)
                                 :: LEncode ((Delta1 ++ [F1 @ w0]++[G0 @ w0]) 
                                 ++ Delta2)).
          
          eapply IH with (h1:=x0) (h2:=(S (S (S (S x))))) (m:=x0+(S (S (S (S x))))) (w:=w1) (FCut:=ARROW FW)...                     
          }
     {  
     apply BANGRInv1 in H4;auto.
     CleanContext.
     apply RTENSORLInv2 in H1. 
         decompose [or] H1;CleanContext;clear H1.
         - discriminate H3.
         -
         apply (rewL1 _ _ H3).
         decide3 (RTENSORL F1 G0 w0)...
         tensor [d| (F1 *** G0) @ w0 |]  (REncode (G @ v) :: LEncode x1 ++ [])...
           
         LLPermMap(REncode (G @ v)
                                 :: LEncode ((x1 ++ [F1 @ w0] ++[G0 @ w0]) ++ [])).
         eapply IH with (h1:=x0) (h2:=(S (S (S (S x))))) (m:=x0+(S (S (S (S x))))) (w:=w1) (FCut:=!! F)...                     
        - 
        decide3 (RTENSORL F1 G0 w0)...
        tensor(@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ []))...
         
        LLPermMap(REncode (G @ v)
                                 :: LEncode ((Delta1 ++ [F1 @ w0]++[G0 @ w0]) 
                                 ++ [])).
          
        eapply IH with (h1:=x0) (h2:=(S (S (S (S x))))) (m:=x0+(S (S (S (S x))))) (w:=w1) (FCut:=!! F)...                     
     }     
     { 
      apply RALLRInv1 in H4;auto;CleanContext.
      apply RTENSORLInv2 in H1. 
      decompose [or] H1;CleanContext;clear H1.
      - discriminate H3.
      -
         apply (rewL1 _ _ H3).
         decide3 (RTENSORL F1 G0 w0)...
         tensor [d| (F1 *** G0) @ w0 |]  (REncode (G @ v) :: LEncode x1 ++ LEncode Delta2)...
           
           
         LLPermMap(REncode (G @ v)
                                 :: LEncode ((x1 ++ [F1 @ w0] ++[G0 @ w0]) 
                                 ++ Delta2)).
        eapply IH with (h1:=x0) (h2:=(S (S (S (S x))))) (m:=x0+(S (S (S (S x))))) (w:=w1) (FCut:=ALL FX)...   
        - 
        decide3 (RTENSORL F1 G0 w0)...
         tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2))...
           
           
         LLPermMap(REncode (G @ v)
                                 :: LEncode ((Delta1 ++ [F1 @ w0] ++[G0 @ w0]) 
                                 ++ Delta2)).
          eapply IH with (h1:=x0) (h2:=(S (S (S (S x))))) (m:=x0+(S (S (S (S x))))) (w:=w1) (FCut:=ALL FX)...                       
       } 
             
     (* IMPLICATION LEFT in Hseq1 *)
    { 
     apply RINITInv1 in H4;auto.
     decompose [or and] H4;clear H4;CleanContext.
      * 
     apply WeakTheory with (theory:= OLTheory)...
     apply seqNtoSeq in Hseq1.
     LLExactMap' Hseq1.

    *
     apply RIMPLLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.

     -
      apply (rewL1 _ _ H4).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (x0 ++ x1)).   
      tensor (LEncode x0)  (REncode (G @ v) :: LEncode x1).   
      permMap.
       
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H7.
      LLExactMap' H7.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H8.
      LLExactMap' H8.
      
     -
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode (x0 ++ x1)).   
      tensor ( LEncode x0) (REncode (G @ v) :: LEncode x1) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x0++[])).
      eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
      LLExactMap H3. 
     - 
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode (x0 ++ x1)).   
      tensor ( LEncode x0) (REncode (G @ v) :: LEncode x1) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H3.
      LLExactMap' H3. 
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[G0 @ w0]) ++ [])).
      eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
      LLExactMap H4. 
      
     - 
      apply (rewL1 _ _ H3).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (x0 ++ x1)).   
      tensor (LEncode x0)  (REncode (G @ v) :: LEncode x1).   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H7.
      LLExactMap' H7. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x0++[])).
      eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
      LLExactMap H4. 
    -
      apply (rewL1 _ _ H3).
       decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (x0 ++ x1)).   
      tensor (LEncode x0)  (REncode (G @ v) :: LEncode x1).   
      permMap.
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4. 
 
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[G0 @ w0])++[])).
      eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
      LLExactMap H7. }  
     
     { 
 
     apply RTENSORRInv1 in H4;auto.
     CleanContext.

     apply RIMPLLInv2 in H1;auto. 
         decompose [or] H1;clear H1;CleanContext.
     - discriminate H1.    
     -
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode ((x3 ++ x4)++Delta2)).   
      permMap.  
      tensor ( LEncode (x3++Delta2)) (REncode (G @ v) :: LEncode x4) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H7.
      LLExactMap' H7. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x3++Delta2)).
      eapply IH with (h1:=x2) (h2:=(S (S (S (S (S x))))) ) (m:=x2 + (S (S (S (S (S x))))) ) (w:=w1) (FCut:=F *** G1)...
      LLExactMap H4. 
     - 
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode ((x3 ++ x4)++Delta2)).   
      permMap.  
      tensor ( LEncode x3) (REncode (G @ v) :: LEncode (x4++Delta2)) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4.
       
      LLPermMap (REncode (G @ v) :: LEncode ((x4 ++ [G0 @ w0]) ++ Delta2)).
      eapply IH with (h1:=x2) (h2:=(S (S (S (S (S x))))) ) (m:=x2 + (S (S (S (S (S x))))) ) (w:=w1) (FCut:=F *** G1)...
      LLExactMap H7.
      
     - 
      apply (rewL1 _ _ H4).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode ((x3 ++ x4)++Delta2)).   
      permMap.  
      tensor ( LEncode (x3++Delta2)) (REncode (G @ v) :: LEncode x4) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H10.
      LLExactMap' H10. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x3++Delta2)).
      eapply IH with (h1:=x2) (h2:=(S (S (S (S (S x))))) ) (m:=x2 + (S (S (S (S (S x))))) ) (w:=w1) (FCut:=F *** G1)...
      LLExactMap H7. 
     - 
      apply (rewL1 _ _ H4).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo) (REncode (G @ v) :: LEncode ((x3 ++ x4)++Delta2)).   
      permMap.  
      tensor ( LEncode x3) (REncode (G @ v) :: LEncode (x4++Delta2)) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H7.
      LLExactMap' H7.
       
      LLPermMap (REncode (G @ v) :: LEncode ((x4 ++ [G0 @ w0]) ++ Delta2)).
      eapply IH with (h1:=x2) (h2:=(S (S (S (S (S x))))) ) (m:=x2 + (S (S (S (S (S x))))) ) (w:=w1) (FCut:=F *** G1)...
      LLExactMap H10.
    } 
    {
    
    apply RIMPLRInv1 in H4;auto.
    CleanContext.
    
    apply RIMPLLInv2 in H1;auto. 
    decompose [or] H1;clear H1;CleanContext.
     - 
      (* IMPL IS PRINCIPAL *)

     inversion H1...
     apply (rewL1 _ _ H4).
     LLPermMap(REncode (G @ v) :: LEncode ((x1 ++ x2) ++ Delta2)). 
     
     eapply RIMPL_PRINCIPAL with (F1:=F1) (F2:=G0) (n':=n') (w:=w0)...
     solveLL.
     LLPermMap(LEncode Delta2 ++ [d| F1 @ w0 |; u| G0 @ w0 |]).
     exact H7.
     LLPermMap(LEncode x1 ++ (u| G @ v | :: LEncode x2)).
     tensor;[ exact H8 | exact H9 ].
     -
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode (x1++Delta2)) (REncode (G @ v) :: LEncode x2) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x1++Delta2)).
      eapply IH with (h1:=x0) (h2:=(S (S (S (S (S (S x)))))) ) (m:=x0 + (S (S (S (S (S (S x)))))) ) (w:=w1) (FCut:=F --o G1)...
      LLExactMap H3. 
     - 
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode x1) (REncode (G @ v) :: LEncode (x2++Delta2)) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H3.
      LLExactMap' H3.
       
      LLPermMap (REncode (G @ v) :: LEncode ((x2 ++ [G0 @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=(S (S (S (S (S (S x))))))  ) (m:=x0 +(S (S (S (S (S (S x)))))) ) (w:=w1) (FCut:=F --o G1)...
      LLExactMap H4.
      
     - 
      apply (rewL1 _ _ H3).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode (x1++Delta2)) (REncode (G @ v) :: LEncode x2) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H8.
      LLExactMap' H8. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x1++Delta2)).
      eapply IH with (h1:=x0) (h2:=(S (S (S (S (S (S x))))))) (m:=x0 + (S (S (S (S (S (S x))))))) (w:=w1) (FCut:=F --o G1)...
      LLExactMap H4. 
     - 
      apply (rewL1 _ _ H3).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo) (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode x1) (REncode (G @ v) :: LEncode (x2++Delta2)) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4.
       
      LLPermMap (REncode (G @ v) :: LEncode ((x2 ++ [G0 @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=(S (S (S (S (S (S x)))))) ) (m:=x0 + (S (S (S (S (S (S x))))))) (w:=w1) (FCut:=F --o G1)...
      LLExactMap H8.
     }
     {
     apply RATRInv1 in H4;auto.
     CleanContext.

     apply RIMPLLInv2 in H1;auto. 
         decompose [or] H1;clear H1;CleanContext.
     - inversion H1.    
     -
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode (x1++Delta2)) (REncode (G @ v) :: LEncode x2) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x1++Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=F AT v0)...
      LLExactMap H3. 
     - 
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode x1) (REncode (G @ v) :: LEncode (x2++Delta2)) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H3.
      LLExactMap' H3.
       
      LLPermMap (REncode (G @ v) :: LEncode ((x2 ++ [G0 @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=F AT v0)...
      LLExactMap H4.
      
     - 
      apply (rewL1 _ _ H3).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode (x1++Delta2)) (REncode (G @ v) :: LEncode x2) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H8.
      LLExactMap' H8. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x1++Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=F AT v0)...
      LLExactMap H4. 
     - 
      apply (rewL1 _ _ H3).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo) (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode x1) (REncode (G @ v) :: LEncode (x2++Delta2)) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4.
       
      LLPermMap (REncode (G @ v) :: LEncode ((x2 ++ [G0 @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=F AT v0)...
      LLExactMap H8.
     }
     {
     apply RARROWRInv1 in H4;auto.
     CleanContext.

     apply RIMPLLInv2 in H1;auto. 
         decompose [or] H1;clear H1;CleanContext.
     - inversion H1.    
     -
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode (x1++Delta2)) (REncode (G @ v) :: LEncode x2) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x1++Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=ARROW FW)...
      LLExactMap H3. 
     - 
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode x1) (REncode (G @ v) :: LEncode (x2++Delta2)) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H3.
      LLExactMap' H3.
       
      LLPermMap (REncode (G @ v) :: LEncode ((x2 ++ [G0 @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=ARROW FW)...
      LLExactMap H4.
      
     - 
      apply (rewL1 _ _ H3).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode (x1++Delta2)) (REncode (G @ v) :: LEncode x2) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H9.
      LLExactMap' H9. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x1++Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=ARROW FW)...
      LLExactMap H4. 
     - 
      apply (rewL1 _ _ H3).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo) (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode x1) (REncode (G @ v) :: LEncode (x2++Delta2)) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4.
       
      LLPermMap (REncode (G @ v) :: LEncode ((x2 ++ [G0 @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=ARROW FW)...
      LLExactMap H9.
     }
     {
     apply BANGRInv1 in H4;auto.
     CleanContext.

     apply RIMPLLInv2 in H1;auto. 
         decompose [or] H1;clear H1;CleanContext.
     - inversion H1.    
     -
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode ((x1 ++ x2)++[])).   
      
      tensor ( LEncode x1) (REncode (G @ v) :: LEncode x2) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x1++[])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=!! F)...
      LLExactMap H3. 
     - 
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode ((x1 ++ x2)++[])).   
      tensor ( LEncode x1) (REncode (G @ v) :: LEncode x2) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H3.
      LLExactMap' H3.
       
      LLPermMap (REncode (G @ v) :: LEncode ((x2 ++ [G0 @ w0]) ++ [])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=!! F)...
      LLExactMap H4.
      
     - 
      apply (rewL1 _ _ H3).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode ((x1 ++ x2)++[])).    
      tensor ( LEncode x1) (REncode (G @ v) :: LEncode x2) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H7.
      LLExactMap' H7. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x1++[])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=!! F)...
      LLExactMap H4. 
     - 
      apply (rewL1 _ _ H3).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo) (REncode (G @ v) :: LEncode ((x1 ++ x2)++[])).    
      tensor ( LEncode x1) (REncode (G @ v) :: LEncode x2) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4.
       
      LLPermMap (REncode (G @ v) :: LEncode ((x2 ++ [G0 @ w0]) ++ [])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=!! F)...
      LLExactMap H7.
     }
     {
     apply RALLRInv1 in H4;auto.
     CleanContext.

     apply RIMPLLInv2 in H1;auto. 
         decompose [or] H1;clear H1;CleanContext.
     - inversion H1.    
     -
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode (x1++Delta2)) (REncode (G @ v) :: LEncode x2) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x1++Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=ALL FX)...
      LLExactMap H3. 
     - 
      apply (rewL1 _ _ H1).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor [d| (F1 --o G0) @ w0 |]  (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode x1) (REncode (G @ v) :: LEncode (x2++Delta2)) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H3.
      LLExactMap' H3.
       
      LLPermMap (REncode (G @ v) :: LEncode ((x2 ++ [G0 @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=ALL FX)...
      LLExactMap H4.
      
     - 
      apply (rewL1 _ _ H3).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode (x1++Delta2)) (REncode (G @ v) :: LEncode x2) .   
      permMap.
      2:{ 
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H10.
      LLExactMap' H10. }
      LLPermMap (REncode (F1 @ w0) :: LEncode (x1++Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=ALL FX)...
      LLExactMap H4. 
     - 
      apply (rewL1 _ _ H3).
      decide3 ( RIMPLL F1 G0 w0)...
      tensor (@nil oo) (REncode (G @ v) :: LEncode ((x1 ++ x2)++Delta2)).   
      permMap.  
      tensor ( LEncode x1) (REncode (G @ v) :: LEncode (x2++Delta2)) .   
      permMap.
      
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4.
       
      LLPermMap (REncode (G @ v) :: LEncode ((x2 ++ [G0 @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x))) ) (m:=x0 +S (S (S (S x)))) (w:=w1) (FCut:=ALL FX)...
      LLExactMap H10.
     }

     (* RATL LEFT in Hseq1 *)
    { 
     apply RINITInv1 in H4;auto.
     decompose [or and] H4;clear H4;CleanContext.
      * 
     apply WeakTheory with (theory:= OLTheory)...
     apply seqNtoSeq in Hseq1.
     LLExactMap' Hseq1.
    *
     apply RATLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    -
      decide3 (RATL F1 v0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode Delta1 ++ []).   
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4.
     - 
      apply (rewL1 _ _ H1).
      decide3 (RATL F1 v0 w0)...
      tensor [d| (F1 AT v0) @ w0 |]  (REncode (G @ v) :: LEncode x0).   
      LLPermMap (REncode (G @ v) :: LEncode ((x0++[F1 @ v0]) ++ [])).
      eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
     - 
      decide3 (RATL F1 v0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode Delta1).
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[F1 @ v0]) ++ [])).
      eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
     }
     { 
     apply RTENSORRInv1 in H4;auto;CleanContext.
   
     apply RATLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    -
      inversion H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RATL F1 v0 w0)...
      tensor [d| (F1 AT v0) @ w0 |]  (REncode (G @ v) :: LEncode (x3++Delta2)).
      permMap.   
      LLPermMap (REncode (G @ v) :: LEncode ((x3++[F1 @ v0]) ++ Delta2)).
      eapply IH with (h1:=x2) (h2:=(S (S (S (S (S x)))))) (m:=x2 + (S (S (S (S (S x)))))) (w:=w1) (FCut:=F *** G0)...
     - 
      decide3 (RATL F1 v0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[F1 @ v0]) ++ Delta2)).
      eapply IH with (h1:=x2) (h2:=(S (S (S (S (S x)))))) (m:=x2 + (S (S (S (S (S x)))))) (w:=w1) (FCut:=F *** G0)...
    }
 
     { 
     apply RIMPLRInv1 in H4;auto;CleanContext.
   
     apply RATLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RATL F1 v0 w0)...
      tensor [d| (F1 AT v0) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap.   
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[F1 @ v0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S (S (S x)))))) (m:=x0 + S (S (S (S (S (S x)))))) (w:=w1) (FCut:=F --o G0)...
     - 
      decide3 (RATL F1 v0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[F1 @ v0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S (S (S x)))))) (m:=x0 + S (S (S (S (S (S x)))))) (w:=w1) (FCut:=F --o G0)...
    }
 { 
     apply RATRInv1 in H4;auto;CleanContext.
   
     apply RATLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    -
     (* RAT IS PRINCIPAL *)
     inversion H1...

     eapply RAT_PRINCIPAL with (F:=F1) (n':=n') (v0:=v0) (w:=w0)...
     solveLL.
     exact H7.
     solveLL. 
     LLPermMap(REncode (G @ v) :: LEncode (Delta1 ++ [F1 @ v0])).
     exact H4.
     -
      apply (rewL1 _ _ H1).
      decide3 ( RATL F1 v0 w0)...
      tensor [d| (F1 AT v0) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).   
      permMap.  
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[F1 @ v0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=(F AT v1))...
     - 
      decide3 ( RATL F1 v0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1++Delta2)).   
     
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[F1 @ v0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=(F AT v1))...
    }    
    { 
     apply RARROWRInv1 in H4;auto;CleanContext.
   
     apply RATLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RATL F1 v0 w0)...
      tensor [d| (F1 AT v0) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap.   
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[F1 @ v0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ARROW FW)...
     - 
      decide3 (RATL F1 v0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[F1 @ v0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ARROW FW)...
    } 
 { 
     apply BANGRInv1 in H4;auto;CleanContext.
   
     apply RATLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RATL F1 v0 w0)...
      tensor [d| (F1 AT v0) @ w0 |]  (REncode (G @ v) :: LEncode x1).
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[F1 @ v0]) ++ [])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=!! F)...
     - 
      decide3 (RATL F1 v0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode Delta1).
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[F1 @ v0]) ++ [])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=!! F)...
    }     
    { 
     apply RALLRInv1 in H4;auto;CleanContext.
   
     apply RATLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RATL F1 v0 w0)...
      tensor [d| (F1 AT v0) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap.   
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[F1 @ v0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ALL FX)...
     - 
      decide3 (RATL F1 v0 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[F1 @ v0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ALL FX)...
    }  
    
 
     (* RATL LEFT in Hseq1 *)
     
    

     
    
     (* RARROW LEFT in Hseq1 *)
     
       { 
     apply RINITInv1 in H4;auto.
     decompose [or and] H4;clear H4;CleanContext.
      * 
     apply WeakTheory with (theory:= OLTheory).
     auto using TheoryInclusion.
     apply seqNtoSeq in Hseq1.
     LLExactMap' Hseq1.
    *
     apply RARROWLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    -
      decide3 (RARROWL FW w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode Delta1 ++ []).   
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H4.
      LLExactMap' H4.
     - 
      apply (rewL1 _ _ H1).
      decide3 (RARROWL FW w0)...
      tensor [d| (ARROW FW) @ w0 |]  (REncode (G @ v) :: LEncode x0).   
      LLPermMap (REncode (G @ v) :: LEncode ((x0++[(FW w0) @ w0 ]) ++ [])).
      eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
     - 
      decide3 (RARROWL FW w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode Delta1).
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FW w0) @ w0 ]) ++ [])).
      eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
     }
     { 
     apply RTENSORRInv1 in H4;auto;CleanContext.
   
     apply RARROWLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RARROWL FW w0)...
      tensor [d| (ARROW FW) @ w0 |]  (REncode (G @ v) :: LEncode (x3++Delta2)).
      permMap.   
      LLPermMap (REncode (G @ v) :: LEncode ((x3++[(FW w0) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x2) (h2:=(S (S (S (S (S x)))))) (m:=x2 + (S (S (S (S (S x)))))) (w:=w1) (FCut:=F *** G0)...
     - 
      decide3 (RARROWL FW w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FW w0) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x2) (h2:=(S (S (S (S (S x)))))) (m:=x2 + (S (S (S (S (S x)))))) (w:=w1) (FCut:=F *** G0)...
    }
     { 
     apply RIMPLRInv1 in H4;auto;CleanContext.
   
     apply RARROWLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RARROWL FW w0)...
      tensor [d| (ARROW FW) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap.   
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[(FW w0) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S (S (S x)))))) (m:=x0 + S (S (S (S (S (S x)))))) (w:=w1) (FCut:=F --o G0)...
     - 
      decide3 (RARROWL FW w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FW w0) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S (S (S x)))))) (m:=x0 + S (S (S (S (S (S x)))))) (w:=w1) (FCut:=F --o G0)...
    }
   { 
     apply RATRInv1 in H4;auto;CleanContext.
   
     apply RARROWLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RARROWL FW w0)...
      tensor [d| (ARROW FW) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap.   
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[(FW w0) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=F AT v0)...
     - 
      decide3 (RARROWL FW w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FW w0) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=F AT v0)...
    } 
 { 

     apply RARROWRInv1 in H4;auto;CleanContext.
   
     apply RARROWLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    -  (* RARROW IS PRINCIPAL *)
     inversion H1...
     apply lbindEq in H3;auto.  
     
     eapply RARROW_PRINCIPAL with (FW:=FW) (FW0:=FW0) (n':=n') (w:=w0)...
     solveLL. exact H9.
     solveLL. 
     LLPermMap(REncode (G @ v) :: LEncode (Delta1 ++ [(FW w0) @ w0])).
     exact H4.
    - 

      apply (rewL1 _ _ H1).
      decide3 (RARROWL FW w0)...
      tensor [d| (ARROW FW) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).   
      permMap.  
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[(FW w0) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ARROW FW0)...
     - 
      decide3 (RARROWL FW w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1++Delta2)).   
     
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FW w0) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ARROW FW0)...
    }    
  
 { 
     apply BANGRInv1 in H4;auto;CleanContext.
   
     apply RARROWLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RARROWL FW w0)...
      tensor [d| (ARROW FW) @ w0 |]  (REncode (G @ v) :: LEncode x1).
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[(FW w0) @ w0]) ++ [])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=!! F)...
     - 
      decide3 (RARROWL FW w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode Delta1).
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FW w0) @ w0]) ++ [])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=!! F)...
    }     
    { 
     apply RALLRInv1 in H4;auto;CleanContext.
   
     apply RARROWLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RARROWL FW w0)...
      tensor [d|(ARROW FW) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap.   
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[(FW w0) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ALL FX)...
     - 
      decide3 (RARROWL FW w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FW w0) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ALL FX)...
    }  
    

     (* RBANGL LEFT in Hseq1 *)
   { 
     apply RINITInv1 in H4;auto.
     decompose [or and] H4;clear H4;CleanContext.
      * 
     apply WeakTheory with (theory:= OLTheory)...
     apply seqNtoSeq in Hseq1.
     LLExactMap' Hseq1.
    *
     apply BANGLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    -
      inversion H1...
      decide3 (RBANGL F1 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode Delta1 ++ []).   
      apply WeakTheory with (theory:= OLTheory)...
      apply seqNtoSeq in H3.
      LLExactMap' H3.
     - 
      apply (rewL1 _ _ H1).
      decide3 (RBANGL F1 w0)...
      tensor [d| (!! F1) @ w0 |]  (REncode (G @ v) :: LEncode x0).   
      LLPermMap (REncode (G @ v) :: LEncode (x0 ++ [])).
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
      LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H3.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
     - 
      decide3 (RBANGL F1 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode Delta1).
      LLPermMap (REncode (G @ v) :: LEncode (Delta1 ++ [])).
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
      LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H3.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
     }
     { 
     apply RTENSORRInv1 in H4;auto;CleanContext.
   
     apply BANGLInv2 in H1;auto.  
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RBANGL F1 w0)...
      tensor [d| (!! F1) @ w0 |]  (REncode (G @ v) :: LEncode (x3++Delta2)).
      permMap.   
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x2) (h2:=(S (S (S (S (S x)))))) (m:=x2 + (S (S (S (S (S x)))))) (w:=w1) (FCut:=F *** G0)...
      LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H4.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
     - 
      decide3 (RBANGL F1 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x2) (h2:=(S (S (S (S (S x)))))) (m:=x2 + (S (S (S (S (S x)))))) (w:=w1) (FCut:=F *** G0)...
       LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H4.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
    }
     { 
     apply RIMPLRInv1 in H4;auto;CleanContext.
   
     apply BANGLInv2 in H1;auto.  
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RBANGL F1 w0)...
      tensor [d| (!! F1) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap.   
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S (S (S x)))))) (m:=x0 + S (S (S (S (S (S x)))))) (w:=w1) (FCut:=F --o G0)...
      LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H3.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
     - 
      decide3 (RBANGL F1 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S (S (S x)))))) (m:=x0 + S (S (S (S (S (S x)))))) (w:=w1) (FCut:=F --o G0)...
       LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H3.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
   }
   { 
     apply RATRInv1 in H4;auto;CleanContext.
   
     apply BANGLInv2 in H1;auto.  
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RBANGL F1 w0)...
      tensor [d| (!! F1) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap.   
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=F AT v0)...
      LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H3.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.     
     - 
     decide3 (RBANGL F1 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=F AT v0)...
       LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H3.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
    } 
 { 
     apply RARROWRInv1 in H4;auto;CleanContext.
   
     apply BANGLInv2 in H1;auto.  
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RBANGL F1 w0)...
      tensor [d| (!! F1) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap.   
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ARROW FW)...
      LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H3.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
     - 
     decide3 (RBANGL F1 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ARROW FW)...
       LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H3.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
    }    
  
 { (* RBANG IS PRINCIPAL *)
     apply BANGRInv1 in H4;auto;CleanContext.
   
     apply BANGLInv2 in H1;auto.  
     decompose [or] H1;clear H1;CleanContext.
    -
     inversion H1...
     rewrite app_nil_r.
   
      eapply RBANG_PRINCIPAL with (F:=F1) (n':=n') (w:=w0)... 
       solveLL. exact H8.
      solveLL. exact H3.
     -
      apply (rewL1 _ _ H1).
      decide3 (RBANGL F1 w0)...
      tensor [d| (!! F1) @ w0 |]  (REncode (G @ v) :: LEncode (x1++[])).
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=!! F)...
      LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H3.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
     - 
      decide3 (RBANGL F1 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ [])).
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=!! F)...
       LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H3.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
    }     
    { 
     apply RALLRInv1 in H4;auto;CleanContext.
   
     apply BANGLInv2 in H1;auto.  
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RBANGL F1 w0)...
      tensor [d| (!! F1) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap.   
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ALL FX)...
      LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H3.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
     - 
     decide3 (RBANGL F1 w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      LLPermMap (LEncode (Gamma ++ [F1 @ w0])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ALL FX)...
       LLPermMap (LEncode Gamma ++ [d| F1 @ w0 |]).
      LLExactMap H3.
      LLPermMap ( [d| F1 @ w0 |] ++ LEncode Gamma).
      apply weakeningGenN.
      LLExactMap Hseq2.
    }
     { 
     apply RINITInv1 in H4;auto.
     decompose [or and] H4;clear H4;CleanContext.
      * 
     apply WeakTheory with (theory:= OLTheory).
     auto using TheoryInclusion.
     apply seqNtoSeq in Hseq1.
     LLExactMap' Hseq1.
    *
     apply RALLLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    -
      decide3 (RALLL FX w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode Delta1 ++ []).   
      apply WeakTheory with (theory:= OLTheory)...
      existential x0.
      apply seqNtoSeq in H9.
      LLExactMap' H9.
     - 
      apply (rewL1 _ _ H1).
      decide3 (RALLL FX w0)...
      tensor [d| (ALL FX) @ w0 |]  (REncode (G @ v) :: LEncode x0).
      existential x1.   
      LLPermMap (REncode (G @ v) :: LEncode ((x0++[(FX x1) @ w0]) ++ [])).
      eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
    - 
      decide3 (RALLL FX w0)... 
      tensor (@nil oo)  (REncode (G @ v) :: LEncode Delta1).
      existential x0.
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FX x0) @ w0]) ++ [])).
      eapply IH with (h1:=x) (h2:=S n1) (m:=x + S n1) (w:=w1) (FCut:=F)...
     }
     
     { 
     apply RTENSORRInv1 in H4;auto;CleanContext.
     apply RALLLInv2 in H1;auto.
     decompose [or] H1;clear H1;CleanContext.
    -
      inversion H1...
   -    
      apply (rewL1 _ _ H1).
      decide3 (RALLL FX w0)...
      tensor [d| (ALL FX) @ w0 |]  (REncode (G @ v) :: LEncode (x3++Delta2)).
      permMap.
      existential x4.  
      LLPermMap (REncode (G @ v) :: LEncode ((x3++[(FX x4) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x2) (h2:=(S (S (S (S (S x)))))) (m:=x2 + (S (S (S (S (S x)))))) (w:=w1) (FCut:=F *** G0)...
     - 
      decide3 (RALLL FX w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      existential x3. 
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FX x3) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x2) (h2:=(S (S (S (S (S x)))))) (m:=x2 + (S (S (S (S (S x)))))) (w:=w1) (FCut:=F *** G0)...
    }
     { 
     apply RIMPLRInv1 in H4;auto;CleanContext.
   
     apply RALLLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RALLL FX w0)...
      tensor [d| (ALL FX) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap. existential x2.  
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[(FX x2) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S (S (S x)))))) (m:=x0 + S (S (S (S (S (S x)))))) (w:=w1) (FCut:=F --o G0)...
     - 
      decide3 (RALLL FX w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      existential x1. 
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FX x1) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S (S (S x)))))) (m:=x0 + S (S (S (S (S (S x)))))) (w:=w1) (FCut:=F --o G0)...
    }
 { 
     apply RATRInv1 in H4;auto;CleanContext.
   
     apply RALLLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RALLL FX w0)...
      tensor [d| (ALL FX) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap. existential x2.  
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[(FX x2) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:= S (S (S (S x))))  (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=F AT v0)...
     - 
      decide3 (RALLL FX w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      existential x1. 
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FX x1) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:= S (S (S (S x))))  (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=F AT v0)...
    }    
    { 
     apply RARROWRInv1 in H4;auto;CleanContext.
   
     apply RALLLInv2 in H1;auto.
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RALLL FX w0)...
      tensor [d| (ALL FX) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap.   existential x2.
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[(FX x2) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ARROW FW)...
     - 
      decide3 (RALLL FX w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      existential x1.
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FX x1) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ARROW FW)...
    } 
 { 
     apply BANGRInv1 in H4;auto;CleanContext.
   
     apply RALLLInv2 in H1;auto. 
     decompose [or] H1;clear H1;CleanContext.
    - discriminate H1.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RALLL FX w0)...
      tensor [d| (ALL FX) @ w0 |]  (REncode (G @ v) :: LEncode x1).
      existential x2.
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[(FX x2) @ w0]) ++ [])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=!! F)...
     - 
      decide3 (RALLL FX w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode Delta1).
      existential x1.
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FX x1) @ w0]) ++ [])).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=!! F)...
    }     
    { 
     apply RALLRInv1 in H4;auto;CleanContext.
   
     apply RALLLInv2 in H1;auto.
     decompose [or] H1;clear H1;CleanContext.
    - (* RALL IS PRINCIPAL *)
      inversion H1...
      apply lbindEq in H3...
      eapply RALL_PRINCIPAL with (FX:=FX) (FX0:=FX0) (n':=n') (w:=w0)...
      inversion H6...
      existential x1.
      LLPermMap ((REncode (G @ v) :: LEncode (Delta1 ++ [(FX x1) @ w0]))).
      exact H12.
    - 
      apply (rewL1 _ _ H1).
      decide3 (RALLL FX w0)...
      tensor [d| (ALL FX) @ w0 |]  (REncode (G @ v) :: LEncode (x1++Delta2)).
      permMap.
      existential x2. 
      LLPermMap (REncode (G @ v) :: LEncode ((x1++[(FX x2) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ALL FX0)...
     - 
      decide3 (RALLL FX w0)...
      tensor (@nil oo)  (REncode (G @ v) :: LEncode (Delta1 ++ Delta2)).
      existential x1. 
      LLPermMap (REncode (G @ v) :: LEncode ((Delta1++[(FX x1) @ w0]) ++ Delta2)).
      eapply IH with (h1:=x0) (h2:=S (S (S (S x)))) (m:=x0 + S (S (S (S x)))) (w:=w1) (FCut:=ALL FX0)...
  }  

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
                              seq OLTheory (LEncode Gamma) (REncode (F @ w) :: (LEncode L)) (> []).
Proof with autounfold with enc;IS;solveF;try easyF.
 intros.
  induction H... 
  + (* init *)
    decide3 (RINIT F1 wexp).
    tensor [REncode (F1 @ wexp)] [d| F1 @ wexp |].
  + decide3 (RTENSORL A B w0)...
    tensor [d| (A *** B) @ w0 |] (REncode (F0 @ wexp) :: LEncode L).
    
    LLPermMap  (REncode (F0 @ wexp) :: d| A @ w0 | :: d| B @ w0 | :: LEncode L).
    apply  IHHyLL...
  + (* tensor right *)
    decide3 (RTENSORR A B w0)...
    tensor [(REncode ((A *** B) @ w0))] (LEncode (L ++ L')) .
    LLPermMap(LEncode L ++ LEncode L'). 
    tensor. 
    LLPermMap (REncode (A @ w0) :: LEncode L).
    apply IHHyLL1...
    LLPermMap (REncode (B @ w0) :: LEncode L').
    apply IHHyLL2...
  + (* implication left *)
    decide3 (RIMPLL A B w0)...
    tensor  [d| (A --o B) @ w0 |] (REncode (F0 @ wexp) :: LEncode (L ++ L')).
    tensor  (LEncode L) (REncode (F0 @ wexp) :: LEncode L'). permMap.
    LLPermMap (REncode (A @ w0) :: LEncode L).
    apply IHHyLL1...
    LLPermMap (u| F0 @ wexp | :: d| B @ w0 | :: LEncode L') .
    apply IHHyLL2...
  +
    decide3 (RIMPLR A B w0)...
    tensor  [REncode ((A --o B) @ w0)] (LEncode L).
    LLPermMap ([REncode (B @ w0)] ++ [d| A @ w0 |] ++ (LEncode L))...
  + (* at  *)
    decide3 (RATL A v w0)...
    tensor [d| (A AT v) @ w0 |] (REncode (F0 @ wexp) :: LEncode L).
    LLPermMap (REncode (F0 @ wexp) :: d| A @ v | :: LEncode L).
    apply IHHyLL...
  + (* at *)
    decide3 (RATR A v w0)...
    tensor [u| (A AT v) @ w0 |] ( LEncode L).
    LLPermMap (REncode (A @ v) :: LEncode L).
    apply IHHyLL...
  + (* arrow *)
    decide3 (RARROWL FW w0)...
    (* automatize here *)
    apply ll_arrowL...
    constructor...
    apply isFArrow...
    intros.
    rewrite <- H2...
    (* ***** *)
    tensor [d| (ARROW FW) @ w0 |] (REncode (F0 @ wexp) :: LEncode L).

    LLPermMap (REncode (F0 @ wexp) :: d| (FW w0) @ w0 | :: LEncode L).
    apply IHHyLL...
    constructor...
    rewrite <- H2...
  + (* arrow *)
    decide3 (RARROWR FW w0)...
    (* automatize here *)
    apply ll_arrowR...
    constructor...
    apply isFArrow...
    intros.
    rewrite <- H2...
    (* ***** *)
    tensor [REncode ((ARROW FW) @ w0)] (LEncode L).

    LLPerm (u| (FW w0) @ w0 | :: LEncode L).
    apply IHHyLL...
    constructor...
    rewrite <- H2...
  + (* bang *)
    decide3 (RBANGL F0 w0)...
    tensor [d| (!! F0) @ w0 |] (REncode (F1 @ wexp)  :: LEncode L).
    LLPermMap (LEncode (F0 @ w0 :: Gamma)).
    apply IHHyLL...
  + (* bang *)
    decide3 (RBANGR F0 w0)...
    tensor [REncode ((!! F0) @ w0)] (@nil oo).
  + (* copy *)
    decide3 (RCOPY F0 w0)...
    constructor...
   
    apply (Utils.isFormulaIn H0 H).
    tensor (@nil oo)(REncode (F1 @ wexp) :: LEncode L) .
    eapply in_map in H. exact H.
    LLPermMap (REncode (F1 @ wexp) :: d| F0 @ w0 | :: LEncode L).
    apply IHHyLL...
    apply (Utils.isFormulaIn H0 H).   
  + (* quantifier *)
    decide3 (RALLL FX w0)...
    constructor...
    constructor...
    constructor...
    intros. rewrite <- H2...
    tensor [d| (ALL FX) @ w0| ] (REncode (F0 @ wexp)  :: LEncode L) .
    existential t.
    LLPermMap (REncode (F0 @ wexp) :: d| (FX t) @ w0 | :: LEncode L).
    apply IHHyLL...
    constructor...
    rewrite <- H2...

  + decide3 (RALLR FX w0)...
    constructor...
    constructor...
    constructor...
    intros. rewrite <- H2...
    tensor [REncode ((ALL FX) @ w0) ]  (LEncode L).
    specialize(H4 x properX).
    LLPermMap (REncode ((FX x) @ w0) :: LEncode L).
    apply H4...
    constructor...
    rewrite <- H2...

  + (* permutation *)

    assert(isOLFormulaL L'). 

    apply (PermuteMap H1);auto. 
    assert(Permutation (LEncode L) (LEncode L')).
    apply Permutation_map; auto. 

    rewrite H6...

Qed.

Lemma downINLEncode : forall F L, In (d| F |) (LEncode L) -> In F L.
Proof with subst;auto.   
   intros.
   eapply in_map_iff in H.
   inversion H as [x Hx]. 
   inversion Hx...
   inversion H0... 
Qed.
     
Theorem Completeness: forall  n Gamma L F w , 
 isOLFormula (F @ w) -> isOLFormulaL Gamma -> isOLFormulaL L ->
                      seqN  OLTheory n (LEncode Gamma) (REncode (F @ w) :: (LEncode L)) (> []) ->
                      HyLL Gamma L (F @ w).
Proof with solveF; try easyF.
  induction n using strongind;intros...
  inversion H2.

  inversion H3...
  *
    apply Remove_In in H6...
    apply in_inv in H6.

    destruct H6...
    + 
      assert(IsPositiveAtom (REncode (F @ w))) by constructor.
      contradiction.
    +
      apply in_map_iff in H4.
      do 2 destruct H4...
  *
    apply in_map_iff in H6.
    destruct H6...
  * 
    inversion H5;CleanContext...
    + (* init *)
     apply RINITInv1 in H7;
     decompose [or and] H7;clear H7;CleanContext...
     apply downINLEncode in H11...
     assert(Hid: HyLL Gamma [F1 @ w0] (F1 @ w0)) by auto.
     eapply (hy_copy H11 Hid)...
    + (* tensor left *)
      apply RTENSORLInv1 in H7;
      decompose [or and] H7;clear H7;CleanContext...
     
      apply (hy_exange H7).
      apply hy_tenL...
      eapply (H x)... easyF.
      LLExactMap H8.
      
      apply downINLEncode in H7...
      eapply (hy_copy H7).
      apply hy_tenL...
      eapply (H x)... 
      LLExactMap H8.
      + (* tensor right *)
      apply RTENSORRInv1 in H7;auto;CleanContext.
      apply (hy_exange H7).

      apply hy_tenR...
      
       eapply (H x)...  
       LLExactMap H10.
       
       eapply (H x)...  
       LLExactMap H11.
    + (*  implication left *)
      apply RIMPLLInv1 in H7;
     decompose [or and] H7;clear H7;CleanContext...
     { apply (hy_exange H7).
       apply hy_impL...     
       * eapply (H x)...  
         LLExactMap H8.
       * eapply (H x)...   
         LLExactMap H9. }
     { apply downINLEncode in H7...
       apply (hy_exange H8).
       eapply (hy_copy H7).   
       apply hy_impL...     
       * eapply (H x)...  
         LLExactMap H9.
       * eapply (H x)...   
         LLExactMap H10. }
    + (* implication right *)
      apply RIMPLRInv1 in H7;CleanContext...
      apply hy_impR.
      apply (H x)...
      LLExactMap H9.
    + (* at left *)
      apply RATLInv1 in H7;
      decompose [or and] H7;clear H7;CleanContext...
      { apply (hy_exange H7).
        apply hy_atL.
        apply (H x)...
        LLExactMap H8. }
      { apply downINLEncode in H7...
        eapply (hy_copy H7).   
        apply hy_atL.     
        eapply (H x)...
        LLExactMap H8. } 
    + (* at right *)
      apply RATRInv1 in H7;CleanContext...
      apply hy_atR.
      apply (H x)...
      LLExactMap H9.
    + (* arrow Left *)
      apply RARROWLInv1 in H7;
      decompose [or and] H7;clear H7;CleanContext...
      { apply (hy_exange H7).
        apply hy_arrowL;auto.
        inversion H8...
        apply (H x)...
        LLExactMap H9. }
      { apply downINLEncode in H7...
        eapply (hy_copy H7).   
        apply hy_arrowL;auto.
        inversion H8...     
        eapply (H x)...
        LLExactMap H9. } 
     + (* arrow right *)
      apply RARROWRInv1 in H7;CleanContext...
      apply hy_arrowR;auto.
      inversion H8...
      apply (H x)...
      LLExactMap H10.
     + (* bang left *)
      apply BANGLInv1 in H7;
      decompose [or and] H7;clear H7;CleanContext...
      { apply (hy_exange H7).
        apply hy_bangL.
        apply (H x)...
        LLExactMap H8. }
      { apply downINLEncode in H7...
        eapply (hy_copy H7).   
        apply hy_bangL;auto.
        eapply (H x)...
        LLExactMap H8. } 
   +  (* bang right *)
      apply BANGRInv1 in H7;CleanContext...
      apply hy_bangR.
      apply (H x)...
    + (* copy *)
      apply RCOPYInv1 in H7;
      decompose [or and] H7;clear H7;CleanContext...
      { apply (H x)... }
      { apply downINLEncode in H7...
        eapply (hy_copy H7).   
        eapply (H x)...
        LLExactMap H8. } 
    +  (* forall *)
      apply RALLLInv1 in H7;
      decompose [or and] H7;clear H7;CleanContext...
      { apply (hy_exange H7).
        eapply hy_allL with (t:=x1);auto.
        apply (H x)...
        LLExactMap H11. }
      { apply downINLEncode in H7...
        eapply (hy_copy H7).   
        eapply hy_allL with (t:=x0);auto.
        eapply (H x)...
        LLExactMap H11. } 
    +  (* forall *)
      apply RALLRInv1 in H7;CleanContext...
      apply hy_allR;auto.  
      intros.
      assert(Hyp: seqN OLTheory x (LEncode Gamma) (LEncode L) (> [u| (FX t) @ w0 |]))...
      inversion Hyp...     
      apply (H n)...
      LLExactMap H16.        
Qed.
End HyLL.
