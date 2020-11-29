(*  ** HyLL as an LL theory 

This file encodes the inference rules of Hybrid Liner logic (HyLL) as
an LL theory. The encoding was originally proposed in

Hybrid linear logic, revisited by Kaustuv Chaudhuri, Joëlle
Despeyroux, Carlos Olarte, Elaine
Pimentel. Math. Struct. Comput. Sci. 29(8): 1151-1176 (2019)

and it is adequate at the level of derivations *)



Require Export FLL.Misc.Hybrid.
Require Import Coq.Init.Nat.
Require Import FLL.SL.CutElimination.
Import FLL.Misc.Permutations.
Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Hint Constructors seq seqN : core .
Hint Constructors uniform_oo : core.
Hint Constructors isFormula : core.

Section HyLL.
  Variable W : Set. (* Set of Worlds *)
  Variable ID : W.
  Variable T : Set. (* Terms of the object logic *)

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

  Notation "'u|' A '|'" := (atom (up A)) (at level 10) .
  Notation "'d|' A '|'" := (atom (down A)) (at level 10) .
  Notation "'dd|' A '|'" := (atom (ddown A)) (at level 10) .
  Notation "'u^|' A '|'" := (perp (up A)) (at level 10) .
  Notation "'d^|' A '|'" := (perp (down A)) (at level 10) .
  Notation "'dd^|' A '|'" := (perp (ddown A)) (at level 10) .

  (** Inductive definition of HyLL sequents. This definition will be
  used to prove that the encoding is sound and complete *)

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

  (** *** The encoding *)

  (** The following definition encode the inference rules of HyLL *)
  Definition RINIT (F:uexp) (w:uexp) : oo := u^|F @ w|  ** ( d^|F @ w| ) .
  Definition RTENSORL (F G w :uexp) :oo := d^| (F *** G) @ w| ** (d|F @ w| $ d|G @ w|).
  Definition RTENSORR (F G w :uexp) :oo := u^| (F *** G) @ w| ** (u|F @ w| ** u|G @ w|).
  Definition RIMPLL (F G w Right : uexp) : oo := d^| (F --o G) @ w | ** (u^|Right| ** ( u|F @ w| ** (u|Right| $ d|G @ w|))).
  Definition RIMPLR (F G w : uexp) : oo := u^| (F --o G) @ w| ** (d|F @ w| $ u|G @ w|) .
  Definition RATL (F v w : uexp) := d^|(F AT v) @ w| ** d| F @ v| .
  Definition RATR (F v w : uexp) := u^|(F AT v) @ w| ** u| F @ v|.
  Definition RARROWL FW w := d^| (ARROW FW) @ w| ** d| (FW w) @ w|.
  Definition RARROWR FW w := u^| (ARROW FW) @ w| ** u| (FW w) @ w|.
  Definition RBANGL F w := d^| (!! F) @ w| ** ? dd|F @ w|.
  Definition RBANGR F w := u^| (!! F) @ w| ** ! u|F @ w|.
  Definition RCOPY F w := dd^| F @ w| ** d| F @ w| . 
  Definition RALLL FX w := d^|(ALL FX) @ w| ** E{ fun x => d|(FX x) @ w|} .
  Definition RALLR FX w := u^|(ALL FX) @ w| ** F{ fun x => u|(FX x) @ w|}.

  Hint Unfold RINIT RTENSORL RTENSORR RIMPLL RIMPLR RATL RATR RARROWL RARROWR RBANGL RBANGR RCOPY  RALLL RALLR : enc.
  
  Inductive OLTheory  : oo ->  Prop :=
  | ll_init : forall F w, isOLFormula (F @ w) -> OLTheory(RINIT  F w)
  | ll_tenL : forall F G w , isOLFormula ((F *** G) @ w)  -> OLTheory (RTENSORL F G w)
  | ll_tenR : forall F G w, isOLFormula ((F *** G) @ w) -> OLTheory (RTENSORR F G w)
  | ll_implL : forall F G w R, isOLFormula ( (F --o G) @ w) -> isOLFormula R -> OLTheory(RIMPLL F G w R)
  | ll_implR : forall F G w, isOLFormula ((F --o G) @ w) -> OLTheory (RIMPLR F G w)
  | ll_atL : forall F v w , isOLFormula ((F AT v) @ w) -> OLTheory(RATL F v w )
  | ll_atR : forall F v w , isOLFormula ((F AT v) @ w) -> OLTheory( RATR F v w)
  | ll_arrowL : forall FW  w , uniform FW -> isOLFormula ( (ARROW FW) @ w) -> OLTheory( RARROWL FW w)
  | ll_arrowR : forall FW  w , uniform FW -> isOLFormula ( (ARROW FW) @ w) -> OLTheory( RARROWR FW w)
  | ll_bangL : forall F w, isOLFormula ( (!! F) @ w) -> OLTheory (RBANGL F w)
  | ll_bangR : forall F w, isOLFormula ( (!! F) @ w) -> OLTheory (RBANGR F w)
  | ll_copy : forall F w, isOLFormula (F @ w) -> OLTheory (RCOPY F w)
  | ll_allL : forall FX w, uniform FX ->  isOLFormula ((ALL FX) @ w) -> OLTheory(RALLL FX w)
  | ll_allR : forall FX w, uniform FX -> isOLFormula ((ALL FX) @ w) -> OLTheory(RALLR FX w).

  Definition LEncode L := map (fun x => d| x|) L.
  Definition CLEncode L := map (fun x => dd| x|) L. (* classical encoding *) 
  Definition REncode F := u| F|.
  
  Hint Constructors OLTheory: core.
  Hint Constructors isOLFormula : core.


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
  
  Ltac easyOLFormula :=
    match goal with  
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
  
  Ltac easyF := try apply ForallApp;auto; try solveOLFormula;try easyOLFormula.
  Ltac IS :=
    try
      match goal with
      |  [H : isOLFormulaL (_ :: _) |- _] =>  inversion H; clear H;subst;try IS
      |  [H : isOLFormula _ |- _ ] => inversion H; clear H;subst;try IS
      | [H: isOLFormula' (_ _ _) |- _] => inversion H;clear H;subst;try IS
      | [H: isOLFormula' (_ _) |- _]=> inversion H;clear H;subst;try IS
      | [H: lbind _ _ = _ |- _ ] => apply lbindEq in H;auto;subst
      end.

  Ltac permMap :=
    match goal with
    | |- Permutation _ _ => unfold REncode;unfold LEncode; unfold CLEncode;try rewrite !map_app;simpl;perm_simplify; fail "permMap failed"
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

  (** Soundness theorem *)
  Theorem Soundeness: forall Gamma L F w , HyLL Gamma L (F @ w) ->
                                           isOLFormulaL Gamma ->
                                           isOLFormulaL L ->
                                           isOLFormula (F @ w) ->
                                           seq OLTheory (CLEncode Gamma) (REncode (F @ w) :: (LEncode L)) (> []).
  Proof with IS;solveF;try easyF.
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
      decide3 (RIMPLL A B w0 ((F0 @ wexp))).
      tensor  [d| (A --o B) @ w0 |] (REncode (F0 @ wexp) :: LEncode (L ++ L')).
      tensor [ REncode (F0 @ wexp)] (LEncode (L ++ L')).
      LLPermMap (LEncode L ++ LEncode L').
      tensor.
      LLPermMap (REncode (A @ w0) :: LEncode L).
      apply IHHyLL1...
      LLPermMap (u| F0 @ wexp | :: d| B @ w0 | :: LEncode L') .
      apply IHHyLL2...
      constructor ...
    +
      decide3 (RIMPLR A B w0).
      tensor  [REncode ((A --o B) @ w0)] (LEncode L).
      LLPermMap ([REncode (B @ w0)] ++ [d| A @ w0 |] ++ (LEncode L))...
    + (* at  *)
      decide3 (RATL A v w0).
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
      LLPermMap (CLEncode (F0 @ w0 :: Gamma)).
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
      constructor...
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

  (* For completeness, better to prove some "invertibility" lemmas *)

  Theorem NoUPInCLEncode: forall F Gamma, ~ In (u| F |) (CLEncode Gamma).
    intros.
    intro HNeg.
    induction Gamma;simpl in*;auto.
    destruct HNeg.
    inversion H.
    apply IHGamma;auto.
  Qed.

  Theorem NoDOWNInCLEncode: forall F  Gamma, ~ In (d| F |) (CLEncode Gamma).
    intros.
    intro HNeg.
    induction Gamma;simpl in*;auto.
    destruct HNeg.
    inversion H.
    apply IHGamma;auto.
  Qed.

  Theorem NoDOWNInLEncode: forall F L, ~ In (dd| F |) (LEncode L).
    intros.
    intro HNeg.
    induction L;simpl in*;auto.
    destruct HNeg.
    inversion H.
    apply IHL;auto.
  Qed.

  Theorem NoUPInLEncode: forall F Gamma, ~ In (u| F |) (LEncode Gamma).
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

  Theorem NoUPinDOwn': forall F L F1 N,
      Permutation (u| F | :: map (fun x : uexp => d| x |) L) ([u| F1 |] ++ N) ->
      F = F1  /\ Permutation  (map (fun x : uexp => d| x |) L) N.
    intros.
    simpl in H.
    apply Permutation_sym in H.
    apply PermutationInCons in H as H'.
    inversion H'. inversion H0;subst.
    apply Permutation_cons_inv in H.
    split;auto. symmetry;trivial. 
    apply NoUPInLEncode in H0;contradiction.
  Qed.

  Theorem FocusinRightAtom: forall n Gamma F w L F1 w0 G,
      seqN OLTheory n (CLEncode Gamma) (REncode (F @ w) :: LEncode L) (>> u^| F1 @ w0 | ** G) ->
      exists n', n = (S n') /\
                 seqN OLTheory n' (CLEncode Gamma) (LEncode L) (>> G) /\
                 F = F1 /\ w = w0.
    intros.
    FLLInversionAll.
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
                 exists L', Permutation L  (F1 @ w0 :: L') /\
                            seqN OLTheory n' (CLEncode Gamma) (REncode (F @ w) :: LEncode L') (>> G).

    intros.
    FLLInversionAll.

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
    FLLInversionAll.
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

    FLLInversionAll.
    eexists.
    eexists.
    split;eauto.
    split;eauto.
    simpl in *.
    LLExact H8.
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
    FLLInversionAll.
    eexists;split; eauto.
    split; eauto.
    split; eauto.
    LLExactMap H7.
  Qed.

  Theorem RBANGLInv:  forall n Gamma G H w0 v L ,
      seqN OLTheory n (CLEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RBANGL H w0) ->
      (exists n' X,
          n = S (S (S n')) /\ Permutation L ((!! H) @ w0 :: X)
          /\ seqN OLTheory n' ((CLEncode Gamma) ++ [dd| H @ w0 |]) (REncode (G @ v) :: LEncode X) (> [])).
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H0;CleanContext.
    FLLInversionAll.
    eexists n0;
      eexists x0;
      split;auto.
  Qed.


  Theorem RBANGRInv:  forall n Gamma G H w0 v L ,
      seqN OLTheory n (CLEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RBANGR H w0) ->
      exists n' ,
        n = S (S (S n')) /\ L=[] /\ G = !! H /\ v = w0
        /\ seqN OLTheory n' (CLEncode Gamma) ([u| H @ w0 |]) (> []) .
  Proof with solveF.
    intros.
    apply FocusinRightAtom in H0;CleanContext.
    FLLInversionAll.
    
    symmetry in H0.
    apply map_eq_nil in H0.
    eexists n0;split; auto.
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

  Theorem RIMPLLInv:  forall n Gamma G F1 F2 R w0 v L ,
      seqN OLTheory n (CLEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RIMPLL F1 F2 w0 R) ->
      (exists n' X1 X2, n = S (S (S (S (S (S (S n')))))) /\ 
                        Permutation  L ((F1 --o F2) @ w0 ::  (X1 ++ X2)) /\ R = (G @ v) /\ 
                        (seqN OLTheory (S (S n')) (CLEncode Gamma) (LEncode X1 ++[u| F1 @ w0 |]) (> []))  /\
                        (seqN OLTheory n' (CLEncode Gamma) ((LEncode X2 ++ [u| G @ v |]) ++ [d| F2 @ w0 |]) (> [])) ).
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H;CleanContext.
    FLLInversionAll.
    - CleanContext.
      rewrite H2 in H3.
      clear H. clear H2.
      apply NoUPinDOwn' in H3.
      destruct H3;subst.
      symmetry in H1. apply AppEncode in H1.
      CleanContext.
      rewrite H in H0.
      eexists n0;
        eexists x1;
        eexists x2;split;auto.
    - CleanContext.
      assert(~ In (u| R |) (CLEncode Gamma)) by apply NoUPInCLEncode.
      contradiction.
  Qed.   


  Theorem RIMPLRInv:  forall n Gamma G F1 F2 w0 v L ,
      seqN OLTheory n (CLEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RIMPLR F1 F2 w0) ->
      (exists n', n = S (S (S (S (S n')))) /\
                  G = F1 --o F2 /\ v = w0 /\ 
                  (seqN OLTheory n' (CLEncode Gamma) (LEncode L ++ [d| F1 @ w0 |; u| F2 @ w0 |]) (> []))) .
  Proof with solveF. 
    intros.
    apply FocusinRightAtom in H;CleanContext.
    FLLInversionAll.
    eexists n0;
      split;auto.
    split;auto.
    split;auto.
    LLExactMap H8.
  Qed. 

  
  Theorem RTENSORLInv:  forall n Gamma G F1 F2 w0 v L ,
      seqN OLTheory n (CLEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RTENSORL F1 F2 w0) ->
      (exists n' X, n = S (S (S (S (S n')))) /\ Permutation  L ((F1 *** F2) @ w0 :: X)  /\ 
                    (seqN OLTheory n' (CLEncode Gamma) (REncode (G @ v) :: LEncode (X ++ [F1 @ w0] ++ [F2 @ w0])) (> []))).
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H;CleanContext.
    FLLInversionAll.
    eexists n0.
    eexists x0;split;auto.
    split;eauto.
    LLExactMap H9.
  Qed.
  
  Theorem RTENSORRInv:  forall n Gamma G F1 F2 v w0 L ,
      seqN OLTheory n (CLEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RTENSORR F1 F2 w0) ->
      exists n' M N,
        n = S (S (S (S n'))) /\ Permutation L (M ++ N) /\ G = F1 *** F2 /\ v = w0
        /\ seqN OLTheory n' (CLEncode Gamma) (LEncode M ++ [u| F1 @ w0 |]) (> [])
        /\ seqN OLTheory n' (CLEncode Gamma) (LEncode N ++ [u| F2 @ w0 |]) (> []) .
  Proof with solveF.
    intros.
    apply FocusinRightAtom in H;CleanContext.
    FLLInversionAll.
    CleanContext.

    symmetry in H2.
    apply AppEncode in H2.
    destruct H2...
    do 2 destruct H.
    CleanContext. 
    do 3 eexists;
      split;eauto;
        split;eauto;
          split;eauto;
            split;eauto.
  Qed.

  Theorem RCOPYInv: forall n Gamma G v L F w0,
      seqN OLTheory n (CLEncode Gamma) (REncode (G @ v) :: LEncode L) (>>RCOPY F w0) ->
      (exists n',
          n = S ( S ( S n')) /\ In (dd| F @ w0 |) (CLEncode Gamma) /\
          seqN OLTheory n' (CLEncode Gamma) ((REncode (G @ v) :: LEncode L) ++ [d| F @ w0 |]) (> [])).
  Proof with solveF.
    intros.
    unfold RCOPY in H.
    FLLInversionAll.
    - 
      apply Permutation_sym in H2.
      apply PermutationInCons in H2 as H2'.
      inversion H2'.
      inversion H1... 
      assert(~ In (dd| F @ w0 |) (LEncode L)) by apply  NoDOWNInLEncode.
      contradiction.
    - 
      rewrite <- H2 in H10.
      eexists n0;split;auto.
  Qed. 
  
  Theorem RALLLInv: forall n Gamma G v L FX w0,
      seqN OLTheory n (CLEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RALLL FX w0) ->
      (exists n' X t,
          n = S (S ( S ( S n'))) /\  Permutation L ((ALL FX) @ w0 :: X) /\
          proper t /\ uniform_oo (fun x => d| (FX x) @ w0 |) /\
          seqN OLTheory n' (CLEncode Gamma) (REncode (G @ v) :: LEncode (X ++
                                                                           [(FX t) @ w0 ])) (> [])) .
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H;CleanContext.
    FLLInversionAll.
    eexists n.
    eexists x0. 
    exists t; 
      split; eauto.
    split; eauto.
    split; eauto.
    split; eauto. 
    LLExactMap H10.    
  Qed.
  
  
  Theorem RALLRInv: forall n Gamma G v L FX w0,
      seqN OLTheory n (CLEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RALLR FX w0) ->
      (exists n',
          n = (S ( S ( S n'))) /\  G = ALL FX /\ v = w0 /\ uniform_oo
                                                             (fun x => u| (FX x) @ w0 |) /\
          forall x,
            proper x -> seqN OLTheory n' (CLEncode Gamma) (LEncode L) (> [u| (FX x) @ w0 |])).
  Proof with solveF.
    intros.
    apply FocusinRightAtom in H;CleanContext.
    FLLInversionAll.
    eexists n0;split; eauto. 
  Qed.
  
  
  Theorem RARROWLInv: forall n Gamma G v L FW w0,
      seqN OLTheory n (CLEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RARROWL FW w0) ->
      (exists n' X,
          n = S ( S ( S n')) /\ Permutation L ((ARROW FW) @ w0 :: X) /\
          seqN OLTheory n' (CLEncode Gamma) (REncode (G @ v) :: LEncode (X ++
                                                                           [(FW w0) @ w0 ])) (> [])).
  Proof with solveF.
    intros.
    apply FocusinLeftAtom in H;CleanContext.
    FLLInversionAll.
    eexists n0.
    eexists x0;split; eauto.
    split; eauto.
    LLExactMap H8.
  Qed.
  

  Theorem RATRInv:  forall n Gamma G F w0 w1 v L ,
      seqN OLTheory n (CLEncode Gamma) (REncode (G @ v) :: LEncode L) (>> RATR F w1 w0) ->
      ( (exists n', n = S (S (S n')) /\
                    G = F AT w1 /\ v = w0 /\ seqN OLTheory n' (CLEncode Gamma) (LEncode L ++ [u| F @ w1 |]) (> []))) .
  Proof with solveF.
    intros.
    apply FocusinRightAtom in H;CleanContext. 
    FLLInversionAll.
    eexists n0;split;auto.
  Qed.
  

  Theorem Completeness: forall  n Gamma L F w , 
      seqN  OLTheory n (CLEncode Gamma) (REncode (F @ w) :: (LEncode L)) (> []) ->
      HyLL Gamma L (F @ w).
  Proof with solveF.
    induction n using strongind;intros...
    inversion H.

    inversion H0...
    *

      apply Remove_In in H3...
      apply in_inv in H3.

      destruct H3...
    + 
      assert(IsPositiveAtom (REncode (F @ w))) by constructor.
      contradiction.
    +
      apply in_map_iff in H1.
      do 2 destruct H1...
      *
        apply in_map_iff in H3.
        destruct H3...
      * 
        inversion H2...
    + (* init *)
      apply RINITInv in H4;CleanContext...
    + (* tensor left *)
      apply RTENSORLInv in H4;CleanContext. 
      apply (hy_exange H4).

      apply hy_tenL...
      eapply (H x)...
      LLExactMap H5.
    + (* tensor right *)
      apply RTENSORRInv in H4;CleanContext...
      apply (hy_exange H4).

      apply hy_tenR...
      
      ** 
        eapply (H x)...  
        LLExactMap H7.
      **
        eapply (H x)...  
        LLExactMap H8.
    + (*  implication left *)
      apply RIMPLLInv in H4.
      CleanContext.
      apply (hy_exange H4).

      apply hy_impL...
      
      ** 
        eapply (H (S (S x)))...  
        LLExactMap H7.
      **
        eapply (H x)...  
        LLExactMap H8.
    + (* implication right *)
      apply RIMPLRInv  in H4.
      CleanContext.
      apply hy_impR.
      apply (H x)...
      LLExactMap H6.
    + (* at left *)
      apply RATLInv in H4.
      CleanContext.
      apply (hy_exange H4).
      apply hy_atL.
      apply (H x)...
    + (* at right *)
      apply RATRInv in H4.
      CleanContext...
      apply hy_atR.
      apply (H x)...
      LLExactMap H6.
    + (* arrow Left *)
      apply RARROWLInv in H4.
      CleanContext...
      apply (hy_exange H4).
      apply hy_arrowL.
      inversion H5...
      inversion H5...
      apply (H x)...
      LLExactMap H6.
    + (* arrow right *)
      apply RARROWRInv in H4.
      CleanContext.
      apply hy_arrowR.
      inversion H5...
      inversion H5...
      apply (H x)...
    + (* bang left *)
      apply RBANGLInv in H4.
      CleanContext...
      apply (hy_exange H4).
      apply hy_bangL...
      apply (H x)...
      LLExactMap H5.
    +  (* bang right *)
      apply RBANGRInv in H4.
      CleanContext...
      apply hy_bangR...
      apply (H x)...
    + (* copy *)
      apply RCOPYInv in H4.
      CleanContext...
      apply in_map_iff in H4.
      inversion H4...
      subst.
      apply (hy_copy H6). 
      apply (H x)...
      LLExactMap H5.
    +  (* forall *)
      apply RALLLInv in H4.
      CleanContext...
      apply (hy_exange H4).
      apply hy_allL with (t:=x1)...
      apply (H x)...
      LLExactMap H8.        
    +  (* forall *)
      apply RALLRInv in H4.
      CleanContext...
      apply hy_allR...  
      intros.
      assert(Hyp: seqN OLTheory x (CLEncode Gamma) (LEncode L) (> [u| (FX t) @ w0 |]))...
      inversion  Hyp...     
      apply (H n)...
      LLExactMap H13.        

  Qed.
End HyLL.
