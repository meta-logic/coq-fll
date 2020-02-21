(**  Some simple examples about the use of the library.
 *)

Require Export FLL.Misc.Hybrid.
Require Export FLL.SL.FLLTactics.
Require Export FLL.Misc.Permutations.
Require Import Coq.Init.Nat.
Require Import Coq.Init.Nat.

Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
Hint Resolve proper_APP uniform_proper : hybrid.
Hint Unfold proper: hybrid.
Hint Rewrite ext_eq_eta : hybrid.
Hint Resolve uniform_id uniform_con uniform_app : hybrid.
Hint Resolve lbindEq exprInhabited : hybrid.
Hint Constructors seq seqN : core.
Hint Resolve uniform_id : core.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


Module Example1 .

  (** LL quantification on [nat] *)
  Definition con' := nat .
  Definition uexp := expr con' .

  (** a unique unary predicate *)
  Inductive Atom:Set :=
  | p : uexp -> Atom.
  
  Definition Var : var -> uexp := (VAR con').
  Definition Bnd : bnd -> uexp := (BND con').

  Inductive uniform_atm' : (uexp -> Atom) -> Prop :=
  | uniform_p: forall FX, uniform FX -> uniform_atm' (fun x:uexp => p (FX x))
  .
  Hint Constructors uniform_atm' : core .
  
  (** Instance of the LL signature *)
  Instance Signature : OLSig :=
    {| 
      con := con';
      atm := Atom;
      uniform_atm := uniform_atm'
    |}.
  

  Notation " '|--' B ';' L ';' X " := (seq EmptyTheory  B L X) (at level 80).

  Example Test1:  |-- [] ; [] ; >> one ** one .
  Proof with solveLL';eauto.
    eapply tri_tensor' with (M:=[]) (N:=[]) ...
  Qed.
  

  Example Test2: |-- [] ; [] ; > [  F{ fun t => perp (p t)} ; E{ fun t => atom (p t)}  ].
  Proof with solveF.
    solveLL'.
    decide1' (E{ fun t  => (atom (p t))}) ...
    existential' x.
    solveLL'.
  Qed.

  Example Test2': |-- [] ; [] ; > [  perp (p (Var 0)) ; atom (p (Var 0))  ].
  Proof with solveF.
    solveLL'.
    decide1' (perp (p (Var 0))).
  Qed.

  
  Example Test3: |-- [] ; [] ; > [  E{ fun t => perp (p t)} ; E{ fun t => atom (p t)}  ].
  Proof with solveF.
    solveLL'.
    decide1' (E{ fun t  => (atom (p t) )}) ...
    existential' (VAR con 0) ...
    solveLL'.
    decide1' (E{ fun t  => (perp (p t) )}) ...
    existential' (VAR con 0).
  Qed.


  Example Test4: |-- [atom (p (CON 0)) ] ; [] ; > [  perp (p (CON 0))  ].
  Proof with solveF.
    solveLL'.
    decide1' (perp (p (CON 0)))...
    solveLL'.
    constructor...
  Qed.

End Example1.

Module Example2.

  (** Definition of the natural numbers *)
  Inductive Econ : Set :=
  | z :  Econ (* zero *)
  | suc : Econ. (* successor *)
  Definition uexp : Set := expr Econ.
  
  Inductive Atom:Set :=
  | p : uexp -> Atom.
  
  Definition Var : var -> uexp := (VAR Econ).
  Definition Bnd : bnd -> uexp := (BND Econ).
  
  Inductive uniform_atm' : (uexp -> Atom) -> Prop :=
  | uniform_p: forall FX, uniform FX -> uniform_atm' (fun x:uexp => p (FX x))
  .

  (** More suitable constructors to work with *)
  Definition Z   := (CON z) .
  Definition SUC : uexp -> uexp  := fun N:uexp => (APP (CON suc) N) .

  Hint Constructors uniform_atm'  : core.

  Instance Signature : OLSig :=
    {| 
      con := Econ;
      atm := Atom;
      uniform_atm := uniform_atm'
    |}.
  
  Notation " n '|---' B ';' L ';' X " := (seqN EmptyTheory n B L X) (at level 80).
  Notation " '|--' B ';' L ';' X " := (seq EmptyTheory  B L X) (at level 80).

  Example test1 : |-- [ atom (p Z) ]; [perp (p Z)]; > [].
  Proof with solveLL';solveF.
    decide1' (perp (p Z) ) ...
  Qed.

  Definition step := fun t:uexp => perp (p t) ** atom (p (SUC t)).
  Definition TWO := SUC (SUC  Z) .
  
  Example test2 : |-- [ E{ step} ]; []; > [perp (p Z) -o perp (p TWO) ].
  Proof with solveLL';solveF.
    simpl...
    decide2' (E{ step}) ...
    existential' Z ... 
    tensor' [atom (p Z)] [perp (p TWO) ] ...
    decide2' (E{ step}) ... 
    existential' (SUC Z)...
    tensor' [atom (p (SUC Z)) ] [perp (p TWO) ] ... 
    decide1' (perp (p TWO) ) ...
  Qed.
  

  (** This is NOT a theorem ... Note that we cannot do induction on uexp terms *)
  Example test3 : |-- [ atom (p Z) ; E{ step} ]; []; > [F{ fun t => perp ( p t) }].
  Proof with solveLL';solveF.
    solveLL'.
    induction x.
    (* this will never work *)
  Abort.

  Example test4 : |-- [ ]; []; > [F{ fun t => atom (p t)} ; E{ fun t => perp (p t)}].
  Proof.
    solveLL'.
    decide1' (E{ fun t => perp (p t)}).
    existential' x.
  Qed.

  Example test4' : forall x, proper x -> |-- [ ]; []; > [atom (p x) ; E{ fun t => perp (p t)}].
  Proof.
    intros.
    solveLL'.
    decide1' (E{ fun t => perp (p t)}).
    existential' x.
  Qed.
End Example2.
