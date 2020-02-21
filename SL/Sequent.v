(** * Focused Sequent system 
This file specifies a one-sided focused system for first-order
classical linear logic. The system is parametric to [theory:
oo->Prop], defining the formulas that can be used in rule
[tri_dec3]. In this implementation, all the atoms are assumed to be
positive and then, proofs must finish with the initial rule focusing
on atomic propositions of the form [perp A]. The exchange rule is
embedded in the definition, e.g., of [tri_tensor]. 
 *)


Require Export FLL.Misc.Utils. 
Require Export FLL.SL.Syntax.

Export ListNotations.
Set Implicit Arguments.

Section LLSequent.
  Context `{OLS: OLSig}.
  Variable theory : oo -> Prop. (* theory Definition *)

  (* Andreoli's triadic system for linear logic *)
  Reserved Notation " n '|-F-' B ';' L ';' X " (at level 80).

  (** Sequent rules. in [n '|-F-' B ';' L ';' X], [n] is the height of
  the derivation ; [B] a list representing the classical context ; [L]
  the linear context and [X] and [Arrow] that can be [DW F] (for the
  positive phase) or [UP L] (for the negative phase). *)
  Inductive seqN:  nat -> multiset oo -> multiset oo -> Arrow -> Prop :=
  | tri_init1 : forall B A n,  n |-F- B ; [atom A] ; DW (perp A)
  | tri_init2 : forall B A n,  In (atom A) B -> n |-F- B ; [] ; DW (perp A)
  | tri_one : forall B n,  n |-F- B ; [] ; DW One
  | tri_tensor : forall B M N MN F G n, Permutation MN (M++N) ->
                                        (n |-F- B ; M ; DW F) ->
                                        (n |-F- B ; N ; DW G )->
                                        S n |-F- B ; MN ; DW (MAnd F G)
  | tri_plus1 : forall B M F G n,
      n |-F- B ; M ; DW F -> S n |-F- B ; M ; DW (AOr F G)
  | tri_plus2 : forall B M F G n,
      n |-F- B ; M ; DW G -> S n |-F- B ; M ; DW (AOr F G)
  | tri_bang : forall B F n,
      n |-F- B ; [] ; UP [F] -> S n  |-F- B ; [] ; DW (Bang F)
  | tri_rel : forall B F L n,
      release F -> n |-F- B ; L ; UP [F] ->  S n |-F- B ; L ; DW F
  | tri_top : forall B L M n,
      n |-F- B ; L ; UP (Top :: M)
  | tri_bot : forall B L M n,
      n |-F- B ; L ; UP M -> S n  |-F- B ; L ; UP (Bot :: M)
  | tri_par : forall B L M F G n,
      n |-F- B ; L ; UP (F::G::M) -> S n  |-F- B ; L ; UP((MOr F G) :: M)
  | tri_with : forall B L M F G n,
      (n |-F- B ; L ; UP (F :: M)) ->
      (n |-F- B ; L ; UP (G :: M)) -> S n|-F- B ; L ; UP ((AAnd F  G) :: M)
  | tri_quest : forall B L M F n,
      n |-F- B ++ [F] ; L ; UP M -> S n  |-F- B ; L ; UP ((Quest F) :: M)
  | tri_store : forall B L M F n,
      ~ asynchronous  F-> n |-F- B ; L ++ [F] ; UP M -> S n |-F- B ; L ; UP (F::M)
  | tri_dec1 : forall B L L' F n,
      ~IsPositiveAtom F -> remove F L L' -> n |-F- B ; L' ; DW F -> S n |-F- B ; L ; UP []
  | tri_dec2 : forall B L F n,
      ~IsPositiveAtom F -> In F B -> n |-F- B ; L ; DW F -> S n |-F- B ; L ; UP []
  | tri_dec3 : forall B L F n,
      theory F -> ~IsPositiveAtom F -> n |-F- B ; L ; DW F -> S n |-F- B ; L ; UP []
  | tri_ex  : forall B FX M t n,
      uniform_oo FX -> proper t -> n |-F- B; M ; DW (FX t) -> S n|-F- B; M ; DW (Some  FX)
  | tri_fx  : forall B L FX M n,
      uniform_oo FX -> (forall x, proper x -> n |-F- B ; L ; UP( (FX x) ::  M)) ->
      S n |-F- B ; L ; UP ((All FX) :: M)                                                                                                                           
  where " n '|-F-' B ';' L ';' X " := (seqN n B L X).
  
  Hint Constructors seqN : core .
  
  (** Well formedness conditions for arrows. *)
  Definition isArrow (A:Arrow) : Prop :=
    match A with
    | UP l => isFormulaL l
    | DW F => isFormula F
    end.
  
  Reserved Notation " '|-f-' B ';' L ';' X " (at level 80).

  (** The same system without the height of the derivation *)
  Inductive seq:  multiset oo -> multiset oo -> Arrow -> Prop :=
  | tri_init1' : forall B A,  |-f- B ; [atom A] ; DW (perp A)
  | tri_init2' : forall B A,  In (atom A) B -> |-f- B ; [] ; DW (perp A)
  | tri_one' : forall B,  |-f- B ; [] ; DW One
  | tri_tensor' : forall B M N MN F G, Permutation MN (M ++ N) ->
                                       (|-f- B ; M ; DW F) ->
                                       (|-f- B ; N ; DW G) ->
                                       |-f- B ; MN ; DW (MAnd F G)
  | tri_plus1' : forall B M F G,
      |-f- B ; M ; DW F -> |-f- B ; M ; DW (AOr F G)
  | tri_plus2' : forall B M F G,
      |-f- B ; M ; DW G -> |-f- B ; M ; DW (AOr F G)
  | tri_bang' : forall B F,
      |-f- B ; [] ; UP [F] -> |-f- B ; [] ; DW (Bang F)
  | tri_rel' : forall B F L, release F -> |-f- B ; L ; UP [F] ->  |-f- B ; L ; DW F
  | tri_top' : forall B L M,
      |-f- B ; L ; UP (Top :: M)
  | tri_bot' : forall B L M,
      |-f- B ; L ; UP M ->  |-f- B ; L ; UP (Bot :: M)
  | tri_par' : forall B L M F G,
      |-f- B ; L ; UP (F::G::M) -> |-f- B ; L ; UP((MOr F G) :: M)
  | tri_with' : forall B L M F G,
      |-f- B ; L ; UP (F :: M) -> |-f- B ; L ; UP (G :: M) -> |-f- B ; L ; UP ((AAnd F  G) :: M)
  | tri_quest' : forall B L M F,
      |-f- B ++ [F] ; L ; UP M -> |-f- B ; L ; UP ((Quest F) :: M)
  | tri_store' : forall B L M F,
      ~ asynchronous  F-> |-f- B ; L ++ [F] ; UP M -> |-f- B ; L ; UP (F::M)
  | tri_dec1' : forall B L L' F,
      ~IsPositiveAtom F -> remove F L L' -> |-f- B ; L' ; DW F -> |-f- B ; L ; UP []
  | tri_dec2' : forall B L F,
      ~IsPositiveAtom F -> In F B -> |-f- B ; L ; DW F -> |-f- B ; L ; UP []
  | tri_dec3' : forall B L F,
      theory F -> ~IsPositiveAtom F -> |-f- B ; L ; DW F -> |-f- B ; L ; UP []
  | tri_ex'  : forall B FX M t,
      uniform_oo FX -> proper t -> |-f- B; M ; DW (FX t) -> |-f- B; M ; DW (Some  FX)
  | tri_fx'  : forall B L FX M,
      uniform_oo FX -> (forall x, proper x -> |-f- B ; L ; UP( (FX x) ::  M)) ->
      |-f- B ; L ; UP ((All FX) :: M)
  where " '|-f-' B ';' L ';' X " := (seq B L X).

  
  Hint Constructors seq : core.
  Definition adeq_seq (B: multiset oo) (L:multiset oo) (X:Arrow) : Prop :=
    isFormulaL B /\ isFormulaL L /\ isArrow X  . (* /\ |-f- B ; L ; X. *)

End LLSequent .

Module LLNotations .
  Notation "'bot'" := Bot.
  Notation "'top'" := Top.
  Notation "'one'" := One.
  Notation "'zero'" := Zero.
  Notation "A ** B" := (MAnd A B ) (at level 50) .
  Notation "A $ B" := (MOr A B) (at level 50) .
  Notation "A 'op' B" := (AOr A B) (at level 50) . 
  Notation "A & B" := (AAnd A B) (at level 50) .
  Notation "! A" := (Bang A) (at level 50) .
  Notation "? A" := (Quest A) (at level 50) .
  Notation " A ^ " := (dual A) (at level 10) .
  Notation " A -o B" := ( (A ^) $ (B) ) (at level 60).
  Notation "'F{' FX '}'" := (All FX) (at level 10) .
  Notation "'E{' FX '}'" := (Some FX) (at level 10) .
  Notation "F == G" := ( ( F -o G ) & ( G -o F )) (at level 60) .

  (** Notation for arrows *)
  (**  Positive phase *)
  Notation ">> F" := (DW F) (at level 80)  .
  (** Negative phase *)
  Notation "> L" := (UP L) (at level 80) .
End LLNotations .
