(**  ** Syntax

The syntactic elements (type [Econ]) includes: 
- [cn]: Denoting a constant of type [nat]
- [pl]: Denoting addition of numerical constants. 
- [tup4]: Denoting tuples of 4 elements

The signature also includes the following atomic predicates:

- [T(t)]: denoting the current time-unit 
  
- [C(n,c,f,lm)]: denoting a cell n, in a compartment c (breast, blood, or
  bone), with a phenotype given by a fitness degree (a number in the interval 0
.. 12) and a list of driver mutations lm.
  
 - [A(n)]: representing the fact that the cell n has gone to apoptosis.

This file defines some numerical constants used in the model. For instance,
there are three possible locations: [breast], [blood] and [bone] denotes,
respectively as the constants 1,2,3.

 *)

Require Export FLL.Misc.Hybrid.
Require Export FLL.SL.FLLTactics.
Require Export FLL.Misc.Permutations.
Require Import Coq.Init.Nat.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


(** ** Numerical constants *)
(** Mutations *)
Definition TGFbeta := 1 .
Definition EPCAM   := 2 .
Definition CD47    := 3 .
Definition CD44    := 4 .
Definition MET     := 5 .
Definition seeded  := 6.

(** Locations *)
Definition breast  := 1.
Definition blood   := 2.
Definition bone    := 3.

(** Binary encoding of (some) lists of Mutations *)
Definition NONE       := 0 .
Definition TG         := 32 .
Definition EP         := 16 .
Definition EPCD       := 24 .
Definition EPCDME     := 26 .
Definition EPCDCD     := 28 .
Definition EPCDCDME   := 30 .
Definition EPCDCDMEse := 31 .

(** [plusOne] defines how to "add" a new mutation to a list of mutations *)
Inductive plusOne : nat ->nat -> Prop :=
| po_nt : plusOne NONE TG
| po_ne  :plusOne TG EP
| po_ep1 : plusOne EP EPCD
| po_epcd1 : plusOne EPCD EPCDME
| po_epcd2 : plusOne EPCD EPCDCD
| po_epcdme1 : plusOne EPCDCD EPCDCDME
| po_epcdme2 : plusOne EPCDME EPCDCDME
| po_epmese : plusOne EPCDCDME EPCDCDMEse.

Hint Constructors plusOne : core .

(** Numerical constants defining how the time pass in each cell's
* transformation *)

Definition d00 := 1 .
Definition d01 (f:nat) := 1 . 
Definition d02 := 3 .
Definition d10 := 1 .
Definition d10r := 1 .
Definition d11 (f:nat) := 1 . 
Definition d12 := 3 .
Definition d20 (f:nat) := 1 .
Definition d20r (f:nat) := f .
Definition d21 (f:nat) := f . 
Definition d22 (f:nat) := 1 . 
Definition d30 (f:nat) := 1 .
Definition d30r (f:nat) := f .
Definition d31 (f:nat) := f . 
Definition d32 (f:nat) := f . 
Definition d40 (f:nat) := f . 
Definition d41 (f:nat) := f .
Definition d42 (f:nat) := f . 
Definition d43 (f:nat) := f . 
Definition d50 (f:nat) := f .
Definition d51 (f:nat) := match f with
                          | 1 | 2 => f
                          | 3 | 4 => f -1 
                          | _ => f -2
                          end.
Definition d52 (f:nat) := 3 .
Definition d60 (f:nat) := 1 .
Definition d61 (f:nat) := match f with
                          | 1 | 2 => f
                          | 3 | 4 => f -1
                          | _ => f -2
                          end.
Definition d62 (f:nat) := 3 .
Definition d70 (f:nat) := 1 .

Definition d71 (f:nat) := match f with
                          | 1 | 2 => f
                          | 3 | 4 => f -1
                          | 5 | 6 => f -2
                          | _ => f -3
                          end.

Definition d72 (f:nat) := 2 . 
Definition d80 (f:nat) := 1 .

Definition d81 (f:nat) := match f with
                          | 1  => f
                          | 2 | 3 => 2
                          | 4 | 5 => 3
                          | 6 | 7 => 4
                          | _ => 5
                          end.

Definition d82 (f:nat) := 2 .


(** Syntactic elements *)
Inductive Econ : Set :=
| cn :  nat -> Econ (* Constant of type nat *)
| pl : Econ (* plus *)
| tup4 : Econ (* tuples of 4 elements *)
.

Definition uexp := expr Econ.

(** The three needed atomic predicates *)
Inductive Atom:Set :=
| T : uexp -> Atom (* Time unit *)
| C : uexp -> Atom (* cell representation *)
| A : uexp -> Atom (* Apoptosis *)
.
  
(** Uniform conditions on atomic propositions *)
Inductive uniform_atm' : (uexp -> Atom) -> Prop :=
| uniform_t: forall FX, uniform FX -> uniform_atm' (fun x:uexp => T (FX x))
| uniform_c: forall FX, uniform FX -> uniform_atm' (fun x:uexp => C (FX x))
| uniform_a: forall FX, uniform FX -> uniform_atm' (fun x:uexp => A (FX x))
  .

  (** More suitable constructors to work with *)
  Definition CN n   := (CON (cn n)) .
  Definition PL T1 T2 := (APP (APP (CON pl) T1) T2).
  Definition TUP T1 T2 T3 T4 := (APP (APP (APP (APP (CON pl) T1) T2) T3) T4).

  Notation "d 's+' t" := (PL d t) (at level 80, right associativity).
  Notation "A{ n }"   := (A n) . (* nat constants *)
  Notation "C{ n ; c ; f ; lm }" := (C (TUP n (CN c) (CN f) (CN lm))) . (* nat constants *)
  Notation "T{ n }"   := (T n) .
  
  Hint Constructors uniform_atm'  : core.


  (** Instantiating the LL signature *)
  Global Instance Signature : OLSig :=
    {| 
      con := Econ;
      atm := Atom;
      uniform_atm := uniform_atm'
    |}.


  Definition T' : uexp -> atm := T.
  Definition C' : uexp -> atm := C.
  Definition A' : uexp -> atm := A.

  Notation "A'{ n }"   := (A' n) . (* nat constants *)
  Notation "C'{ n ; c ; f ; lm }" := (C' (TUP n (CN c) (CN f) (CN lm))) . (* nat constants *)
  Notation "T'{ n }"   := (T' n) .

  (** Well formed condition for terms *)

  Inductive IsTerm : uexp -> Prop :=
  | isTerm1 : forall n, IsTerm (CN n)
  | isTerm2 : forall A B, IsTerm A -> IsTerm B -> IsTerm (PL A B)
  .
  Hint Constructors IsTerm : core .
  
  
