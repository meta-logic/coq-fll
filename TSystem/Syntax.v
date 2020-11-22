(**  

 *)

Require Export FLL.Misc.Hybrid.
Require Export FLL.SL.FLLTactics.
Require Export FLL.Misc.Permutations.
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

(** Time delays for rules *)

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



Inductive Econ : Set :=
| cn :  nat -> Econ (* Constant of type nat *)
| pl : Econ (* plus *)
| tup4 : Econ (* tuples of 4 elements *)
.

Definition uexp := expr Econ.

Inductive Atom:Set :=
| T : uexp -> Atom (* Time unit *)
| C : uexp -> Atom (* cell representation *)
| A : uexp -> Atom (* Apoptosis *)
.
  

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

  

  Inductive IsTerm : uexp -> Prop :=
  | isTerm1 : forall n, IsTerm (CN n)
  | isTerm2 : forall A B, IsTerm A -> IsTerm B -> IsTerm (PL A B)
  .
  Hint Constructors IsTerm : core .
  
  Definition EncodeRule (Dt loc fit listMut loc' fit' listMut': nat) (t n :uexp) : oo :=
    ( (perp  T{ t} ) ** perp C{n ; loc ; fit ; listMut}) ** ( (atom T{ t s+ (CN Dt)} $ (atom C{n ;loc' ; fit' ; listMut'}) )) .

  (** Rules for apoptosis *)
  Definition EncodeRuleAP (Dt loc fit listMut : nat) (t n : uexp): oo :=
    ( (perp  T{ t} ) ** perp C{n ; loc ; fit ; listMut }) ** ( (atom T{ t s+ (CN Dt)}) $ (atom A{ n })).

Hint Unfold EncodeRule : core  .
Hint Unfold EncodeRuleAP : core .

(* ================================================ *)
(* Definition of Rules *)
(* ================================================ *)
(**  In the breast: *)
Definition br0             := EncodeRule d00 breast 1 NONE breast 0 NONE .
Definition br1 (f:nat)     := EncodeRuleAP (d01 f) breast f NONE .
Definition br2             := EncodeRule d02 breast 1 NONE breast 1 TG .
Definition brt0            := EncodeRule d10 breast 1 TG breast 0 TG .
Definition brt0r            := EncodeRule d10r breast 1 TG breast 2 TG .
Definition brt1 (f:nat)    := EncodeRuleAP (d11 f) breast f TG .
Definition brt2 (f:nat)    := EncodeRule d12 breast f TG breast (f+1) EP .
Definition bre0 (f:nat)    := EncodeRule (d20 f) breast f EP breast (f-1) EP .
Definition bre0r (f:nat)    := EncodeRule (d20r f) breast f EP breast (f+1) EP .
Definition bre1 (f:nat)    := EncodeRuleAP (d21 f) breast f EP .
Definition bre2 (f:nat)    := EncodeRule (d22 f) breast f EP blood (f+1) EP . 

(** In the blood: *)
Definition ble0 (f:nat)    := EncodeRule (d30 f) blood f EP blood (f-1) EP .
Definition ble0r (f:nat)   := EncodeRule (d30r f) blood f EP blood (f+1) EP .
Definition ble1 (f:nat)    := EncodeRuleAP (d31 f) blood f EP .
Definition ble2 (f:nat)    := EncodeRule (d32 f) blood f EP blood (f+2) EPCD .
Definition blec0 (f:nat)   := EncodeRule (d40 f) blood f EPCD blood (f-1) EPCD .
Definition blec1 (f:nat)   := EncodeRuleAP (d41 f) blood f EPCD .
Definition blec2 (f:nat)   := EncodeRule (d42 f) blood f EPCD blood (f+2) EPCDCD .
Definition blec3 (f:nat)   := EncodeRule (d43 f) blood f EPCD blood (f+2) EPCDME .
Definition blecc0 (f:nat)  := EncodeRule (d50 f) blood f EPCDCD blood (f-1) EPCDCD .
Definition blecc1 (f:nat)  := EncodeRuleAP (d51 f) blood f EPCDCD .
Definition blecc2 (f:nat)  := EncodeRule (d52 f) blood f EPCDCD blood (f+2) EPCDCDME .
Definition blecm0 (f:nat)  := EncodeRule (d60 f) blood f EPCDME blood (f-1) EPCDME .
Definition blecm1 (f:nat)  := EncodeRuleAP (d61 f) blood f EPCDME .
Definition blecm2 (f:nat)  := EncodeRule (d62 f) blood f EPCDME blood (f+2) EPCDCDME .
Definition bleccm0 (f:nat) := EncodeRule (d70 f) blood f EPCDCDME blood (f-1) EPCDCDME .
Definition bleccm1 (f:nat) := EncodeRuleAP (d71 f) blood f EPCDCDME .
Definition bleccm2 (f:nat) := EncodeRule (d72 f) blood f EPCDCDME bone (f+1) EPCDCDME .

(** In the bone: *)
Definition bo0 (f:nat)     := EncodeRule (d80 f) bone f EPCDCDME bone (f-1) EPCDCDME .
Definition bo1 (f:nat)     := EncodeRuleAP (d81 f) bone f EPCDCDME .
Definition bo2 (f:nat)     := EncodeRule (d82 f) bone f EPCDCDME bone (f+1) EPCDCDMEse .
  
(** Theory containing the whole set of rules *)

Definition GenRs (R : nat -> uexp -> uexp -> oo) (l: list nat) := map R l.


Definition Theory := [br0] ++ (GenRs br1 [0;1]) ++ [br2 ; brt0 ; brt0r] ++
                           (GenRs brt1 [0;1;2]) ++ (GenRs brt2 [1;2]) ++
                           (GenRs bre0 [1;2;3]) ++ (GenRs bre0r [1;2]) ++
                           (GenRs bre1 [0;1;2;3]) ++ (GenRs bre2 [1;2;3]) ++
                           (* blood *)
                           (GenRs ble0 [1;2;3;4]) ++ (GenRs ble0r [1;2;3]) ++
                           (GenRs ble1 [0;1;2;3;4]) ++
                           (GenRs ble2 [1;2;3;4]) ++ (GenRs blec0 [1;2;3;4;5;6]) ++
                           (GenRs blec1 [0;1;2;3;4;5;6]) ++ (GenRs blec2 [1;2;3;4;5;6]) ++
                           (GenRs blec3 [1;2;3;4;5;6]) ++ (GenRs blecc0 [1;2;3;4;5;6]) ++
                           (GenRs blecc1 [0;1;2;3;4;5;6;7;8]) ++ 
                           (GenRs blecc2 [1;2;3;4;5;6;7;8])  ++
                           (GenRs blecm0 [1;2;3;4;5;6;7;8]) ++ 
                           (GenRs blecm1 [0;1;2;3;4;5;6;7;8]) ++
                           (GenRs blecm2 [1;2;3;4;5;6;7;8]) ++ 
                           (GenRs bleccm0 [1;2;3;4;5;6;7;8;9;10]) ++
                           (GenRs bleccm1 [0;1;2;3;4;5;6;7;8;9;10]) ++ 
                           (GenRs bleccm2 [1;2;3;4;5;6;7;8;9;10]) ++
                           (* Bone *)
                           (GenRs bo0 [1;2;3;4;5;6;7;8;9;10;11]) ++ 
                           (GenRs bo1 [0;1;2;3;4;5;6;7;8;9;10;11]) ++
                           (GenRs bo2 [1;2;3;4;5;6;7;8;9;10;11]).

Inductive OLTheory : oo -> Prop :=
| oltheory : forall F t n, In F Theory -> IsTerm t -> IsTerm n ->  OLTheory (F t n)
.


Notation " n '|---' B ';' L ';' X " := (seqN OLTheory n B L X) (at level 80).
Notation " '|--' B ';' L ';' X " := (seq OLTheory  B L X) (at level 80).

(** Solves goals of the form [In F Theory] *)
Ltac SolveInTheory :=
  try
    match goal with
    | [|- OLTheory _] => constructor;auto; unfold Theory;
                         simpl;
                         repeat match goal with
                                | [|- ?F = ?F \/ ?G] => left;auto
                                | _ => right
                                end
    end.

Lemma tensorapp : forall B L1 L2 F G,
    |-- B ; L2 ; ( >> F) -> |-- B ; L1 ; ( >>  G) -> |-- B ; L1 ++ L2 ;  ( >>  F ** G) .
  intros.
  eapply tri_tensor' with (N:= L1) (M:=L2);solveF.
Qed.

Lemma tensorapp' : forall B L1 L2 F G,
    |-- B ; L1 ; ( >> F) -> |-- B ; L2 ; ( >>  G) -> |-- B ; L1 ++ L2 ;  ( >>  F ** G) .
  intros.
  eapply tri_tensor' with (N:= L2) (M:=L1);solveF.
Qed.

  Ltac applyRule R :=
    decide3 R;SolveInTheory;
    SplitContext' 1;
    apply tensorapp; [
      SplitContext' 1; apply tensorapp';solveLL| simpl];solveLL.

  Ltac ApplyRule R :=
    match goal with 
      [|- context[ T{ ?time}  ]  ] =>
      match goal with
        [|- context[ C{ ?n ; _ ; _ ; _ }]] =>
         applyRule (R time n)
         end
         end.

Lemma Property1: forall n t, 
    |-- [] ; [ E{ fun  x  => perp (T{ x}  )} ** (perp C{ CN n;  bone;  8;  EPCDCDME} )  ;  atom T{ CN t} ; atom C{ CN n ;  blood ;  3 ;  EPCD}]   ;  (> []).
Proof with solveF.
  intros.
  ApplyRule (blec2 3).
  ApplyRule (blecc2 5).
  ApplyRule (bleccm2 7).
  (* Proving the goal *)
  decide1 (E{ fun x => perp T{ x}} ** perp C{ CN n; bone; 8; EPCDCDME}).
  SplitContext' 1.
  apply tensorapp'...
  existential ( ((CN t s+ CN (d42 3)) s+ CN (d52 5)) s+ CN (d72 7)).
Qed.



Lemma Property2: forall n t,
    |-- [] ; [E{ fun  x  => perp (T{ x}  )} **  ( (perp C{ CN n ; bone ; 6 ; EPCDCDME}) 
                                                 op (perp C{CN n ; bone ; 7 ; EPCDCDME}) op (perp C{CN n ; bone ; 8 ; EPCDCDME} ) 
                                                 op (perp C{CN n ; bone ; 9 ; EPCDCDME}) )] ; 
 ( > [atom T{ CN t}  ; atom  C{ CN n ; blood ; 3 ; EPCD}  & atom C{ CN n ; blood ; 4 ; EPCD} ]) .
Proof with solveF.
  intros.
  solveLL.
  + (* first subgoal *)
    ApplyRule (blec0 3).
    ApplyRule (blec2 2).
    ApplyRule (blecc0 4).
    ApplyRule (blecc2 3).
    ApplyRule (bleccm2 5).
    (* Focusing on goal *)
    decide1 (E{ fun x => perp T{ x}} **
              (((perp C{ CN n; bone; 6; EPCDCDME} op perp C{ CN n; bone; 7; EPCDCDME})
                  op perp C{ CN n; bone; 8; EPCDCDME}) op perp C{ CN n; bone; 9; EPCDCDME})).
    SplitContext' 1.
    apply tensorapp'...
    existential  (((((CN t s+ CN (d40 3)) s+ CN (d42 2)) s+ CN (d50 4)) s+ CN (d52 3)) s+ CN (d72 5)).
  + (* second goal *)
    ApplyRule (blec0 4) .
    ApplyRule (blec2 3) .
    ApplyRule (blecc0 5) .
    ApplyRule (blecc2 4) .
    ApplyRule (bleccm2 6) .
    (* now focusing on the goal *)
    decide1 (E{ fun x => perp T{ x}} **
              (((perp C{ CN n; bone; 6; EPCDCDME} op perp C{ CN n; bone; 7; EPCDCDME})
                  op perp C{ CN n; bone; 8; EPCDCDME}) op perp C{ CN n; bone; 9; EPCDCDME})).
    SplitContext' 1.
    apply tensorapp'...
    existential ( ((((CN t s+ CN (d40 4)) s+ CN (d42 3)) s+ CN (d50 5)) s+ CN (d52 4)) s+ CN (d72 6)).
Qed.


(** ** Property 3 *)
(** A cell in the breast, with mutation [ EP ], might have his fitness oscillating from [ 1 ] to [ 2 ] and back ? *)
Lemma Property3_Seq1: forall n t,
    exists d,
 |-- [] ; [ E{ fun x => perp T{ x s+ d}} ** (perp C{ CN n; breast; 2; EP})   ; 
              atom T{ CN t} ; atom C{ CN n ; breast ; 1 ; EP}]   ; (> []).
Proof with solveF .
  intros.
  exists (CN (d20r 1)).
  ApplyRule (bre0r 1).
  (* Proving the goal *)
  decide1 (E{ fun x => perp T{ x s+ CN (d20r 1)}} ** perp C{ CN n; breast; 2; EP}).
  SplitContext' 1.
  apply tensorapp'...
  existential (CN t).
Qed.

Lemma Property3_Seq2: forall n t,
    exists d,
 |-- [] ; [ E{ fun x => perp T{ x s+ d}} ** (perp C{ CN n; breast; 1; EP})   ; 
              atom T{ CN t} ; atom C{ CN n ; breast ; 2 ; EP}]   ; (> []).
Proof with solveF .
  intros.
  exists (CN (d20 2)).
  ApplyRule (bre0 2).
  (* Proving the goal *)
  decide1 (E{ fun x  => perp T{ x s+ CN (d20 2)}} ** perp C{ CN n; breast; 1; EP}).
  SplitContext' 1.
  apply tensorapp'...
  existential (CN t).
Qed.
  
