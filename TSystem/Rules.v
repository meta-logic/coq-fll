(**  ** Rules of the system
     
This file defines the rules of transition system specified in:
        
Joëlle Despeyroux, Amy Felty, Pietro Lio and Carlos Olarte: A Logical
Framework for Modelling Breast Cancer Progression

There are 177 rules that modify the state of the cell according to the driven
mutations it posses. 
 *)

Require Export TSystem.Syntax.
Require Export FLL.SL.FLLTactics.
Require Export FLL.Misc.Permutations.


Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


Hint Constructors plusOne : core .
Hint Constructors uniform_atm'  : core.
Hint Constructors IsTerm : core .

(** Rules changing the state of the system: 
1. Advancing the time in Dt units
2. Modifying the three parameters of the cell: location, fitness and list of mutations.
*)
  Definition EncodeRule (Dt loc fit listMut loc' fit' listMut': nat) (t n :uexp) : oo :=
    ( (perp  T{ t} ) ** perp C{n ; loc ; fit ; listMut}) ** ( (atom T{ t s+ (CN Dt)} $ (atom C{n ;loc' ; fit' ; listMut'}) )) .

  (** Rules for apoptosis *)
  Definition EncodeRuleAP (Dt loc fit listMut : nat) (t n : uexp): oo :=
    ( (perp  T{ t} ) ** perp C{n ; loc ; fit ; listMut }) ** ( (atom T{ t s+ (CN Dt)}) $ (atom A{ n })).

Hint Unfold EncodeRule : core  .
Hint Unfold EncodeRuleAP : core .

(* ================================================ *)
(** Definition of the rules *)
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

(** This tactic applies the rule R on the current goal. The splitting
of the context is made automatically due to the particular
representation of the state of the system we have here.  *)
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
