(** * Tactics for the focused system

In order to use FLL, this module must be imported. It defines useful
tactics for forward and backward (inversion) reasoning. Some useful
notations are also introduced.

As a general rule, tactics for the system without measures are names
with an apostrophe. For instance, [solveLL] for the system [seqN] and
[solveLL'] for the system [seq].
 *)
Require Export FLL.Misc.Utils.
Require Export FLL.SL.StructuralRules.
Require Import FLL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

(* Section FLL. *)

(** Solves some efficiency problems related to rewriting with setoids *)
Remove Hints Equivalence.pointwise_equivalence : typeclass_instances.
Existing Instance Equivalence.pointwise_equivalence | 11.

Hint Constructors isFormula Remove seqN IsPositiveAtom : core .

(** This tactic solves most of the irrelevant goals in a focused
  proof (e.g., proving whether a formula is positive or not) *)
Ltac solveF :=
  simpl;auto;subst;
  let H := fresh "H" in
  repeat
    match goal with
    | [ |- _ <= _ ] => lia
    | [ |- _ >= _ ] => lia
    | [ |- _ < _ ] => lia
    | [ |- _ > _ ] => lia
    | [ |- In ?F (?F :: _)] => constructor;auto
    | [H : False |- _] => contradiction
    | [H : ?F , H' : ~ ?F |- _ ] => contradiction
    | [H : _ /\ _ |- _] => destruct H;solveF
                                        
    | [|-~ asynchronous _] => intro H; inversion H;auto
    | [|-~ IsPositiveAtom _ ] => intro H; inversion H;auto
    | [|- IsPositiveAtom _ ] => repeat constructor
    | [|- release _] => constructor
    | [|- Remove _ _ _] => constructor
    | [H: Permutation [?F] _ |- _] => apply Permutation_unq in H;subst
    | [H: In _ [] |- _ ] => inversion H
    | [|- asynchronous _] => constructor
    | [H: Remove _ [?F] ?L |- _] =>  apply RemoveUnique in H;subst
    | [H: release ?F  |- _] =>
      let H' := fresh "H" in
      match F with
      | MAnd _ _ => contradict H;intro H';inversion H'
      | perp _ => contradict H;intro H';inversion H'
      | Some _ => contradict H;intro H';inversion H'
      | zero => contradict H;intro H';inversion H'
      | AOr _ _ => contradict H;intro H';inversion H'
      | Bang _ => inversion H
      | top => clear H
      end
    | [H : ~ asynchronous ?F |- _ ] =>
      match F with
      | AAnd _ _ => contradict H;constructor
      | MOr _ _ => contradict H;constructor
      | All _ => contradict H;constructor
      | Quest _ => contradict H;constructor
      | Bot => contradict H;constructor
      | Top => contradict H;constructor
      end
    | [H : ~ IsPositiveAtom ( atom _ ) |- _ ] => contradict H;constructor
    | [H : In _ [_] |- _ ] => inversion H;clear H
    | [H : In _ [] |- _ ] => inversion H
    | [H : _ :: _ = [] |- _] => inversion H
    | [H : [] = _ :: _ |- _] => inversion H
    | [H : [ ?a ] = [ ?b ] |- _ ] => inversion H; clear H ; subst ; solveF
    | [H: (atom _ ) = (atom _ ) |- _ ] => inversion H;clear H
    | [H : In ?F _ \/ In ?F [] |- _] =>  destruct H;solveF
    | [H : In ?F [] \/ In ?F _ |- _] =>  destruct H;solveF
    | [|- context[nil ++ _]] => rewrite app_nil_l
    | [H: context[nil ++ _] |- _] => rewrite app_nil_l in H
    | [|- context[sub _ 0]] => rewrite Nat.sub_0_r
    | [H: context[sub _ 0] |- _] => rewrite Nat.sub_0_r in H
    | [ |- _ >= _] => subst; omega
    | [ |- _ <= _] => subst; omega
    end;auto;
  try(match goal with
      | [ |- Permutation _ _] =>  perm
      end).

(** This tactic acts on the linear context by moving the n-th
  element to the front of the list *)
Ltac ExchangeFront n :=
  let H:= fresh "H" in
  match goal with
    [|- seqN _ _ _ ?L _ ] =>
    let T := constr:(FrontApp n L) in
    let A := constr:(fst (fst T)) in
    let B := constr:(snd (fst T)) in
    let C := constr:(snd T) in
    let A' := eval simpl  in A in
        let B' := eval simpl  in B in
            let C' := eval simpl  in C in
                assert(H : Permutation  (A' ++ B' ++ C' ) (B' ++ A' ++ C') ) by auto using Permutation_midle, Permutation_midle_app ; simpl in H;
                                     apply exchangeLCN with (LC :=  (A' ++ B' ++ C'));auto;simpl;
                                     clear H
  end.
Ltac ExchangeFront' n :=
  let H:= fresh "H" in
  match goal with
    [|- seq _ _ ?L _ ] =>
    let T := constr:(FrontApp n L) in
    let A := constr:(fst (fst T)) in
    let B := constr:(snd (fst T)) in
    let C := constr:(snd T) in
    let A' := eval simpl  in A in
        let B' := eval simpl  in B in
            let C' := eval simpl  in C in
                assert(H : Permutation  (A' ++ B' ++ C' ) (B' ++ A' ++ C') ) by auto using Permutation_midle, Permutation_midle_app ; simpl in H;
                                     apply exchangeLC with (LC :=  (A' ++ B' ++ C'));auto;simpl;
                                     clear H
  end.

(** Moving the last element of the context to the first position *)
Ltac ExchangeLast :=
  match goal with
    [|- seqN _ _ _ ?L _ ] =>
    let l := constr:(length L) in
    let l' :=  eval simpl  in l in
        ExchangeFront l'
  end.

Ltac ExchangeLast' :=
  match goal with
    [|- seq _ _ ?L _ ] =>
    let l := constr:(length L) in
    let l' :=  eval simpl  in l in
        ExchangeFront' l'
  end.


Ltac ExchangeApp :=
  match goal with
    [|- seqN _ _ _ (?A ++ ?B) _ ] =>
    apply exchangeLCN with (LC := B ++ A); [apply Permutation_app_comm |idtac]
  end.
Ltac ExchangeApp' :=
  match goal with
    [|- seq _ _ (?A ++ ?B) _ ] =>
    apply exchangeLC with (LC := B ++ A); [apply Permutation_app_comm |idtac]
  end.

(** Finishes the proof if H is a sequent that only needs some exchanges to be
equal to the goal *) 
Ltac LLExact H :=
  let G:= type of H in
  match G with
  | (seqN ?T _ ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- seqN T _ ?Gamma' ?Delta' X ] =>
      apply exchangeCCN with (CC:= Gamma);auto; try perm;
      apply exchangeLCN with (LC:= Delta);auto;try perm
    end 
  end;auto.


Ltac LLExact' H :=
  let G:= type of H in
  match G with
  | (seq ?T ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- seq T ?Gamma' ?Delta' X ] =>
      apply exchangeCC with (CC:= Gamma);auto; try perm;
      apply exchangeLC with (LC:= Delta);auto;try perm
    end
  end;auto.

(** Splits the linear context L into L1 ++ L2 where L1 contains the first n elements of L *)
Ltac SplitContext n :=
  match goal with
  | [ |- seqN _ _ _ ?L _ ] =>
    let H := fresh "H" in
    let L1 := constr:(firstn n L) in
    let L2 := constr:(skipn n L) in
    let L1' := eval simpl in L1 in
        let L2' := eval simpl in L2 in
            let L3 := constr:(L1' ++ L2') in
            (assert(H : Permutation L L3) by auto using Permutation_midle, Permutation_midle_app);rewrite H;clear H 
  end.

Ltac SplitContext' n :=
  match goal with
  | [ |- seq _ _ ?L _ ] =>
    let H := fresh "H" in
    let L1 := constr:(firstn n L) in
    let L2 := constr:(skipn n L) in
    let L1' := eval simpl in L1 in
        let L2' := eval simpl in L2 in
            let L3 := constr:(L1' ++ L2') in
            (assert(H : Permutation L L3) by auto using Permutation_midle, Permutation_midle_app);rewrite H;clear H 
  end.

Ltac solveUniform :=
  auto;
  repeat 
    match goal with
    | [|- uniform_oo _] =>  constructor 
    | [|- uniform _ ] => eauto using uniform_id, uniform_con, uniform_app
    | [|- uniform_atm _ ] => constructor
    | [|- proper _ ] => constructor
    | [|- level _ _ ] => constructor
    end.


Tactic Notation "store" := apply tri_store ;solveF.
Tactic Notation "store'" := apply tri_store' ;solveF.
Tactic Notation "par" := apply tri_par.
Tactic Notation "par'" := apply tri_par'.
Tactic Notation "release'" := apply tri_rel' ; solveF.
Tactic Notation "release" := apply tri_rel ; solveF.
Tactic Notation "init" := first [apply tri_init1;auto | apply tri_init2;auto].
Tactic Notation "init'" := first [apply tri_init1' | apply tri_init2'].

(** This tactic applies as many positive/negative rules as
  possible. Connectives as exists and tensor are not automatically
  introduced (due to the decision on the contexts/terms ) *)
Ltac solveLL :=
  try
    match goal with
    (* initial Rules *)
    | [|- seqN _ _ _ _ (>> (perp _))] => init
    | [|- seqN _ _ _ [] (>>  One)] => apply tri_one
    | [|- seqN _ _ _ [perp ?A] (>> (atom ?A))] => apply InitPosNegDwN
    | [|- seqN _ _ _ [atom ?A ; perp ?A] (> [])] => apply InitPosNegN
    | [|- seqN _ _ _ [perp ?A; atom ?A ] (> [])] => rewrite Permutation_cons_append with (x:= (perp A)); apply InitPosNegN
    (* Change of polarity *)
    | [|- seqN _ _ _ _ (>>  ?F)] =>
      match F with
      | MOr _ _ => release;solveLL
      | All _ =>release;solveLL
      | Bot  => release;solveLL
      | (atom _)  => release;solveLL
      | Top  => release;solveLL
      | AAnd _ _  => release;solveLL
      | Quest _  => release;solveLL
      | Bang _  => apply tri_bang;solveLL
      end
    (* Negative Phase *)
    | [ |- seqN _ _ _ _ (> ((One ) :: _ ))] => store ;solveLL
    | [ |- seqN _ _ _ _ (> ((Zero ) :: _ ))] => store ;solveLL
    | [ |- seqN _ _ _ _ (> ((atom _ ) :: _ ))] => store ;solveLL
    | [ |- seqN _ _ _ _ (> ((perp _ ) :: _ ))] => store ;solveLL
    | [ |- seqN _ _ _ _ (> ( (Bang _) :: _)) ] => store ;solveLL
    | [ |- seqN _ _ _ _ (> ( (Quest _) :: _)) ] => apply tri_quest ;solveLL
    | [ |- seqN _ _ _ _ (> ( (Top) :: _))  ] => apply tri_top
    | [ |- seqN _ _ _ _ (> ( (MOr _ _) :: _)) ] => par ;solveLL
    | [ |- seqN _ _ _ _ (> ( (AOr _ _) :: _)) ] => store ;solveLL
    | [ |- seqN _ _ _ _ (> ( (AAnd _ _) :: _)) ] => apply tri_with ;solveLL
    | [ |- seqN _ _ _ _ (> ( (Bot) :: _)) ] => apply tri_bot ;solveLL
    | [ |- seqN _ _ _ _ (> ( (MAnd _ _) :: _)) ] => store ;solveLL
    | [ |- seqN _ _ _ _ (> ( (All _) :: _)) ] => let x:= fresh "x" in
                                                 let xp := fresh "properX" in
                                                 apply tri_fx ;try solveUniform; intros x xp ; solveLL
    | [ |- seqN _ _ _ _ (> ((Some _ ) :: _ ))] => store ;solveLL
    end.

Ltac solveLL' :=
  try
    match goal with
    (* initial Rules *)
    | [|- seq _ _ _ (>> (perp _))] => init'
    | [|- seq _ _ [] (>>  One)] => apply tri_one'
    | [|- seq _ _ [perp ?A] (>> (atom ?A))] => apply InitPosNegDw
    | [|- seq _ _ [atom ?A ; perp ?A] (> [])] => apply InitPosNeg
    | [|- seq _ _ [perp ?A; atom ?A ] (> [])] => rewrite Permutation_cons_append with (x:= (perp A)); apply InitPosNeg
    (* Change of polarity *)
    | [|- seq _ _ _ (>>  ?F)] =>
      match F with
      | MOr _ _ => release';solveLL'
      | All _ =>release';solveLL'
      | Bot  => release';solveLL'
      | (atom _)  => release';solveLL'
      | Top  => release';solveLL'
      | AAnd _ _  => release';solveLL'
      | Quest _  => release';solveLL'
      | Bang _  => apply tri_bang';solveLL'
      end
    (* Negative Phase *)
    | [ |- seq _ _ _ (> ((One) :: _ ))] => store' ;solveLL'
    | [ |- seq _ _ _ (> ((Zero) :: _ ))] => store' ;solveLL'
    | [ |- seq _ _ _ (> ((atom _ ) :: _ ))] => store' ;solveLL'
    | [ |- seq _ _ _ (> ((perp _ ) :: _ ))] => store' ;solveLL'
    | [ |- seq _ _ _ (> ((Bang _ ) :: _ ))] => store' ;solveLL'
    | [ |- seq _ _ _ (> ( (Quest _) :: _)) ] => apply tri_quest' ;solveLL'
    | [ |- seq _ _ _ (> ( (Top) :: _))  ] => apply tri_top'
    | [ |- seq _ _ _ (> ( (MOr _ _) :: _)) ] => par' ;solveLL'
    | [ |- seq _ _ _ (> ( (AOr _ _) :: _)) ] => store' ;solveLL'
    | [ |- seq _ _ _ (> ( (AAnd _ _) :: _)) ] => apply tri_with' ;solveLL'
    | [ |- seq _ _ _ (> ( (Bot) :: _)) ] => apply tri_bot' ;solveLL'
    | [ |- seq _ _ _ (> ( (MAnd _ _) :: _)) ] => store' ;solveLL'
    | [ |- seq _ _ _ (> ( (All _) :: _)) ] => let x:= fresh "x" in
                                              let xp := fresh "properX" in
                                              apply tri_fx' ; try solveUniform ; intros x xp  ;solveLL'
    | [ |- seq _ _ _ (> ((Some _ ) :: _ ))] => store' ;solveLL'
    end.

(** Decision rule on the linear context based on the position of the formula *) 
Ltac dec1' n :=
  ExchangeFront' n;
  match goal with
    [|- seq _ _ (?G :: _) (> []) ] =>
    eapply tri_dec1' with (F:= G);solveF
  end.
(** Decision rule on the linear context based on the position of the formula *) 
Ltac dec1 n :=
  ExchangeFront n;
  match goal with
    [|- seqN _ _ _ (?G :: _) (> []) ] =>
    eapply tri_dec1 with (F:= G);solveF
  end.

(** Notation for forward reasoning on FLL sequents *)
Tactic Notation "decide1"  constr(R) := eapply @tri_dec1 with (F:= R);solveF.
Tactic Notation "decide2"  constr(R) := eapply @tri_dec2 with (F:= R);solveF.
Tactic Notation "decide3"  constr(R) := eapply @tri_dec3 with (F:= R);solveF.
Tactic Notation "tensor"  constr(Ctx1) constr(Ctx2) := eapply @tri_tensor with (M:=Ctx1) (N:=Ctx2);solveF;solveLL.
Tactic Notation "tensor"   := eapply @tri_tensor ;solveF;solveLL.
Tactic Notation "oplus1" := apply tri_plus1;solveLL.
Tactic Notation "oplus2" := apply tri_plus2;solveLL.
Tactic Notation "oplus1'" := apply tri_plus1';solveLL'.
Tactic Notation "oplus2'" := apply tri_plus2';solveLL'.
Tactic Notation "existential" constr(tt) := eapply @tri_ex with (t:=tt);try solveUniform; auto;solveLL.
Tactic Notation "decide1'"  constr(R) := eapply @tri_dec1' with (F:= R);solveF.
Tactic Notation "decide2'"  constr(R) := eapply @tri_dec2' with (F:= R);solveF.
Tactic Notation "decide3'"  constr(R) := eapply @tri_dec3' with (F:= R);solveF.
Tactic Notation "tensor'"  constr(Ctx1) constr(Ctx2) := eapply @tri_tensor' with (M:=Ctx1) (N:=Ctx2);solveF;solveLL'.
Tactic Notation "tensor'"  := eapply @tri_tensor' ;solveF;solveLL'.
Tactic Notation "existential'" constr(tt) := eapply @tri_ex' with (t:=tt);try solveUniform ; auto;solveLL'.


(** First splits the context L into L1 ++ L2 (where L1 contains
      the first n elements of L1) and then, it applied tensor where L2
      goes to the first branch and L1 goes to the second branch *)
Ltac tensorSplitI' n :=
  SplitContext' n;
  rewrite Permutation_app_comm;
  match goal with
  | [ |- seq _ _ (?L1 ++ ?L2) _ ] =>
    tensor' L1 L2;solveLL'
  end.

(** First splits the context L into L1 ++ L2 (where L1 contains
      the first n elements of L1) and then, it applied tensor where L2
      goes to the first branch and L1 goes to the second branch *)
Ltac tensorSplitI n :=
  SplitContext n;
  rewrite Permutation_app_comm;
  match goal with
  | [ |- seqN _ _ _ (?L1 ++ ?L2) _ ] =>
    tensor L1 L2;solveLL
  end.

(** Applying tensor and splitting the context automatically *)
Ltac tensorSplit' n :=
  SplitContext' n;
  match goal with
  | [ |- seq _ _ (?L1 ++ ?L2) _ ] =>
    tensor' L1 L2;solveLL'
  end.


Ltac tensorSplit n :=
  SplitContext n;
  match goal with
  | [ |- seqN _ _ _ (?L1 ++ ?L2) _ ] =>
    tensor L1 L2;solveLL
  end.



(** Given a rule R (belonging to the theory), this rule introduces R
  (using [tri_dec3]) and then tries to decompose such formula using
  [solveLL]. *)
Ltac bipole Rule :=
  match goal with
  | [|- seqN _ _ _ (?A :: ?L) (> [] ) ] =>
    decide3 Rule;
    tensor [A] L; solveLL
  end.
Ltac bipole' Rule :=
  match goal with
  | [|- seq _ _ (?A :: ?L) (> [] ) ] =>
    decide3' Rule;
    tensor' [A] L; solveLL'
  end.

(** This tactic must be used to reason by inversion on hypotheses
  containing FLL sequents. Must of the "irrelevant" cases (as, e.g.,
  assuming that focused can be lost on a positive formula) are
  discarded. *)
Ltac invTriStep H :=
  repeat autounfold in H;
  simpl in H;
  let F := type of H in
  let H' := fresh "H" in
  match F with
  | seqN _ _  _ _ (> []) => inversion H;subst;solveF (* decision rules *)
  | seqN _ _  _ _ (> ((One ):: _)) => inversion H;subst (* Store *)
  | seqN _ _  _ _ (> ((Zero ):: _)) => inversion H;subst (* Store *)
  | seqN _ _  _ _ (> ((Bot ):: _)) => inversion H;[subst | solveF] (* Bot *)
  | seqN _ _  _ _ (> ((atom _ ):: _)) => inversion H;subst (* Store *)
  | seqN _ _  _ _ (> ((perp _ ):: _)) => inversion H;subst (* Store *)
  | seqN _ _  _ _ (> ((AAnd _ _) :: _)) => inversion H;subst;[idtac | solveF ] (* with  *)
  | seqN _ _  _ _ (> ((MOr _ _) :: _)) => inversion H;subst;[idtac | solveF ] (* with /release *)
  | seqN _ _  _ _ (> ((AOr _ _) :: _)) => inversion H;subst (* store *)
  | seqN _ _  _ _ (> ((MAnd _ _) :: _)) => inversion H;subst (* store *)
  | seqN _ _  _ _ (> ((Bang _ ) :: _)) => inversion H;subst (* store *)
  | seqN _ _  _ _ (> ((Quest _):: _) ) => inversion H;subst; [idtac | solveF];simpl in H (* quest *)
  | seqN _ _  _ _ (> ((All _):: _) ) => inversion H;subst; [solveF | idtac] (* forall /release *)
  | seqN _ _  _ _ (> ((Some _):: _) ) => inversion H;subst (* store *)
  | seqN _ _  _ _ (> ((Top):: _) ) => inversion H;subst; [idtac | solveF];simpl in H (* top *)
  | seqN _ _  _ _ (>> (MAnd _ _)) => inversion H;subst;[idtac | solveF] (* tensor --2nd branch contradictory/release*)
  | seqN _ _  _ _ (>> (AOr _ _)) => inversion H;subst;[idtac | idtac | solveF]  (* oplus --2nd branch contradictory *)
  | seqN _ _  _ _ (>> (Bang _)) => inversion H;subst;[idtac | solveF]  (* --2nd branch contradictory *)
  | seqN _ _  _ _ (>>  (perp _)) => apply FocusAtomN in H as H';inversion H';solveF (* [solveF | intro; apply True]*)  (* focus on an atom*)
  | seqN _ _  _ _ (>>  (atom _ )) => inversion H;subst (* release *)
  | seqN _ _  _ _ (>>  (Top)) => inversion H;subst (* top *)
  | seqN _ _  _ _ (>>  (Bot)) => inversion H;subst (* bot *)
  | seqN _ _  _ _ (>>  (Quest _)) => inversion H;subst (* quest *)
  | seqN _ _  _ _ (>>  (MOr _ _)) => inversion H;subst 
  | seqN _ _  _ _ (>>  (AAnd _ _)) => inversion H;subst (* with /release *)
  | seqN _ _  _ _ (>>  (All _) ) => inversion H;subst (* forall /release *)
  | seqN _ _  _ _ (>> (Some _) ) => inversion H;subst; [solveF | idtac] (* exists *)
  | seqN _ _  _ _ (>> (Zero) ) => inversion H;solveF 
  end.

Ltac invTri H := invTriStep H ; clear H.

(** Version without measures *)
Ltac invTri' H :=
  repeat autounfold in H;
  simpl in H;
  let F := type of H in
  let H' := fresh "H" in
  match F with
  | seq _  _ _ (> []) => inversion H;subst;solveF (* decision rules *)
  | seq _  _ _ (> ((One ):: _)) => inversion H;subst (* Store *)
  | seq _  _ _ (> ((Zero ):: _)) => inversion H;subst (* Store *)
  | seq _  _ _ (> ((Bot ):: _)) => inversion H;[subst | solveF] (* Bot *)
  | seq _  _ _ (> ((Top):: _) ) => inversion H;subst; [idtac | solveF];simpl in H (* top *)
  | seq _  _ _ (> ((atom _ ):: _)) => inversion H;subst (* Store *)
  | seq _  _ _ (> ((perp _ ):: _)) => inversion H;subst (* Store *)
  | seq _  _ _ (> ((AAnd _ _) :: _)) => inversion H;subst;[idtac | solveF ] (* with  *)
  | seq _  _ _ (> ((MOr _ _) :: _)) => inversion H;subst;[idtac | solveF ] (* with /release *)
  | seq _  _ _ (> ((AOr _ _) :: _)) => inversion H;subst (* store *)
  | seq _  _ _ (> ((MAnd _ _) :: _)) => inversion H;subst (* store *)
  | seq _  _ _ (> ((Bang _) :: _)) => inversion H;subst (* store *)
  | seq _  _ _ (> ((Quest _):: _) ) => inversion H;subst; [idtac | solveF];simpl in H (* quest *)
  | seq _  _ _ (> ((All _):: _) ) => inversion H;subst; [solveF | idtac] (* forall /release *)
  | seq _  _ _ (> ((Some _):: _) ) => inversion H;subst (* store *)
  | seq _  _ _ (>> (MAnd _ _)) => inversion H;subst;[idtac | solveF] (* tensor --2nd branch contradictory/release*)
  | seq _  _ _ (>> (AOr _ _)) => inversion H;subst;[idtac | idtac |  solveF] (* oplus --2nd branch contradictory/release*)
  | seq _  _ _ (>> (Bang _)) => inversion H;subst;[idtac | solveF] (* 2nd branch contradictory/release*)
  | seq _  _ _ (>>  (perp _)) => apply FocusAtom in H as H'; inversion H'; solveF (* [solveF | intro; apply True]*)  (* focus on an atom*)
  | seq _  _ _ (>>  (atom _ )) => inversion H;subst (* release *)
  | seq _  _ _ (>>  (Top)) => inversion H;subst (* top *)
  | seq _  _ _ (>>  (Bot)) => inversion H;subst (* bot *)
  | seq _  _ _ (>>  (Quest _)) => inversion H;subst (* quest *)
  | seq _  _ _ (>>  (MOr _ _)) => inversion H;subst 
  | seq _  _ _ (>>  (AAnd _ _)) => inversion H;subst (* with /release *)
  | seq _  _ _ (>>  (All _) ) => inversion H;subst (* forall /release *)
  | seq _  _ _ (>> (Some _) ) => inversion H;subst; [solveF | idtac] (* exists *)
  | seq _  _ _ (>> (Zero ) ) => inversion H;solveF
  end;
  clear H.

(* Applies, possibly several times, inversion (invTri) on the 
    hypothesis containing focused sequents. It stops when the negative 
    phase ends ([Gamma ; Delta ; > []])
 *)
Ltac InvTriAll :=
  repeat
    match goal with
    | [H : seqN _ _ _ _ (>> _) |- _ ] => invTri H
    | [H : seqN _ _ _ _ (> (?C :: _)) |- _ ] => invTri H
    end.

Ltac InvTriAll' :=
  repeat
    match goal with
    | [H : seq _ _ _ (>> _) |- _ ] => invTri' H
    | [H : seq _ _ _ (> (?C :: _)) |- _ ] => invTri' H
    end.


(* Hypothesis with a higher proof than the one needed *)
Ltac HProof :=
  match goal with
  | [ H : seqN _ ?n ?G ?M ?X |- seqN _ ?m ?G ?M ?X ] =>
    eapply HeightGeq;[eauto | omega]
  end.
Ltac HProof' :=
  match goal with
  | [ H : seqN _ ?n ?G ?M ?X |-  seq _ ?G ?M ?X ] =>
    eapply seqNtoSeq;eauto
  end.

Ltac invseqN :=
  repeat
    match goal with
    | [ H : seqN EmptyTheory _ _ _ (> (_ :: _)) |- _ ] => invTri H
    end.
Ltac invseq :=
  repeat
    match goal with
    | [ H : seq EmptyTheory _ _ (> (_ :: _)) |- _ ] => invTri' H
    end.
(** Erasing some of the (unimportant) hypotheses added by the [solveF] and [solveLL] procedures *)
Ltac CleanContext :=
  repeat
    match goal with
    | [H : release _ |- _ ] => clear H
    | [H : ~ asynchronous _ |- _ ] => clear H
    | [H : ~ IsPositiveAtom _ |- _ ] => clear H
    | [H : [_] = [_] \/ [_] = [] /\ In _ [] |- _] => clear H
    | [H : exists (x : _), _ |- _ ] => destruct H
    | [H : _ /\ _ |- _ ] => destruct H
    end;subst.

(* Check if the permutation P applies to the sequent in H and rewrites it *)
Ltac LLPermH H P :=
  match goal with
  | [ H : seqN _ _ ?Gamma ?Delta _ |- _] =>
    let HP := fresh "H" in
    first[
        assert(HP : Permutation Gamma P ) by perm; rewrite HP in H;clear HP
      | assert(HP : Permutation Delta P ) by perm; rewrite HP in H;clear HP
      ]
  |[ H : seq _ ?Gamma ?Delta _ |- _] =>
   let HP := fresh "H" in
   first[
       assert(HP : Permutation Gamma P ) by perm; rewrite HP in H;clear HP
     | assert(HP : Permutation Delta P ) by perm; rewrite HP in H;clear HP
     ]
  end.
Ltac LLPerm P :=
  match goal with
  | [ |- seqN _ _ ?Gamma ?Delta _ ] =>
    let HP := fresh "H" in
    first[
        assert(HP : Permutation Gamma P ) by perm; rewrite HP;clear HP
      | assert(HP : Permutation Delta P ) by perm; rewrite HP;clear HP
      ]
  |[ |- seq _ ?Gamma ?Delta _ ] =>
   let HP := fresh "H" in
   first[
       assert(HP : Permutation Gamma P ) by perm; rewrite HP;clear HP
     | assert(HP : Permutation Delta P ) by perm; rewrite HP;clear HP
     ]
  end.

(** "rewrite perm_swap in H" would be enough for exchanging the first 2
elements of a list. However, such rewrite is quite slow (probably for
Coq's search mechanism in Class Instances). This tactic implement the
same step without using rewriting *)
Ltac permswap H :=
        let Hs := type of H in 
        match Hs with
        |  (seqN _ _ (?F :: ?G :: ?L) _ _) =>
           apply exchangeCCN with (CC':= (G :: F :: L)) in H;[|perm]
        |  (seq  _ (?F :: ?G :: ?L) _ _) =>
           apply exchangeCC with (CC':= (G :: F :: L)) in H;[|perm]
        end.
