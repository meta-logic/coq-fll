(**  ** Properties
     
Here we prove some of the properties reported in 

Joëlle Despeyroux, Amy Felty, Pietro Lio and Carlos Olarte: A Logical
Framework for Modelling Breast Cancer Progression
 *)

Require Export TSystem.Rules.
Require Export FLL.SL.FLLTactics.
Require Export FLL.Misc.Permutations.


Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


Hint Constructors plusOne : core .
Hint Constructors uniform_atm'  : core.
Hint Constructors IsTerm : core .
Hint Unfold EncodeRule : core  .
Hint Unfold EncodeRuleAP : core .

Notation " n '|---' B ';' L ';' X " := (seqN OLTheory n B L X) (at level 80).
Notation " '|--' B ';' L ';' X " := (seq OLTheory  B L X) (at level 80).

(** s it possible for a CTC, with mutations EPCAM,CD47 and fitness 3 ,
to become an extravasating CTC with fitness 8 ? What is the time delay
for such transition ? *)
Lemma Property1: forall n t, 
    |-- [] ; [ E{ fun  x  => perp (T{ x}  )} ** (perp C{ CN n;  bone;  8;  EPCDCDME} )  ;  atom T{ CN t} ; atom C{ CN n ;  blood ;  3 ;  EPCD}]   ;  (> []).
Proof with solveF;solveLL.
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


(** What is the time delay for a CTC with mutations EPCAM, CD47 and
fitness 3 or 4 to become an extravasating CTC with fitness between 6
and 9 ? *)
Lemma Property2: forall n t,
    |-- [] ; [E{ fun  x  => perp (T{ x}  )} **  ( (perp C{ CN n ; bone ; 6 ; EPCDCDME}) 
                                                 op (perp C{CN n ; bone ; 7 ; EPCDCDME}) op (perp C{CN n ; bone ; 8 ; EPCDCDME} ) 
                                                 op (perp C{CN n ; bone ; 9 ; EPCDCDME}) )] ; 
 ( > [atom T{ CN t}  ; atom  C{ CN n ; blood ; 3 ; EPCD}  & atom C{ CN n ; blood ; 4 ; EPCD} ]) .
Proof with solveF;solveLL.
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
    oplus1.
    oplus1.
    oplus1.
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
    oplus1.
    oplus1.
    oplus2.
Qed.


(** A cell in the breast, with mutation [ EP ], might have his fitness
oscillating from [ 1 ] to [ 2 ] and back ? *)
Lemma Property3_Seq1: forall n t,
    exists d,
 |-- [] ; [ E{ fun x => perp T{ x s+ d}} ** (perp C{ CN n; breast; 2; EP})   ; 
              atom T{ CN t} ; atom C{ CN n ; breast ; 1 ; EP}]   ; (> []).
Proof with solveF;solveLL.
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
Proof with solveF;solveLL .
  intros.
  exists (CN (d20 2)).
  ApplyRule (bre0 2).
  (* Proving the goal *)
  decide1 (E{ fun x  => perp T{ x s+ CN (d20 2)}} ** perp C{ CN n; breast; 1; EP}).
  SplitContext' 1.
  apply tensorapp'...
  existential (CN t).
Qed.
  

(** Case analysis on each of the rules of the [Theory] *)
Ltac CaseRule :=
  match goal with
    [ HR : In _ ?R |- _ ] =>  inversion HR;subst;clear HR
  end.



Lemma PermutationState:
  forall t t' n n' c c' ft ft' lm lm' N,
    Permutation [atom T{ CN t}; atom C{ CN n; c; ft; lm}] (atom T{ t'} :: atom C{ n'; c'; ft'; lm'} :: N) -> N = [] /\ t' = CN t /\ CN n = n' /\ c = c' /\ ft = ft' /\ lm = lm'.
Proof with solveF.
  
  intros.
  apply PProp_perm_select in H.
  destruct H...
  inversion H0...
  firstorder.
  CleanContext.
  apply Permutation_unq in H0.
  inversion H0...
Qed.



Ltac SolveCase :=
  match goal with
    [ H: |-- [] ; _ ; ( >> ?R _ _) |- _] =>
    unfold R in H; unfold EncodeRule in H ; FLLInversionAll;CleanContext
  | [ H: |-- [] ; _ ; ( >> ?R _ _ _) |- _] =>
    unfold R in H; unfold EncodeRule in H ; FLLInversionAll;CleanContext
  end ;                                                                                                    
  match goal with
    [ H1 : Permutation _ (?M ++ _) ,  H2: Permutation ?M _ |- _] =>
    rewrite H2 in H1;simpl in H1;
    apply PermutationState in H1;solveF;clear H2;
    match goal with
    | [H3 : _ = _ |- _ ] => solve [inversion H3 | eexists;eauto]
    end
  end.



(** Any cell having a null fitness must go to apoptosis  *)
Theorem Property4 : 
  forall (n t :nat) c lm ,  
    |-- [] ; [ atom  T{ CN t} ; atom C{ CN n ; c; 0 ; lm} ] ; UP [] ->
     exists d, |-- [] ; [ atom  T{ (CN t)  s+ d } ; atom A{ CN n } ] ; UP [].
  Proof with solveF.
  intros.
  inversion H...
  (** cannot decide on a formula of the linear context *)
  {apply Remove_In in H1...
   inversion H1...
   rewrite <- H4 in H0...
  }
  clear H.
  inversion H0...
  idtac "Checking 171 rules (this may take a while)".
  repeat first [ CaseRule | SolveCase | eauto].
Qed.
