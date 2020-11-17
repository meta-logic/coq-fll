(** * Utils *)
(** Common definitions including:
 -  theorems about lists and permutation.  
 -  the induction scheme for Strong Induction
 -  some arithmetic results (specially dealing with [max] and [min])
 *)

Require Export Coq.Relations.Relations.
Require Export Coq.Classes.Morphisms.
Require Export Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Export Coq.Lists.List.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Arith.Arith.
Require Export Coq.Init.Nat.
Require Import Lia.


Export ListNotations.

Set Implicit Arguments.


(** ** Operations on lists/multisets *)
Section MultisetOperations.
  Variable T:Type.

  (** removing an element from a list *)
  Inductive Remove :T -> list T -> list T -> Prop :=
  | Remove1: forall t l, Remove t (t::l) l
  | Remove2: forall t t' l1 l2,  Remove t l1 l2 -> Remove t (t'::l1) (t'::l2).
  
End MultisetOperations.

Hint Constructors Remove : core .

(** ** Additional results on lists *)
Section List.
  (** Bringing an element to the front of the list *)
  (** e.g., [FrontApp 3 [1;2;3;4;5]] returns the triple ([[3] , [1;2] , [4;5]]) *)
  Definition FrontApp {A:Type} (n:nat) (L : list A)   :=
    let n' := pred n in
    match L with
    | nil => ( nil , nil , nil)
    | a::L' => ( [nth n' ((a::L')) a] , firstn n' (a::L') ,  skipn n (a::L'))
    end.

  Lemma AppNilNil : forall {A:Type} (L L' : list A), [] = L ++ L' -> L =[] /\ L' = [].
    intros.
    destruct L;destruct L';simpl;auto.
    simpl in H;inversion H.
    simpl in H;inversion H.
  Qed.

End List.

(** ** Additional results about permutations *)
Section Permutations.
  Variable A:Type.

  Lemma Perm_swap_inv : forall (x y : A) (N M : list A),
      Permutation (x :: N) (y :: x :: M) ->
      Permutation N ( y :: M).
    intros.
    rewrite perm_swap in H.
    apply Permutation_cons_inv in H;auto.
  Qed.

  Lemma Perm_swap_inv_app : forall y N M (x : A) ,
      Permutation (x :: N) (y ++ x :: M) ->
      Permutation N ( y ++ M).
    intros.
    rewrite  (Permutation_cons_append M x) in H.
    rewrite  Permutation_cons_append in H.
    rewrite app_assoc in H.
    rewrite  <- Permutation_cons_append in H.
    rewrite  <- (Permutation_cons_append (y ++ M) x ) in H.
    apply Permutation_cons_inv in H;auto.
  Qed.

  Theorem PermutConsApp: forall (a : A) l1 b l2,
      Permutation (a :: l1 ++ b :: l2) (b :: a :: l1 ++ l2).
    intros.
    rewrite perm_swap.
    rewrite <- Permutation_middle.
    auto.
  Qed.

  Lemma PermutationInCons : forall (F:A) M N,
      Permutation (F::M) N -> In F N.
    intros.
    eapply Permutation_in with (x:= F) (l':=N);eauto.
    constructor;auto.
  Qed.


  (** A slightly different version of  [Permutation_map] *)
  Lemma PermuteMap : forall (L L' : list A) (f: A->Prop),
      Forall f L -> Permutation L L'-> Forall f L'.
    intros.
    apply Permutation_sym in H0.
    assert(forall x, In x L' -> In x L) by eauto using Permutation_in.
    rewrite Forall_forall in H.
    rewrite Forall_forall;intros.
    firstorder.
  Qed.

  Lemma Permutation_unq : forall (L :list A) (F :A),
      Permutation [F] L -> L = [F].
    intros.
    destruct L.
    + apply Permutation_sym in H.
      apply Permutation_nil_cons in H.
      contradiction. 
    + assert(Hl : (length  L) = 0).
      apply Permutation_length in H;simpl in H.
      inversion H;auto.
      apply length_zero_iff_nil in Hl;subst.
      apply Permutation_length_1 in H;subst;auto.
  Qed.

  Lemma Permutation_nil' : forall (L : list A),
      Permutation L [] -> L = [].
    intros.
    apply Permutation_sym in H.
    apply Permutation_nil;auto.
  Qed.

  Lemma Permutation_mid : forall (F:A) l1 l2 l1' l2', 
      Permutation (l1 ++ F :: l2) (l1' ++ F :: l2') ->
      Permutation (l1 ++ l2) (l1' ++ l2').
    intros.
    assert(Permutation (F::l2) (l2 ++ [F]))
      by  apply Permutation_cons_append.
    rewrite H0 in H.
    assert(Permutation (F::l2') (l2' ++ [F]))
      by  apply Permutation_cons_append.
    rewrite H1 in H.
    apply Permutation_app_inv_r with (l:= [F]).
    do 2 rewrite app_assoc_reverse;auto.
  Qed.

  Lemma Permutation_midle : forall  (F:A) l1 l2,
      Permutation (l1 ++ F :: l2) ( F :: l1  ++ l2).
    intros.
    generalize (Permutation_cons_append  l1 F);intro.
    change (F::l1++l2) with ( (F::l1) ++ l2).
    rewrite H.
    assert(l1 ++ F :: l2 = (l1 ++ [F]) ++ l2).
    rewrite app_assoc_reverse;auto.
    rewrite H0.
    auto.
  Qed.

  Lemma Permutation_midle_app : forall  (la lb lc: list A),
      Permutation (la ++ lb ++ lc) ( lb ++ la  ++ lc).
    intros.
    rewrite <- app_assoc_reverse. 
    rewrite Permutation_app_comm with (l:=la).
    rewrite app_assoc_reverse;auto.
  Qed.

  
  
  Lemma InPermutation : forall (l:A) L,
      In l L -> exists L', Permutation L (l :: L').
    induction L;intros.
    inversion H.
    inversion H;subst.
    exists L;auto.
    apply IHL in H0.
    destruct H0 as [L' H0].
    exists (a :: L').
    rewrite H0.
    constructor.
  Qed.

  Lemma PermutationNeqIn : forall (F G :A) N M,
      Permutation (F :: N) (G :: M) -> F <> G ->
      exists M', Permutation M (F :: M').
    intros.
    apply Permutation_in with (x:= F)in H.
    inversion H.
    subst;contradiction.
    apply InPermutation in H1.
    firstorder.
    constructor;auto.

  Qed.

  Lemma Per_app_assoc : forall  (A' B C : list A),
      Permutation (A' ++ B ++ C) ( (A' ++ B) ++ C).
    intros.
    rewrite app_assoc;auto.
  Qed.
  
  Lemma Per_app_assoc_comm : forall (A' B C : list A),
      Permutation (A' ++ B ++ C) ( (A' ++ C) ++ B).
    intros.
    rewrite (Permutation_app_comm B C).
    rewrite app_assoc;auto.
  Qed.

  Lemma Per_app_assoc_comm' : forall  (A' B C : list A),
      Permutation (A' ++ B ++ C) (A' ++ C ++ B).
    intros.
    rewrite (Permutation_app_comm C B);auto.
  Qed.

  Lemma Per_app_assoc_comm'' : forall   (A' B C : list A),
      Permutation (A' ++ B ++ C) (B ++ A' ++ C).
    intros.
    rewrite app_assoc.
    rewrite (Permutation_app_comm A' B).
    rewrite app_assoc_reverse;auto.
  Qed.

End Permutations.

(** ** Properties about [Remove] *)
Section Remove.
  Variable A:Type.
  Lemma Remove_In  : forall (F: A) (L L' :list A),
      Remove F L L' -> In F L.
    induction L;intros.
    + inversion H.    
    + inversion H;subst.
      ++ constructor;auto.
      ++ apply IHL in H4.
         right;auto.
  Qed.

  Lemma In_Remove  : forall (F: A) (L :list A),
      In F L -> exists L', Remove F L L'.
    induction L;intros.
    + inversion H. 
    + inversion H;subst.
      ++ exists L.
         constructor.
      ++ apply IHL in H0.
         destruct H0 as [L'].
         exists (a::L').
         constructor;auto.
  Qed.

  Lemma RemoveUnique : forall (F G:A) L,
      Remove F [G] L -> F = G.
    intros.
    apply Remove_In in H.
    inversion H;auto.
    inversion H0.
  Qed.

  Lemma Remove_app_head : forall (F:A) L1 L1' L2,
      Remove F L1 L1' -> Remove F (L2 ++ L1) (L2 ++ L1').
    induction L2;intros;auto.
    apply IHL2 in H.
    change ((a :: L2) ++ L1) with (a :: (L2 ++ L1)) .
    change ((a :: L2) ++ L1') with (a :: (L2 ++ L1')) .
    apply Remove2;auto.
  Qed.

  Lemma Remove_app_in : forall (F:A) L1 L2,
      Remove F (L1 ++ F :: L2) (L1 ++ L2).
    intros.
    apply Remove_app_head.
    constructor.
  Qed.

  Lemma Remove_head: forall (F:A) L1 L,
      Remove F (F :: L1) L ->
      L = L1 \/ (exists l1, L = F::l1 /\ Remove F L1 l1).
    intros.
    inversion H;subst;auto.
    right.
    exists l2;auto.
  Qed.

  Lemma Remove_inv: forall (F:A) a L L1,
      Remove F L (a :: L1) ->
      exists b1 b2 L2, L = b1 :: b2 :: L2 /\
                       ( ( b1=F /\ a::L1 = b2::L2) \/
                         (a=b1 /\ Remove F (b2::L2) L1) ) .
  Proof with subst.
    intros.
    revert dependent L1.
    revert dependent a.
    revert dependent F.
    induction L;intros ...
    + inversion H.
    + inversion H ...
      repeat eexists;auto.
      destruct L1.
      ++  inversion H2 ...
          repeat eexists;auto.
      ++ apply IHL in H2.
         destruct H2 as [b1 [b2 [ L2 [H2 H2']]]].
         destruct H2'.
         +++ inversion H2 ...
             repeat eexists;auto.
             right; firstorder ...
             inversion H2...
             constructor.
         +++ destruct H0 ...
             repeat eexists;auto.
  Qed.

  Lemma Remove_inv_cons: forall (F:A) a L L1,
      Remove F (a::L) L1 ->
      (F =a /\ L = L1) \/
      (exists L1', L1 = a::L1' /\ Remove F L L1') .
    intros.
    inversion H;subst.
    + left;auto.
    + right.
      eexists.
      eauto.
  Qed.

End Remove.


(** ** Preperties relating [Remove] and [Permutation] *)
Section RemovePermutation.
  Variable A:Type.
  Lemma Remove_Permutation_Ex  : forall (F : A) (L L' M : list A),
      Remove F L L' -> Permutation L M -> exists M', Remove F M M'. 
    intros.
    apply Remove_In in H as Hrm.
    destruct L.
    + inversion Hrm.
    + assert(In F M).
      eapply Permutation_in;eauto.
      apply In_Remove;auto.
  Qed.

  Lemma Remove_upto_permute : forall (F:A) L1 L2 L,
      Remove F L L1 -> Remove F L L2 ->  Permutation L1 L2.
  Proof with subst.
    intros.
    revert dependent L1.
    revert dependent L2.
    induction L;intros.
    +  inversion H.
    + apply Remove_inv_cons in H as H'.
      apply Remove_inv_cons in H0 as H0'.
      destruct H';destruct H0'.
      ++ firstorder;subst;auto. (* case both took the first element *)
      ++ firstorder...
         apply Remove_In in H4 as H4'.
         apply In_Remove in H4'.
         destruct H4'.
         assert (Permutation x x0) by  (eapply IHL;eauto).
         apply Remove_In in H1 as H1'.
         apply in_split in H1'.
         firstorder ...
         assert (Remove a (x1 ++ a :: x2) (x1++x2)) by apply Remove_app_in.
         generalize (IHL x0 H1 (x1++x2) H3);intro.
         assert (Permutation  (a:: x1 ++ x2) (x1 ++a :: x2) ) by  apply Permutation_middle.
         rewrite <- H6.
         constructor.
         rewrite H5.
         rewrite H2.
         auto.
      ++ firstorder...
         apply Remove_In in H4 as H4'.
         apply In_Remove in H4'.
         destruct H4'.
         assert (Permutation x x0) by  (eapply IHL;eauto).
         apply Remove_In in H1 as H1'.
         apply in_split in H1'.
         firstorder ...
         assert (Remove a (x1 ++ a :: x2) (x1++x2)) by apply Remove_app_in.
         generalize (IHL x0 H1 (x1++x2) H3);intro.
         assert (Permutation  (a:: x1 ++ x2) (x1 ++a :: x2) ) by  apply Permutation_middle.
         rewrite <- H6.
         constructor.
         rewrite H5.
         rewrite H2.
         auto.
      ++ firstorder;subst.
         generalize (IHL x0 H4 x H3);intro.
         constructor;auto.
  Qed.


  Lemma Remove_permute : forall (F:A) L1 L2 L,
      Remove F (L1 ++ F :: L2) L -> Permutation (L1 ++ L2) L.
    intros.
    assert(Remove  F (L1 ++ F :: L2) (L1 ++ L2)) by  apply Remove_app_in.
    eapply Remove_upto_permute;eauto.
  Qed.

  Lemma Remove_app_tail : forall (F:A) L1 L1' L2,
      Remove F L1 L1' -> Remove F (L1++L2) (L1'++L2).
    intros. induction H.
    *
      apply Remove1.
    *
      change ((t' :: l1) ++ L2) with (t' ::(l1 ++ L2)).
      change ((t' :: l2) ++ L2) with (t' ::(l2 ++ L2)).
      apply Remove2;auto.
  Qed.

  Lemma Remove_Permutation_Ex2  : forall (F : A) (L L' M : list A),
      Remove F L L' -> Permutation L M ->
      exists M', Remove F M M'  /\ Permutation M' L'.
    intros.
    assert(HFL: In F L) by eauto using Remove_In.
    assert(HFM: In F M).
    { apply Permutation_in with (x:=F) in H0; auto; constructor;auto. }
    apply In_nth_error in HFL as HFL'.
    destruct HFL' as [n  HFL'].
    apply nth_error_split in HFL'.
    destruct HFL' as [l1 [l2 [HFL' HFL''] ]];subst.
    apply In_nth_error in HFM as HFM'.
    destruct HFM' as [n  HFM'].
    apply nth_error_split in HFM'.
    destruct HFM' as [l1' [l2' [HFM' HFM''] ]];subst.
    exists (l1' ++ l2').
    split.
    + apply Remove_app_head.
      constructor.
    + apply Remove_permute in H.
      apply Permutation_mid in H0.
      rewrite <- H0.
      rewrite H.
      auto.
  Qed.

  Lemma Remove_Permute : forall (F : A) (L L' M : list A),
      Remove F L L' -> Permutation L (F :: L').
    induction L;intros.
    inversion H.
    apply Remove_inv_cons in H.
    firstorder;subst.
    constructor;auto.
    assert(Permutation (F::a::x) (a :: F ::x)).
    constructor.
    rewrite H.
    constructor.
    apply IHL;auto.
  Qed.

End RemovePermutation.


(** ** Strong Induction *)

Section StrongIndPrinciple.

  Variable P: nat -> Prop.

  Hypothesis P0: P O.

  Hypothesis Pn: forall n, (forall m, m<=n -> P m) -> P (S n).

  Lemma strind_hyp : forall n, (forall m, ((m <= n) -> P m)).
  Proof.
    induction n; intros m H;inversion H;auto.
  Qed.
  (** Strong induction principle *)
  Theorem strongind: forall n, P n.
  Proof.
    induction n; auto.
    apply Pn.
    apply strind_hyp.
  Qed.

End StrongIndPrinciple.


(** ** Aditional results on Arithmentic *)
Section Arithmentic.

  Lemma MaxPlus : forall a b, (max a b <= plus a  b).
    intros;lia.
  Qed.
  
  Lemma MaxPlus' : forall a b c, (plus a b <= c -> max a b <= c).
    intros;lia.
  Qed.
  
  
  Theorem GtExists : forall n, n>0 -> exists n', n = S n'.
    intros.
    destruct n;inversion H;subst;eauto.
  Qed.

End Arithmentic.

Ltac mgt0 := let H := fresh "H" in
             match goal with [_ :  ?m >= S _ |- _] =>
                             assert(H : m>0) by lia;
                             apply GtExists in H;
                             destruct H;subst
             end.

(** ** Aditional results on Forall/map *)
Section ForAllMap. 
  Lemma ForallAppInv1:
    forall {A : Type} {M N : list A} (f : A -> Prop),
      Forall f (N ++ M) -> Forall f N.
    induction N;auto;intros.
    inversion H;subst.
    apply IHN in H3.
    auto.
  Qed.

  Lemma ForallApp : forall {A: Type} (M N : list A) (f : A->Prop),
      Forall f N ->  Forall f M -> Forall f (N ++ M).
    intros.
    apply Forall_forall;intros.
    rewrite Forall_forall in H.
    rewrite Forall_forall in H0.
    apply in_app_or in H1.
    destruct H1;auto.
  Qed.
  
  Lemma ForallAppInv2:
    forall {A : Type} {M N : list A} (f : A -> Prop),
      Forall f (N ++ M) -> Forall f M.
    induction N;auto;intros.
    inversion H;subst.
    apply IHN in H3;auto.
  Qed.
  
  Lemma ForallAppComm:
    forall {A : Type} {M N : list A} (f : A -> Prop),
      Forall f (N ++ M) -> Forall f (M ++ N).
    intros. eapply PermuteMap;eauto.
    apply Permutation_app_comm.
  Qed.
  
  Lemma Forall_Permute:
    forall {A : Type} {M N : list A} (f : A -> Prop),
      Forall f M -> Permutation M N -> Forall f N.
  Proof with subst;auto.
    induction 2...
    inversion H...
    inversion H...
    inversion H3...
  Qed.

  Lemma Forall_Permute':
    forall {A : Type} {M N O: list A} (f : A -> Prop),
      Forall f M -> Permutation M N -> Permutation N O -> Forall f O.
  Proof with subst;auto.
    intros.
    assert(Permutation M O). 
    apply (Permutation_trans H0 H1).
    apply (Forall_Permute H H2).
  Qed.
  
  Hint Extern 1 (Permutation ?S ?U) =>
  match goal with
  | H: Permutation S ?T |- _ => apply (Permutation_trans H)
  | H: Permutation ?T S  |- _ => symmetry in H; apply (Permutation_trans H)  
  end : core.
  
  Example transitivity_Permutation : forall {A : Type} (f : A -> Prop){T1 T2 T3 T4 T5: list A},
  Forall f T1 ->
  Permutation T1 T2 ->
  Permutation T2 T3 ->
  Permutation T4 T3 ->
  Permutation T3 T5 ->
  Permutation T5 T4 ->
  Forall f T4.
Proof.
  intros.
  eauto using Forall_Permute'.
Qed.
  
   
  Generalizable All Variables.
  Global Instance Forall_morph : 
    Proper ((@Permutation A) ==> Basics.impl) (Forall f).
  Proof.
    unfold Proper; unfold respectful; unfold Basics.impl.
    intros.
    eapply Forall_Permute;eauto.
  Qed. 
  
  Lemma ForallCons : forall {A: Type} (F:A) (M : list A) (f : A->Prop), 
      f F ->  Forall f M -> Forall f (F :: M).
    intros.
    change (F :: M) with ([F] ++ M).
    apply ForallApp;auto.
  Qed.                
  
  Lemma isFormulaIn :  forall {A : Type} {F : A} {L : list A} (f : A -> Prop), 
      Forall f L -> In F L -> f F. 
  Proof.
    intros.
    generalize (Forall_forall f L );intro.
    destruct H1.
    apply H1 with (x:= F) in H ;auto.
  Qed.
  
  Hint Resolve ForallApp:isFormulaIn.
  Hint Resolve ForallApp:core.
  Hint Resolve ForallCons:core.
  
End ForAllMap .

Ltac solveForall :=
    match goal with
    | [ H1: ?f ?F, H2: Forall ?f ?M  |- Forall ?f (?F :: ?M)] => apply ForallCons;auto
    | [ H1: Forall ?f ?M, H2: Forall ?f ?N  |- Forall ?f (?M ++ ?N)] => apply ForallApp;auto
    | [ H: Forall ?f (?M ++ ?N)  |- Forall ?f ?M] => apply (Forall_app _ M N);auto
    | [ H: Forall ?f (?M ++ ?N)  |- Forall ?f ?N] => apply (Forall_app _ M N);auto
    | [ H1: In ?F ?L, H2: Forall ?f ?L  |- ?f ?F] => apply (isFormulaIn H2 H1);auto
    | [ H: Forall ?f (?M ++ ?N)  |- Forall ?f (?N ++ ?M)] => apply ForallAppComm;auto
    | [ H1: Forall ?f ?T1, 
        H2: Permutation ?T1 ?X,
        H3: Permutation ?Y ?T2  |- Forall ?f ?T2] =>  eauto using Forall_Permute'
        | [ H1: Forall ?f ?T1, 
        H2: Permutation ?T1 ?T2  |- Forall ?f ?T2] =>  eauto using Forall_Permute'
        
    | [ H: Forall ?f (?M ++ ?F :: ?N)  |- ?f ?F] => apply (Forall_elt _ _ _ H);auto 
    | [ H: Forall ?f (?F :: ?L)  |- ?f ?F] => apply (Forall_inv H);auto 
    | [ H: Forall ?f (?F :: ?L)  |- Forall ?f ?L] => apply (Forall_inv_tail H);auto 
    | [ H1: Forall ?f (?F :: ?M), H2: Forall ?f ?N  |- Forall ?f (?F :: ?N)] => inversion H;subst;auto 
      
    | [ H: Forall ?f (?F :: ?M) |- Forall ?f (?M ++ [?F]) ] => inversion H;subst;auto
    | [ H1: Forall ?f (?F :: ?M), H2: Forall ?f ?N  |- Forall ?f (?N ++ [?F])] => inversion H;subst;auto
    
    | [ H: ?f (_ ?A) |- ?f ?A ] => inversion H;subst;auto
    | [ H: ?f (_ ?A1 ?A2) |- ?f ?A1 ] => inversion H;subst;auto 
    | [ H: ?f (_ ?A1 ?A2) |- ?f ?A2 ] => inversion H;subst;auto
    
    
    end.
   

(** Solving some of the [Permutation] goals appearing in the proof *)
Ltac SolvePermutation :=
  repeat
    match goal with
    | [ |- Permutation (?F :: _) (?F :: _)] => apply perm_skip
    | [ |- Permutation _ _] =>
      auto using  Permutation_sym,  Per_app_assoc, Per_app_assoc_comm,
      Per_app_assoc_comm', Per_app_assoc_comm''
    end.
