(** * System LK for propositional classical logic encoded as an LL theory

This file encodes the inference rules of the system LK (propositional
classical logic). The cut-coherence and well-formedness properties are
proved and then, using [OLCutElimination] we prove the cut-elimination
theorem for this system .
 *)

Require Export FLL.OL.OLCutc.
Require Import Coq.Init.Nat.
Require Import FLL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


(** ** Syntax *)
(* units: true and false *)
Inductive Constants := TT | FF  .
(* conjunction, disjunction and implication *)
Inductive Connectives := AND | OR | IMP  .
(* no quantifiers *)
Inductive Quantifiers := ALL|SOME .

Inductive UConnectives := .

Instance SimpleOLSig : OLSyntax:=
  {|
    OLType := nat;
    constants := Constants ;
    uconnectives := UConnectives;
    connectives := Connectives ;
    quantifiers := Quantifiers
  |}.


(** ** Inference rules *)

(** *** Constants *)
Definition rulesCTE (c:constants) :=
  match c with
  | TT => ZEROTOP
  | FF => TOPZERO
  end.

(** *** Binary connectives *)
Definition rulesBC (c :connectives) :=
  match c with
  | AND => PARTENSOR
  | OR =>  TENSORPAR
  | IMP => TENSORPAREXCH
  end.

(** *** Quantifiers *)
Definition rulesQD (q :quantifiers) :=
  match q with
  | ALL => ALLSOME
  | SOME => SOMEALL
  end
.

Instance SimpleOORUles : OORules :=
  {|
    rulesCte := rulesCTE ;
    rulesBin := rulesBC;
    rulesQ := rulesQD
  |}.


Inductive LKSeq : list uexp -> list uexp -> Prop :=
| LKTRUE : forall L L', LKSeq L ((t_cons TT)::L')
| LKFALSE : forall L L', LKSeq (t_cons FF :: L) L' 
| LKinit : forall L L' F,  LKSeq (F:: L) (F::L')
| LKAndL : forall L F G L', LKSeq (F :: G :: L) L' -> LKSeq ( (t_bin AND F G) :: L) L'
| LKAndR : forall L F G L' , LKSeq L (F::L') -> LKSeq L (G::L') -> LKSeq L (t_bin AND F G :: L')
| LKOrL : forall L F G L',  LKSeq (F :: L) L' ->  LKSeq (G :: L) L' -> LKSeq ( (t_bin OR F G) :: L) L'
| LKOrR : forall L F G L' , LKSeq L (F::G::L') -> LKSeq L (t_bin OR F G :: L')
| LKImpL : forall L A B L' , LKSeq L (A::L') -> LKSeq (B:: L) L' -> LKSeq (t_bin IMP A B ::L) L'
| LKImpR : forall L A B L' , LKSeq (A:: L) (B::L') ->  LKSeq L (t_bin IMP A B :: L')
| LKAllL : forall L t FX L', uniform FX -> proper t -> LKSeq( FX t :: L) L' -> LKSeq (t_quant ALL FX :: L) L'
| LKAllR : forall L FX L' , uniform FX -> (forall x, proper x -> LKSeq L ((FX x)::L')) -> LKSeq L (t_quant ALL FX :: L')
| LKSomeL : forall L FX L', uniform FX -> (forall x, proper x -> LKSeq (FX x:: L) L') -> LKSeq (t_quant SOME FX :: L) L'
| LKSomeR : forall L FX t L', uniform FX -> proper t -> LKSeq L ((FX t)::L')-> LKSeq L (t_quant SOME FX::L')
(* Explicit exchange *)
| LKExL : forall L L' Delta, Permutation L L' -> LKSeq L Delta -> LKSeq L' Delta
| LKExR : forall L L' Delta, Permutation L L' -> LKSeq Delta L -> LKSeq Delta L'
(* Explicit contraction *)
| LKCtL : forall L L' F, LKSeq (F :: F :: L)  L' -> LKSeq (F :: L)  L'
| LKCtR : forall L L' F, LKSeq L (F :: F :: L')   -> LKSeq L (F :: L')
.

Hint Constructors LKSeq : core .
Hint Constructors OLTheory buildTheory : core.
Hint Constructors  isOLFormula : core. 
Hint Unfold IsPositiveLAtomFormulaL : core. 
Hint Constructors IsPositiveRAtomFormula : core .


Global Instance LKL_morph : 
  Proper ((@Permutation uexp) ==> eq ==> iff) (LKSeq).
Proof.
  unfold Proper; unfold respectful. 
  intros.
  split;intros;subst.
  eapply LKExL;eauto.
  apply Permutation_sym in H.
  eapply LKExL;eauto.
Qed.

Global Instance LKR_morph : 
  Proper (eq ==> (@Permutation uexp)  ==> iff) (LKSeq).
Proof.
  unfold Proper; unfold respectful. 
  intros.
  split;intros;subst.
  eapply LKExR;eauto.
  apply Permutation_sym in H0.
  eapply LKExR;eauto.
Qed.


Ltac toLK H :=
  match (type of H) with
  | In (u| _ |)(LEncode _ ++ REncode _) =>
    apply upRight in H; apply OLInPermutation in H;CleanContext;
    eapply LKExR; [apply Permutation_sym; eauto|]
  | In (d| _ |)(LEncode _ ++ REncode _) =>
    apply downLeft in H; apply OLInPermutationL in H;CleanContext;
    eapply LKExL; [apply Permutation_sym;eauto | ]
  | seqN _ _ (u| ?F | :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := LEncode L ++ REncode (F :: R)) in H ;[| simpl; perm]
  | seqN _ _ (u| ?F | :: ?T :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := T :: LEncode L ++ REncode (F :: R)) in H ;[| simpl; perm]
  | seqN _ _ (d| ?F | :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := LEncode (F :: L) ++ REncode R) in H ;[| simpl; perm]
  | seqN _ _ (d| ?F | :: ?T :: LEncode ?L ++ REncode ?R) [] (> []) =>
    apply exchangeCCN with (CC' := T :: LEncode (F::L) ++ REncode R) in H ;[| simpl; perm]
  end.



Ltac solveOLTheory :=
  try
    match goal with
    | [H : isOLFormulaL (?F :: _) |-  OLTheory (RINIT ?F)] =>
      solve [inversion H0; apply ooth_init;auto]
    | [ H: isOLFormulaL (_  _ ?F::?L)|- OLTheory _ ] =>
      solve [do 2 constructor;inversion H;subst;auto ]
    | [ H: _|- OLTheory _ ] =>
      solve [do 2 constructor;auto ]
    end.

Theorem Soundeness: forall L L', LKSeq L L' ->
                                 isOLFormulaL L ->
                                 isOLFormulaL L' ->
                                 seq OLTheory (LEncode L ++  REncode L') [] (> []).
Proof with solveF;solveLL;solveOLTheory;SolveIS. 
  intros.
  induction H. 
  + (* True on the right *)
    decide3 (makeRuleConstant TT Right)...
    apply in_or_app...
  + (* false on the left *)
    decide3 (makeRuleConstant FF Left)...
  + (* init *)
    decide3 (RINIT F)...
    tensor (@nil oo) (@nil oo)...
    right...
    apply in_or_app...
  + (* ANDL1 *)
    decide3 (makeRuleBin AND Left F G)...      
    LLPerm (d| t_bin AND F G | :: d| F | ::  d| G | :: (LEncode L ++ REncode L')).
    apply weakening.
    apply IHLKSeq...
  + (* And R *)
    decide3 (makeRuleBin AND Right F G)...
    apply in_or_app...
    LLPerm (u| t_bin AND F G | :: (LEncode L ++ ( u| F | :: REncode L') )) .
    apply weakening...
    apply IHLKSeq1...
    LLPerm (u| t_bin AND F G | :: (LEncode L ++ ( u| G | :: REncode L') )) .
    apply weakening...
    apply IHLKSeq2...
  + (* Or L *)
    decide3 (makeRuleBin OR Left F G)...
    apply weakening. LLPerm( ( d| F | :: LEncode L) ++ REncode L').
    apply IHLKSeq1... 
    
    apply weakening. LLPerm( ( d| G | :: LEncode L) ++ REncode L').
    apply IHLKSeq2...
  +  (* OrR *)
    decide3 (makeRuleBin OR Right F G)...
    apply in_or_app...
    LLPerm ( u| t_bin OR F G | :: (LEncode L  ++  (u| F | :: u| G | ::  REncode L') )) .
    apply weakening.
    apply IHLKSeq...
  + (* implication left *)
    decide3 (makeRuleBin IMP Left A B)...
    apply weakening.
    LLPerm  ((LEncode L ++ (u| A | :: REncode L'))).
    apply IHLKSeq1... 
    apply weakening.
    LLPerm ( (d| B | :: LEncode L) ++ REncode L').
    apply IHLKSeq2... 
    
  + (* implication right *)
    decide3 (makeRuleBin IMP Right A B)... 
    apply in_or_app...
    LLPerm  ( u| t_bin IMP A B | :: ( d| A | :: LEncode L) ++ ( u| B | :: REncode L') ).
    apply weakening.
    apply IHLKSeq...
  + (* forall left *)
    decide3 (makeRuleQ ALL Left FX)...
    existential t...
    apply weakening.
    LLPerm (( d| FX t | :: LEncode L) ++ REncode L' ).
    apply IHLKSeq...
  + (* forall right *)
    decide3 (makeRuleQ ALL Right FX)...
    apply in_or_app...
    LLPerm (u| t_quant ALL FX | :: (LEncode L ++ (u| FX x | ::REncode L') )).
    apply weakening...
    apply H3...
  + (* existst left *)
    decide3 (makeRuleQ SOME Left FX)... 
    apply weakening...
    
    LLPerm (( d| FX x | :: LEncode L) ++ REncode L') .
    apply H3...
  + (* exists right *)
    decide3 (makeRuleQ SOME Right FX)...
    apply in_or_app...
    existential t...
    LLPerm  (u| t_quant SOME FX | :: (LEncode L ++ u| FX t | :: REncode L') ).
    apply weakening...
    apply IHLKSeq...
  + (* exchange *)
    eapply Permutation_map in  H as H'.
    unfold LEncode; rewrite <- H'...
    apply IHLKSeq...
    rewrite H...
  + eapply Permutation_map in  H as H'.
    unfold REncode; rewrite <- H'...
    apply IHLKSeq...
    rewrite H...
  + (* contraction *)
    simpl.
    assert(seq OLTheory (d| F | :: d| F | :: LEncode L ++ REncode L') [] (> [])).
    apply IHLKSeq...
    constructor...
    eapply contraction in H2...
  + assert (seq OLTheory (LEncode L ++ REncode (F :: F :: L')) [] (> [])).
    apply IHLKSeq...
    constructor...
    simpl in H2.
    LLPermH H2 (u| F | :: u| F | :: LEncode L ++  REncode L') .
    simpl.
    eapply contraction in H2... LLExact H2.
Qed.


Theorem Completeness: forall n L L' , 
    isOLFormulaL L ->
    isOLFormulaL L' ->
    seqN OLTheory n (LEncode L ++  REncode L') [] (> []) ->
    LKSeq L L' .
Proof with solveF;solveLL;SolveIS;CleanContext.
  induction n using strongind;intros L L' HisL HisL' Hseq; inversion Hseq;subst.
  inversion H2.
  apply InIsPositive in H2;contradiction.
  inversion H1...
  + (* from the theory *)
    inversion H0...
    ++ (* Constant right *)
      apply FocusingRightCte in H3...
      (* by cases on C *)
      destruct C;simpl in H5...
      toLK H4...
    ++ (* constant left *)
      apply FocusingLeftCte in H3...
      (* by cases on C *)
      destruct C;simpl in H4...
      toLK H4...
      inversion H5...
      toLK H4...
    ++ (* binary connective right *)
      apply FocusingRightRule in H3...
      (* by cases on C *)
      destruct C;simpl in H5...
      { (* case AND *)
        apply AppPARTENSORRight in H5...
        toLK H4.
        toLK H5.
        toLK H6.
        apply LKCtR.
        apply LKAndR; rewrite <- H3;
          eapply H with (m:= x0)...
      }
      { (*  OR *)
        apply AppTENSORPARRight in H5...
        toLK H4.
        do 2 toLK H5.
        apply LKCtR.
        apply LKOrR; rewrite <- H3;
          eapply H with (m:= x0)...
        simpl in H5... LLExact H5.
      }
      { (* impl *)
        apply AppTENSORPAREXCHRight in H5...
        toLK H4.
        do 2 toLK H5.
        apply LKCtR.
        apply LKImpR; rewrite <- H3;
          eapply H with (m:= x0)...
      }
    ++  (* binary connective left *)
      apply FocusingLeftRule in H3...
      (* by cases on C *)
      destruct C;simpl in H5...
      { (* case AND *)
        apply AppPARTENSORLeft in H5...
        toLK H4.
        do 2 toLK H5.
        apply LKCtL.
        apply LKAndL; rewrite <- H3.
        eapply H with (m:= x0)...
        simpl in H5. LLExact H5.
      }
      {(*  OR *)
        apply AppTENSORPARLeft in H5...
        toLK H4.
        toLK H5.
        toLK H6.
        apply LKCtL.
        apply LKOrL; rewrite <- H3; eapply H with (m:= x0)...
      }
      { (* impl *)
        apply AppTENSORPAREXCHLeft in H5...
        toLK H4.
        toLK H5.
        toLK H6.
        apply LKCtL.
        apply LKImpL; rewrite <- H3; eapply H with (m:= x0)...
      }
    ++ (* quantifier *)
      apply FocusingRightQ in H3...
      (* by cases on C *)
      destruct C;simpl in H6...
      { (* All *)
        apply AppALLSOMERight in H6...
        toLK H5.
        apply LKCtR.
        apply LKAllR;auto;intros ;rewrite <- H3...
        specialize (H6 x1 H5).
        toLK H6.
        eapply H with (m:= x0)...
      }
      { (* Exists *)
        apply AppSOMEALLRight in H6...
        toLK H5.
        apply LKCtR.
        eapply LKSomeR;eauto ;rewrite <- H3...
        apply H with (m:= x0)...
        LLExact H7.
      }
    ++ (* quantifier left *)
      apply FocusingLeftQ in H3...
      (* by cases on C *)
      destruct C;simpl in H6...
      { (* All *)
        apply AppALLSOMELeft in H6...
        toLK H5.
        toLK H7.
        apply LKCtL.
        eapply LKAllL;eauto; rewrite <- H3...
        eapply H with (m:= x0)...
      }
      { (* some *)
        apply AppSOMEALLLeft in H6...
        toLK H5.
        apply LKCtL.
        eapply LKSomeL;auto;intros;rewrite <- H3.
        specialize ( H6 x1 H5)...
        toLK H6.
        eapply H with (m:= x0)...
      }
  + (* init *)
    apply Init_inversion1 in H3...
    toLK H2.
    toLK H3.
    apply LKinit.
Qed.

Theorem Adequacy:  forall L L' , 
    isOLFormulaL L ->
    isOLFormulaL L' ->
    (
      seq OLTheory  (LEncode L ++ REncode L') [] (> []) <->
      LKSeq L L' ).
Proof with solveF;solveLL.
  intros.
  split;intros.
  + apply seqtoSeqN in H1;CleanContext.
    apply  Completeness in H1...
  +  apply Soundeness in H1...
Qed.
(** The cut-elimination theorem instantiated for LK *)
Check Adequacy .
Check CutElimination.

