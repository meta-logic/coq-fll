(** * System LM for propositional minimal logic encoded as an LL theory

This file encodes the inference rules of the system LM (propositional
minimal logic). The cut-coherence and well-formedness properties are
proved and then, using [OLCutElimination] we prove the cut-elimination
theorem for this system .
 *)

Require Export FLL.OL.OLCutElimTheorem.
Require Import Coq.Init.Nat.
Require Import FLL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


(** ** Syntax *)
(* No constants *)
Inductive Constants := .
(* conjunction, disjunction and implication *)
Inductive Connectives := AND | OR | IMPL  .
(* no quantifiers *)
Inductive Quantifiers := .
(* No unary connectives  *) 
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
  match c return ruleCte with 
  end.

(** *** Unary connectives *)
Definition rulesUC  (c:uconnectives) :=
  match c return ruleUnary with
  end.

(** *** Binary connectives *)
Definition rulesBC (c :connectives) :=
  match c with
  | AND => {| rb_rightBody := fun F G => (atom (up F)) ** (atom (up G) );
              rb_leftBody  := fun F G => (atom (down F) ) $ (atom (down G)) |}
  | OR => {| rb_rightBody := fun F G => (atom (up F)) op (atom (up G) );
             rb_leftBody  := fun F G => (atom (down F) ) & (atom (down G)) |}
  | IMPL => {| rb_rightBody := fun F G => (atom (down F)) $  (atom (up G) );
               rb_leftBody  := fun F G => (atom (up F) ) ** (atom (down G)) |}
  end.

(** *** Quantifiers *)
Definition rulesQC (c :quantifiers) :=
  match c return ruleQ with
  end.


Instance SimpleOORUles : OORules :=
  {|
    rulesCte := rulesCTE ;
    rulesUnary := rulesUC ;
    rulesBin := rulesBC;
    rulesQ := rulesQC
  |}.

(** ** Well-formedness conditions *)

Definition down' : uexp -> atm := down.
Definition up' : uexp -> atm := up.
Hint Unfold down' up' : core .

(** *** Constants *)
Lemma wellFormedConstant_p : wellFormedCte.
Proof with WFSolver.
  unfold wellFormedCte;intros.
  destruct lab.
Qed.


(** *** Unary connectives *)

Lemma wellFormedUnary_p : wellFormedUnary.
Proof with WFSolver.
  unfold wellFormedUnary;intros.
  destruct lab.
Qed.


(** *** Binary connectives *)
Lemma wellFormedBinary_p : wellFormedBinary.
Proof with WFSolver.
  unfold wellFormedBinary;intros.
  destruct lab;destruct s.
  + (* Conjunction left *)
    exists BOneP...
    intros n HSeq HIs...
    InvTriAll.
    
    ++ exists ([atom (down' Fo1)] ++ [atom (down' Go1)]).
       exists (@nil oo).
       eexists. exists 5...
       left.  exists N...
       decide3' (makeLRuleBin AND Fo1 Go1)...
       tensor' [(atom (down (t_bin AND Fo1 Go1)))] Delta1... 
    ++  exists ([atom (down' Fo1)] ++ [atom (down' Go1)]).
        exists (@nil oo).
        eexists. exists 5...
        rewrite H1.
        right...
        decide3' (makeLRuleBin AND Fo1 Go1).
        tensor' (@nil oo) Delta1...
  + (* Conjunction right *)
    exists BTwoPM...
    intros n HSeq HIs...
    InvTriAll...
    ++ exists M0.  exists N0.
       exists [atom (up' Fo1)].
       exists [atom (up' Go1)].
       exists (@nil oo). exists (@nil oo).
       eexists. exists 4...
       rewrite H1.
       left...
       tensor' M0 N0...
       decide3' (makeRRuleBin AND Fo1 Go1)...
       tensor' [(atom (up (t_bin AND Fo1 Go1)))] (Delta1 ++ Delta2)...
       tensor' Delta1 Delta2...
       
    ++ exists M0.  exists N0.
       exists [atom (up' Fo1)].
       exists [atom (up' Go1)].
       exists (@nil oo). exists (@nil oo).
       eexists. exists 4...
       rewrite H1.
       right...
       tensor' M0 N0...
       decide3' (makeRRuleBin AND Fo1 Go1)...
       tensor' (@nil oo) (Delta1 ++ Delta2)...
       tensor' Delta1 Delta2...

  + (* Disjunction left *)
    exists BTwoPA...
    intros n HSeq HIs...
    InvTriAll...
    ++ exists N. 
       exists [atom (down' Fo1)].
       exists [atom (down' Go1)].
       exists (@nil oo). exists (@nil oo).
       eexists. exists 4...
       left...
       decide3' (makeLRuleBin OR Fo1 Go1)...
       tensor' [ (atom (down (t_bin OR Fo1 Go1)))] Delta12.
    ++ exists N. 
       exists [atom (down' Fo1)].
       exists [atom (down' Go1)].
       exists (@nil oo). exists (@nil oo).
       eexists. exists 4...
       right...
       decide3' (makeLRuleBin OR Fo1 Go1)...
       tensor' (@nil oo) Delta12.
       
  + (* Disjunction right *)
    exists BOneP...
    intros n HSeq HIs...
    InvTriAll.

    exists  [atom (up' Fo1)]. exists (@nil oo).
    eexists. exists 4...
    rewrite H1.
    left.
    exists N...
    apply tri_plus1'...
    decide3'  (perp (up (t_bin OR Fo1 Go1)) ** (atom (up Fo1) op atom (up Go1))).
    tensor' [ (atom (up (t_bin OR Fo1 Go1)))] Delta1.

    exists  [atom (up' Fo1)]. exists (@nil oo).
    eexists. exists 4...
    rewrite H1.
    right...
    apply tri_plus1'...
    decide3'  (perp (up (t_bin OR Fo1 Go1)) ** (atom (up Fo1) op atom (up Go1))).
    tensor' (@nil oo) Delta1.

    exists  [atom (up' Go1)]. exists (@nil oo).
    eexists. exists 4...
    rewrite H1.
    left.
    exists N...
    apply tri_plus2'...
    decide3'  (perp (up (t_bin OR Fo1 Go1)) ** (atom (up Fo1) op atom (up Go1))).
    tensor' [ (atom (up (t_bin OR Fo1 Go1)))] Delta1.

    exists  [atom (up' Go1)]. exists (@nil oo).
    eexists. exists 4...
    rewrite H1.
    right...
    apply tri_plus2'...
    decide3'  (perp (up (t_bin OR Fo1 Go1)) ** (atom (up Fo1) op atom (up Go1))).
    tensor' (@nil oo) Delta1.

  + (* implication left *)
    exists BTwoPM...
     intros n HSeq HIs...
     InvTriAll...
     ++ exists M0.  exists N0.
        exists [atom (up' Fo1)].
        exists [atom (down' Go1)].
        exists (@nil oo). exists (@nil oo).
        eexists. exists 4...
        rewrite H1.
        left...
        tensor' M0 N0...
        decide3' (makeLRuleBin IMPL Fo1 Go1)...
        tensor' [(atom (down (t_bin IMPL Fo1 Go1)))] (Delta1 ++ Delta2)...
        tensor' Delta1 Delta2...

     ++ exists M0.  exists N0.
        exists [atom (up' Fo1)].
        exists [atom (down' Go1)].
        exists (@nil oo). exists (@nil oo).
        eexists. exists 4...
        rewrite H1.
        right...
        tensor' M0 N0...
        decide3' (makeLRuleBin IMPL Fo1 Go1)...
        tensor' (@nil oo) (Delta1 ++ Delta2)...
        tensor' Delta1 Delta2...

  + (* implication right *)
    exists BOneP...
    intros n HSeq HIs...
    InvTriAll.
    
    ++ exists ([atom (down' Fo1)] ++ [atom (up' Go1)]).
       exists (@nil oo).
       eexists. exists 5...
       left.  exists N...
       decide3' (makeRRuleBin IMPL Fo1 Go1)...
       tensor' [(atom (up (t_bin IMPL Fo1 Go1)))] Delta1... 
    ++  exists ([atom (down' Fo1)] ++ [atom (up' Go1)]).
        exists (@nil oo).
        eexists. exists 5...
        rewrite H1.
        right...
        decide3' (makeRRuleBin IMPL Fo1 Go1).
        tensor' (@nil oo) Delta1...
Qed.



(** *** Quantifiers *)
Lemma wellFormedQuantifier_p : wellFormedQuantifier.
Proof with solveF.
  unfold wellFormedQuantifier. intros.
  destruct lab.
Qed.

Lemma wellFormedTheory_p : wellFormedTheory.
  split.
  apply wellFormedConstant_p.
  split.
  apply wellFormedUnary_p.
  split; [apply wellFormedBinary_p | apply wellFormedQuantifier_p].
Qed.

(** ** Cut-coherency properties *)

(** *** Binary Connectives *)
Lemma CutCoherenceAND: CutCoherenceBin (rulesBC AND).
Proof with solveF.
  unfold CutCoherenceBin;intros.
  simpl.
  solveLL'.
  decide3' ((atom (up F) ) ** (atom (down F) )). econstructor;eauto using le_max_l.
  tensor' [perp (up F) ] [ perp (up G) ; (perp (down F) ) ** perp (down G) ];solveLL'.
  decide3' ((atom (up G) ) ** atom (down G) ). econstructor;eauto using le_max_r.
  solveLL'.
  tensor' [perp (up G)  ][ (perp (down F) ) ** perp (down G) ; atom (down F) ];solveLL'.
  decide1' ((perp (down F) ) ** perp (down G) ).
  tensor' [atom (down F) ] [atom (down G) ].
Qed.

Lemma CutCoherenceOR: CutCoherenceBin (rulesBC OR).
Proof with solveF.
  unfold CutCoherenceBin;intros.
  simpl.
  solveLL'.
  decide3' ((atom (up F) ) ** (atom (down F) )). econstructor;eauto using le_max_l.
  tensor' [perp (up F) ] [  perp (down F) op perp (down G)];solveLL'.
  decide1' (perp (down F) op perp (down G)) .

  decide3' ((atom (up G) ) ** (atom (down G) )). econstructor;eauto using le_max_r.
  tensor' [perp (up G) ] [  perp (down F) op perp (down G)];solveLL'.
  decide1' (perp (down F) op perp (down G)) .
Qed.

Lemma CutCoherenceIMPL: CutCoherenceBin (rulesBC IMPL).
Proof with solveF.
  unfold CutCoherenceBin;intros.
  simpl.
  solveLL'.
  decide3' ((atom (up F) ) ** (atom (down F) )). econstructor;eauto using le_max_l.
  tensor' [perp (up F)]  [perp (down F) ** perp (up G); perp (down G)];solveLL'. 
  decide3' ((atom (up G) ) ** (atom (down G) )). econstructor;eauto using le_max_r.
  tensor' [perp (down F) ** perp (up G); atom (down F)] [perp (down G)];solveLL'.
  decide1' (perp (down F) ** perp (up G)) .
  tensor' [atom (down F) ][ atom (up G)] . 
Qed.


Lemma CutCoherence_p : CutCoherence .
  split;intros; try destruct lab.
  split;intros; try destruct lab.
  split;intros; try destruct lab;
    auto using CutCoherenceAND, CutCoherenceOR, CutCoherenceIMPL .
Qed.

(** The theory is well formed: cut-coherence holds and all the rules
are bipoles *)
Lemma wellTheory_p : wellTheory.
  split;auto using CutCoherence_p,  wellFormedTheory_p.
Qed.

Hint Unfold  OLTheoryIsFormula ConstantsFormulas UConnectivesFormulas ConnectivesFormulas QuantifiersFormulas : core .
Hint Unfold  OLTheoryIsFormulaD ConstantsFormulasD UConnectivesFormulasD ConnectivesFormulasD QuantifiersFormulasD :core.

Theorem  OLTheoryIsFormula_p :  OLTheoryIsFormula.
Proof with SolveIsFormulas.
  split;autounfold...
  intro;destruct lab...
Qed.

Theorem  OLTheoryIsFormulaD_p :  OLTheoryIsFormulaD.
Proof with SolveIsFormulas.
  split;autounfold...
  intro;destruct lab...
Qed.
  
(** The cut-elimination theorem instantiated for LK *)
Check OLCutElimination wellTheory_p OLTheoryIsFormula_p OLTheoryIsFormulaD_p.
