(** * System LJ for propositional intuitionistic logic encoded as an LL theory

This file encodes the inference rules of the system LJ . The cut-coherence and well-formedness properties are
proved and then, using [OLCutElimination] we prove the cut-elimination
theorem for this system .
 *)

Require Export FLL.OL.OLCutPOS.
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
(* Although negation is not needed we keep it for illustrative purposes *) 
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
  | AND => PLUSWITH
  | OR =>  WITHPLUS
  | IMP => TENSORPAR
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

(** The cut-elimination theorem instantiated for LK *)
Check CutElimination.

(** Soundness and Completeness *)

Inductive LJSeq : list uexp -> uexp -> Prop :=
| LJTRUE : forall L, LJSeq L (t_cons TT)
| LJFALSE : forall L G, LJSeq (t_cons FF :: L) G
| LJinit : forall L F,  LJSeq (F:: L) F
| LJAndL1 : forall L F G R, LJSeq (F :: L) R -> LJSeq ( (t_bin AND F G) :: L) R
| LJAndL2 : forall L F G R, LJSeq (G :: L) R -> LJSeq ( (t_bin AND F G) :: L) R
| LJAndR : forall L F G , LJSeq L F -> LJSeq L G -> LJSeq L (t_bin AND F G)
| LJImpL : forall L A B G , LJSeq L A -> LJSeq (B:: L) G -> LJSeq (t_bin IMP A B ::L) G
| LJImpR : forall L A B  , LJSeq (A:: L) B ->  LJSeq L (t_bin IMP A B)
| LJAllL : forall L t FX G, uniform FX -> proper t -> LJSeq( FX t :: L) G -> LJSeq (t_quant ALL FX :: L) G
| LJAllR : forall L FX , uniform FX -> (forall x, proper x -> LJSeq L (FX x)) -> LJSeq L (t_quant ALL FX)
| LJEXL : forall L FX G, uniform FX -> (forall x, proper x -> LJSeq (FX x:: L) G) -> LJSeq (t_quant SOME FX :: L) G
| LJEXR : forall L FX t, uniform FX -> proper t -> LJSeq L (FX t)-> LJSeq L (t_quant SOME FX)
| (* contraction is needed *)
LJContr : forall L F G, (LJSeq (F :: F:: L)) G -> (LJSeq (F :: L)) G
| (* Explicit exchange *)
LJEx : forall L L' G, Permutation L L' -> LJSeq L G -> LJSeq L' G 
.
Hint Constructors LJSeq : core .

Definition LEncode L := map (fun x => d| x|) L.
Definition REncode F := u| F|.


Hint Constructors OLTheory buildTheory : core.
Hint Constructors isOLFormula : core. 
Theorem Soundeness: forall L F, LJSeq L F ->
                                isOLFormulaL L ->
                                isOLFormula F ->
                                seq OLTheory (LEncode L) [ REncode F] (> []).
Proof with solveF;solveLL'.
    intros.
    induction H.
    + (* True on the right *)
      decide3' (makeRuleConstant TT Right).
      do 2 constructor...
      tensor' [REncode (t_cons TT)] (@nil oo).
    + (* false on the left *)
      decide3' (makeRuleConstant FF Left).
      do 4 constructor.
      tensor' (@nil oo) [REncode G]...
      
    + (* init *)
      decide3' (RINIT F)...
      tensor' [REncode F] (@nil oo)...
      
    + (* ANDL1 *)
      simpl.
      decide3' (makeRuleBin AND Left F G)...
      constructor... (*!! avoid this kind of things*)
      constructor...
      inversion H0...
      assert(isOLFormulaL (F :: L) ).
      { inversion H0...
        inversion H4...
        inversion H2... (* this is inconsistent *)
        constructor...
      }
      apply IHLJSeq in H2...
      
      tensor' (@nil oo) [REncode R]...
      oplus1'.
      LLPerm (d| F | :: d| t_bin AND F G | :: LEncode L ) .
      inversion H0...
      LLPerm ( d| t_bin AND F G | :: d| F |  :: LEncode L).
      apply weakening.
      simpl in IHLJSeq ...
    +  (* ANDL2 *)
      admit.
    + (* And R *)
      inversion H1...
      inversion H3.
      apply  IHLJSeq1 in H0 as IH1...
      apply  IHLJSeq2 in H0 as IH2...
      decide3' (makeRuleBin AND Right F G)...
      do 2 constructor...
      tensor' [REncode (t_bin AND F G)] (@nil oo).
    + (* implication left *)
      admit.
    + (* implication right *)
      admit.
    + (* forall left *)
      inversion H0...
      inversion H6...
      inversion H4... (* inconsistent *)
      apply lbindEq in H5...
      specialize(H9 t H2).
      assert(seq OLTheory (LEncode (FX t :: L)) [REncode G] (> [])).
      apply IHLJSeq...
      rewrite <- H5...
      constructor...
      decide3' (makeRuleQ ALL Left FX)...
      do 2 constructor...
      tensor' (@nil oo) [REncode G]...
      existential' t...
      apply weakening.
      LLPerm(d| FX t |:: LEncode L )...
    + (* forall right *)
      inversion H1...
      inversion H4...
      apply lbindEq in H5...
      decide3' (makeRuleQ ALL Right FX)...
      do 2 constructor...
      tensor' ([REncode (t_quant ALL FX)]) (@nil oo).
      specialize(H3 x properX).
      apply H3 in H0 as H3'...
      rewrite <- H5...
    + (* existst left *)
      admit.
    + (* exists right *)
      admit.
    + (* contraction *)
      (* by contraction on LL*)
      admit.
    + (* exchange *)
      (* by exchange in LL *)
      admit.
Admitted.
  
  Theorem Completeness: forall n L F , 
                                    isOLFormulaL L ->
                                    isOLFormula F ->
                                    seqN OLTheory n (LEncode L) [ REncode F] (> []) ->
                                    LJSeq L F .
    Proof with solveF;solveLL'.
      induction n using strongind;intros.
      inversion H1.

      inversion H2...
      unfold REncode in H4... (* cannot focus on atoms *)
      admit. (* H5 is inconsistent since F0 must be an atom *)
      
      
      inversion H4...
      + (* from the theory *)
        inversion H3...
        ++ (* Constant right *)
          apply FocusingRightCte in H6. (* the second goal should be automatic *)
          CleanContext.
          (* by cases on C *)
          destruct C;simpl in H8...
          inversion H8... (* there is no proof o zero *)

          admit. (* this should be ok *)
        ++  (* constant left *)
          admit.
        ++ (* binary connective right *)
          apply FocusingRightRule in H6. (* the second goal should be automatic *)
          CleanContext.
          (* by cases on C *)
          destruct C;simpl in H8...
          { (* case AND *)
            apply AppPLUSWITHRight in H8.
            CleanContext.
            apply H in H6...
            apply H in H8...
            (* this part should be automatic *)
            inversion H7...
            inversion H5... (* inconsistent *)
            inversion H7...
            inversion H5... (* inconsistent *)
          }
          { (*  OR *)
            admit.
          }
          { (* impl *)
            admit.
          }
          admit. (* this one should be automatic *) 
          
        ++  (* binary connective left *)
          admit.
        ++ (* Quantifier right *)
          apply FocusingRightQ in H6... (* the second goal should be automatic *)
          CleanContext.
          (* by cases on C*)
          destruct C;simpl in H9...
          { (* case ALL *)
            inversion H9...
            inversion H13...
            apply LJAllR...
            intros.
            specialize(H16 x H5).
            inversion H16...
            apply H in H19...
            (* This part should be automatic *)
            inversion H8...
            inversion H10... (* inconsistent *)
            apply lbindEq in H11...
            rewrite <- H11...
          }
          { (* case SOME *)
            inversion H9...
            inversion H14...
            inversion H13...
            apply LJEXR with (t:=t)...
            apply H in H18...
            (* This part should be automatic *)
            inversion H8...
            inversion H5... (* inconsistent *)
            apply lbindEq in H11...
            rewrite <- H11...
          }
          

          admit. (* this should be automatic *)
          
        ++ (* Quantifier left *)
          admit.
      + (* init *)
        apply Init_inversion1 in H6...
        admit. (* from h6 *)
        admit. (* this should be automatic *)
    Admitted.
    
