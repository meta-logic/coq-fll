# Cut-coherence conditions

In this directory we show how to encode different inference systems as LL
theories. Then, using the results in [1], we show that cut-coherent systems
satisfy the cut-elimination property. Moreover, we prove that the inference
rules of Hybrid Linear Logic (HyLL) can be adequately encoded as an LL theory
[2] at the highest level of adequacy. 

## Cut-coherence conditions 

Roughly, Cut-coherence [1] means that the left and right rules for a connective
are self-dual. More precisely, if BL and BR are the LL formulas defining the
bodies of the rules, then [BL ^ ; BR ^] is provable in LL. This fact is used to
prove cut-elimination of the encoded system. All the principal cases are
uniformly proved by using the cut rule at the meta-level (i.e., the LL's
cut-rule). 

#### OLSyntax 

General definitions to encode the syntax of the OL, encoding constants/units,
connectives and quantifiers.


#### OLDefinitions

Useful definitions and tactics for the proof of the cut-elimination theorem of
Object Logics.

#### OLCutl

In this file we show how the cut-elimination procedure for FLL can be used to
prove cut-elimination for object logics that are cut-coherent in the sense [1].
This procedure applies for substructural logics (where weakening and
contraction do not apply). 

The file MALL shows that Multiplicative Additive Linear Logic is an instance of
this definitions, thus obtaining the cut-elimination theorem for it. 

#### OLCuti

The file OLCuti proves the  cut-coherence theorem for logics featuring
structural rules only on the left side of the sequent. As an example, two
versions of first-order intuitionistic logics are shown to fulfill the needed
conditions, thus obtaining cut-elimination theorems for them. See the files
LJ.v and LJm.v for more details.  In those files, we also prove that the
encodings presented are adequate at the level of derivations.

As a second example, the file LM.v presents the encoding of minimal
intuitionistic logic (and its adequacy is proved). The cut-elimination theorem
of OLCuti applies for it.  Moreover, in NDSeq we encode the logical rules of
natural deduction for minimal logic. We also prove the equivalences between
left (resp.  right) introduction rules in sequent calculus and elimination
(resp.  introduction) rules in Natural Deduction. Hence, using the
cut-elimination theorem of LL we prove the relative completeness of these
systems.

#### OLCutc

The file OLCutc proves the cut-coherence theorem for logics featuring
structural rules on both the right and left side of the sequents. As an
example, LK.v encodes the inference rules of first-order classical logic.  The
encoding is shown to be adequate and the result in OLCutc applies for it. 

#### HyLL

This file proves the result in [2]: the inference rules of HyLL can be
adequately encoded as an LL theory. 

#### HyLLCut

The encoding in [2] is not cut-coherent and then, we cannot use it to prove
cut-elimination of HyLL. In HyLLCut.v we propose a second encoding of HyLL
without units which is adequate only at the level of proofs. This encoding is
cut-coherent and we use such condition to establish cut-elimination of HyLL. 

## References
[1] _A formal framework for specifying sequent calculus proof systems_ by 	Dale Miller and Elaine Pimentel. Theor. Comput. Sci. 474: 98-116 (2013)

[2] _Hybrid linear logic, revisited_ by Kaustuv Chaudhuri, Joëlle Despeyroux, Carlos Olarte, Elaine Pimentel. Math. Struct. Comput. Sci. 29(8): 1151-1176 (2019)

