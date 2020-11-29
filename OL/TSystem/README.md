# An example of transition system
This directory contains the formalization of a transition system modeling a
cell's life cycle. The model was originally proposed in 

Joëlle Despeyroux, Amy Felty, Pietro Lio and Carlos Olarte: _A Logical
Framework for Modelling Breast Cancer Progression_


## Syntax.v

This file defines some constants used in the model and the following atomic
predicates:

- _T(t)_: denoting the current time-unit
- _C(n,c,f,lm)_: denoting a cell _n_, in a compartment _c_ (breast, blood, or
  bone), with a phenotype given by a fitness degree (a number in the interval 0
  .. 12) and a list of driver mutations _lm_
- _A(n)_: representing the fact that the cell n has gone to apoptosis

The usual well-formed conditions are also proved here. 

## Rules.v

The rules of the system consume and produce the atomic propositions above.
There are 171 rules that modify the state of the cell according to the driven
mutations it posses. 

## Properties.v

Here we specify some properties that can be proved using the tactics of the FLL
system. 
