From mathcomp
  Require Import ssreflect.
Require Import Coq.Sets.Ensembles.

Lemma Formula_1_4 (T : Type) (A B C : Ensemble T) : Included T A B /\ Included T B C -> Included T A C.
Proof.
  case.
  move=> HAinclB HBinclC x HxinA.
  apply: (HBinclC x).
  apply: (HAinclB x).
  by [].
Qed.

Lemma Formula_1_5 (T : Type) (A : Ensemble T) : Included T (Empty_set T) A.
Proof.
  move=> x HxinEmptySet.
  by [].
Qed.
