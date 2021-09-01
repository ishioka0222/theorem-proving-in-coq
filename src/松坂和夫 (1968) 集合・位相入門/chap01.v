From mathcomp
  Require Import ssreflect.
Require Import Coq.Sets.Ensembles.

Lemma Formula_1_4 (T : Type) (A B C : Ensemble T) : Included T A B /\ Included T B C -> Included T A C.
Proof.
  case.
  move=> HAinclB HBinclC x HxinA.
  apply (HBinclC x).
  apply (HAinclB x).
  by [].
Qed.

Lemma Formula_1_5 (T : Type) (A : Ensemble T) : Included T (Empty_set T) A.
Proof.
  move=> x HxinEmptySet.
  by [].
Qed.

Lemma Formula_2_2_1 (T : Type) (A B : Ensemble T) : Included T A (Union T A B).
Proof.
  move=> x HxinA.
  left.
  by [].
Qed.

Lemma Formula_2_2_2 (T : Type) (A B : Ensemble T) : Included T B (Union T A B).
Proof.
  move=> x HxinB.
  right.
  by [].
Qed.

Lemma Formula_2_3 (T : Type) (A B C : Ensemble T) : Included T A C /\ Included T B C -> Included T (Union T A B) C.
Proof.
  case.
  move=> HAinclC HBinclC x [y | z].
  + apply HAinclC.
  + apply HBinclC.
Qed.

Lemma Formula_2_4 (T : Type) (A : Ensemble T) : (Union T A A) = A.
Proof.
  apply Extensionality_Ensembles.
  apply conj.
  + move=> x.
    case.
    + move=> y.
      by [].
    + move=> y.
      by [].
  + apply (Formula_2_2_1 T A A).
Qed.

Lemma Formula_2_5 (T : Type) (A B : Ensemble T) : (Union T A B) = (Union T B A).
Proof.
  apply Extensionality_Ensembles.
  apply conj.
  + move=> x.
    case.
    + move=> y HyinA.
      right.
      by [].
    + move=> y HyinB.
      left.
      by [].
  + move=>x.
    case.
    + move=> y HyinB.
      right.
      by [].
    + move=> y HyinA.
      left.
      by [].
Qed.

Lemma Formula_2_6 (T : Type) (A B C : Ensemble T) : (Union T (Union T A B) C) = (Union T A (Union T B C)).
Proof.
  apply Extensionality_Ensembles.
  apply conj.
  + move=> x [ab | c].
    + move=> [a | b].
      + left.
        by [].
      + right.
        left.
        by [].
    + move=> HcinC.
      right.
      right.
      by [].
  + move=> x [a | bc].
    + move=> HainA.
      left.
      left.
      by [].
    + move=> [b | c].
      + left.
        right.
        by [].
      + right.
        by [].
Qed.

Lemma Formula_2_7 (T : Type) (A B : Ensemble T) : Included T A B <-> (Union T A B) = B.
Proof.
  apply conj.
  + move=> HAinclB.
    apply Extensionality_Ensembles.
    apply conj.
    + move=> x.
      case.
      + move=> y HyinA.
        apply HAinclB.
        by [].
      + move=> y HyinB.
        by [].
    + move=> x HxinB.
      right.
      by [].
  + move=> Heq.
    rewrite -Heq.
    apply Formula_2_2_1.
Qed.

Lemma Formula_2_8 (T : Type) (A B C : Ensemble T) : Included T A B -> Included T (Union T A C) (Union T B C).
Proof.
  move=> HAinclB x.
  case.
  + move=> y HyinA.
    left.
    apply HAinclB.
    by [].
  + move=> y HyinC.
    right.
    by [].
Qed.

Lemma Formula_2_9 (T : Type) (A : Ensemble T) : (Union T (Empty_set T) A) = A.
Proof.
  apply Formula_2_7.
  apply Formula_1_5.
Qed.

Lemma Formula_2_2'_1 (T : Type) (A B : Ensemble T) : Included T (Intersection T A B) A.
Proof.
  move=> x [y HyinA HyinB].
  by [].
Qed.

Lemma Formula_2_2'_2 (T : Type) (A B : Ensemble T) : Included T (Intersection T A B) B.
Proof.
  move=> x [y HyinA HyinB].
  by [].
Qed.
