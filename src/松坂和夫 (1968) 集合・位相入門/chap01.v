From mathcomp
  Require Import ssreflect.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Powerset.

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
  + move=> x HxinAcupA.
    destruct HxinAcupA as [x HxinA | x HxinA].
    + by [].
    + by [].
  + apply (Formula_2_2_1 T A A).
Qed.

Lemma Formula_2_5 (T : Type) (A B : Ensemble T) : (Union T A B) = (Union T B A).
Proof.
  apply Extensionality_Ensembles.
  apply conj.
  + move=> x HxinAcupB.
    destruct HxinAcupB as [x HxinA | x HxinB].
    + right.
      by [].
    + left.
      by [].
  + move=>x HxinBcupA.
    destruct HxinBcupA as [x HxinB | x HxinA].
    + right.
      by [].
    + left.
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
    + move=> x HxinAcupB.
      destruct HxinAcupB as [x HxinA| x HxinB].
      + apply HAinclB.
        by [].
      + by [].
    + move=> x HxinB.
      right.
      by [].
  + move=> Heq.
    rewrite -Heq.
    apply Formula_2_2_1.
Qed.

Lemma Formula_2_8 (T : Type) (A B C : Ensemble T) : Included T A B -> Included T (Union T A C) (Union T B C).
Proof.
  move=> HAinclB x HxinAcupC.
  destruct HxinAcupC as [x HxinA | x HxinC].
  + left.
    apply HAinclB.
    by [].
  + right.
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

Lemma Formula_2_3' (T : Type) (A B C : Ensemble T) : Included T C A /\ Included T C B -> Included T C (Intersection T A B).
Proof.
  move=> [HCinclA HCinclB] x HxinC.
  apply Intersection_intro.
  + apply HCinclA.
    by [].
  + apply HCinclB.
    by [].
Qed.

Lemma Formula_2_4' (T : Type) (A : Ensemble T) : (Intersection T A A) = A.
Proof.
  apply Extensionality_Ensembles.
  apply conj.
  + apply (Formula_2_2'_1 T A A).
  + move=> x HxinA.
    apply Intersection_intro.
    + by [].
    + by [].
Qed.

Lemma Formula_2_5' (T : Type) (A B : Ensemble T) : (Intersection T A B) = (Intersection T B A).
Proof.
  apply Extensionality_Ensembles.
  apply conj.
  + move=> x HxinAcapB.
    destruct HxinAcapB as [x HinA HinB].
    apply Intersection_intro.
    + by [].
    + by [].
  + move=> x HxinBcapA.
    destruct HxinBcapA as [x HinB HinA].
    apply Intersection_intro.
    + by [].
    + by [].
Qed.

Lemma Formula_2_6' (T : Type) (A B C : Ensemble T) : (Intersection T (Intersection T A B) C) = (Intersection T A (Intersection T B C)).
Proof.
  apply Extensionality_Ensembles.
  apply conj.
  + move=> x HxinAcapBcapC.
    destruct HxinAcapBcapC as [x HxinAcapB HxinC].
    destruct HxinAcapB as [x HxinA HxinB].
    apply Intersection_intro.
    + by [].
    + apply Intersection_intro.
      + by [].
      + by [].
  + move=> x HxinAcapBcapC.
    destruct HxinAcapBcapC as [x HxinA HxinBcapC].
    destruct HxinBcapC as [x HxinB HxinC].
    apply Intersection_intro.
    + apply Intersection_intro.
      + by [].
      + by [].
    + by [].
Qed.

Lemma Formula_2_7' (T : Type) (A B : Ensemble T) : Included T A B <-> (Intersection T A B) = A.
Proof.
  apply conj.
  + move=> HAinclB.
    apply Extensionality_Ensembles.
    apply conj.
    + move=> x HxinAcapB.
      destruct HxinAcapB as [x HxinA HxinB].
      by [].
    + move=> x HxinAcapB.
      apply Intersection_intro.
      + by [].
      + apply HAinclB.
        by [].
  + move=> Heq.
    rewrite -Heq.
    apply (Formula_2_2'_2 T A B).
Qed.

Lemma Formula_2_8' (T : Type) (A B C : Ensemble T) : Included T A B -> Included T (Intersection T A C) (Intersection T B C).
Proof.
  move=> HAinclB x HxinAcapB.
  destruct HxinAcapB as [x HxinA HxinC].
  apply Intersection_intro.
  + apply HAinclB.
    by [].
  + by [].
Qed.

Lemma Formula_2_9' (T : Type) (A : Ensemble T) : Intersection T (Empty_set T) A = (Empty_set T).
Proof.
  apply Extensionality_Ensembles.
  apply conj.
  + move=> x Hxin.
    destruct Hxin as [x HxinEmp HxinA].
    by [].
  + move=> x Hxin.
    by [].
Qed.

Lemma Formula_2_10 (T : Type) (A B C : Ensemble T) : Intersection T (Union T A B) C = Union T (Intersection T A C) (Intersection T B C).
Proof.
  apply Extensionality_Ensembles.
  apply conj.
  + move=> x HxinCap.
    destruct HxinCap as [x HxinCup HxinC].
    destruct HxinCup as [x HxinA | HxinB].
    + left.
      by apply Intersection_intro.
    + right.
      by apply Intersection_intro.
  + move=> x HxinCup.
    destruct HxinCup as [x HxinAcapC | x HxinBcapC].
    + destruct HxinAcapC as [x HxinA HxinC].
      apply Intersection_intro.
      + by left.
      + by [].
    + destruct HxinBcapC as [x HxinB HxinC].
      apply Intersection_intro.
      + by right.
      + by [].
Qed.

Lemma Formula_2_10' (T : Type) (A B C : Ensemble T) : Union T (Intersection T A B) C = Intersection T (Union T A C) (Union T B C).
Proof.
  apply Extensionality_Ensembles.
  apply conj.
  + move=> x HxinCup.
    destruct HxinCup as [x HxinCap | x HxinC].
    + destruct HxinCap as [x HxinA HxinB].
      by apply Intersection_intro; left.
    + by split; right.
  + move=> x HxinCap.
    destruct HxinCap as [x HxinAcupC HxinBcupC].
    destruct HxinAcupC as [x HxinA | x HxinC].
    + destruct HxinBcupC as [x HxinB | x HxinC].
      + by left; split.
      + by right.
    + destruct HxinBcupC as [x HxinB | x HxinC'].
      + by right.
      + by right.
Qed.

Lemma Formula_2_11 (T : Type) (A B : Ensemble T) : Intersection T (Union T A B) A = A.
Proof.
  apply Extensionality_Ensembles.
  split.
  + move=> x HxinAcupB.
    destruct HxinAcupB as [x HxinAcupB HxinA].
    by [].
  + move=> x HxinA.
    split.
    + by left.
    + by [].
Qed.

Lemma Formula_2_11' (T : Type) (A B : Ensemble T) : Union T (Intersection T A B) A = A.
Proof.
  apply Extensionality_Ensembles.
  split.
  + move=> x HxinCup.
    destruct HxinCup as [x HxinAcapB | x HxinA].
    + by destruct HxinAcapB as [x HxinA HxinB].
    + by [].
  + move=> x HxinA.
    by right.
Qed.

Lemma Formula_2_12_1 (T : Type) (A : Ensemble T) : Union T A (Complement T A) = Full_set T.
Proof.
  apply Extensionality_Ensembles.
  split.
  + by [].
  + move=> x _.
    by case: (classic (In T A x)); [left | right].
Qed.

Lemma Formula_2_12_2 (T : Type) (A : Ensemble T) : Intersection T A (Complement T A) = Empty_set T.
Proof.
  apply Extensionality_Ensembles.
  split.
  + move=> x HxinAcapAc.
    destruct HxinAcapAc as [x HxinA HxinAc].
    by [].
  + by [].
Qed.

Lemma Formula_2_13 (T : Type) (A : Ensemble T) : Complement T (Complement T A) = A.
Proof.
  apply Extensionality_Ensembles.
  split.
  + move=> x HxinAcc.
    apply NNPP.
    by [].
  + move=> x HxinA HxinAc.
    apply (HxinAc HxinA).
Qed.

Lemma Formula_2_14_1 (T : Type) : Complement T (Empty_set T) = Full_set T.
Proof.
  apply Extensionality_Ensembles.
  split.
  + move=> x Hx.
    by [].
  + move=> x H1 H2.
    by [].
Qed.

Lemma Formula_2_14_2 (T : Type) : Complement T (Full_set T) = Empty_set T.
Proof.
  apply Extensionality_Ensembles.
  split.
  + move=> x H.
    by case H.
  + move=> x H.
    by [].
Qed.

Lemma Formula_2_15 (T : Type) (A B : Ensemble T) : Included T A B <-> Included T (Complement T B) (Complement T A).
Proof.
  split.
  + move=> HAinclB x HxinBc HxinA.
    apply HxinBc.
    apply HAinclB.
    by [].
  + move=> HBcinclAc x HxinA.
    apply NNPP.
    move=> HxnotinB.
    apply (HBcinclAc x HxnotinB).
    by [].
Qed.

Lemma Formula_2_16 (T : Type) (A B : Ensemble T) : Complement T (Union T A B) = Intersection T (Complement T A) (Complement T B).
Proof.
  apply Extensionality_Ensembles.
  split.
  + move=> x HxinAcupBc.
    split.
    + move=> HxinA.
      apply HxinAcupBc.
      left.
      by [].
    + move=> HxinB.
      apply HxinAcupBc.
      right.
      by [].
  + move=> x HxinAccapBc HxinAcupB.
    destruct HxinAccapBc as [x HxinAc HxinBc].
    destruct HxinAcupB as [x HxinA | x HxinB].
    + apply HxinAc.
      by [].
    + apply HxinBc.
      by [].
Qed.

Lemma Formula_2_16' (T : Type) (A B : Ensemble T) : Complement T (Intersection T A B) = Union T (Complement T A) (Complement T B).
Proof.
  apply Extensionality_Ensembles.
  split.
  + move=> x HxinAcapBc.
    case (classic (In T A x)).
    + move=> HxinA.
      right.
      move=> HxinB.
      apply HxinAcapBc.
      by split.
    + move=> HxnotinA.
      by left.
  + move=> x HxinAccupBc HxinAcapB.
    destruct HxinAcapB as [x HxinA HxinB].
    by destruct HxinAccupBc as [x HxinAc | x HxinBc].
Qed.

Lemma Formula_p18_l10 (T : Type) : (Full_set T) = (Empty_set T) -> (Power_set T (Full_set T)) = (Singleton (Ensemble T) (Empty_set T)).
Proof.
  move=> HFullEqEmpty.
  apply Extensionality_Ensembles.
  apply conj.
  + move=> X HXinPFull.
    have: (X = Empty_set T).
    + apply Extensionality_Ensembles.
      split.
      + rewrite -HFullEqEmpty.
        by [].
      + by [].
    + move=> HXeqEmpty.
      rewrite HXeqEmpty.
      by [].
  + move=> X HX.
    apply Definition_of_Power_set.
    move=> x HxinX.
    apply Full_intro.
Qed.
