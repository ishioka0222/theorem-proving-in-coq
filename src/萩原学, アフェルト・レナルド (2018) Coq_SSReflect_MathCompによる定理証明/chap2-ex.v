From mathcomp
  Require Import ssreflect ssrnat.

Hypothesis ExMidLaw : forall P : Prop, P \/ ~P.

Lemma notnotEq (P : Prop) : ~ ~ P -> P.
Proof.
  move=> HnotnotP.
  - case: (ExMidLaw (~ P)).
    + by move /HnotnotP.
    + by case: (ExMidLaw P).
Qed.

(* 問2.2 *)
Lemma ex2_2 : forall A B C : Prop, (A -> B) /\ (B -> C) -> (A -> C).
Proof.
  move=> A B C; case.
  move=> Hyp1 Hyp2 Hyp3.
  by apply: (Hyp2 (Hyp1 Hyp3)).
Qed.

(* 問2.7 *)
Lemma ex2_7 (A B : Prop) : ~(A /\ B) <-> (~A) \/ (~B).
Proof.
  apply: conj.
  + move=> HnotAandB.
    case: (ExMidLaw ((~A) \/ (~B))).
    + by [].
    + case: (ExMidLaw A).
      + move=> HA HnotnotAornotB.
        case: (ExMidLaw B).
        + move=> HB.
          case: HnotAandB.
          apply: conj.
          by [].
          by [].
        + move=> HnotB.
          right.
          by [].
      + move=> HnotA HnotnotAornotB.
        left.
        by [].
  + move=> HnotAornotB HAandB.
    case: HnotAornotB.
    + case: HAandB.
      by [].
    + case: HAandB.
      by [].
Qed.

(* 問2.8 *)
Lemma ex2_8 (T : Type) (P : T -> Prop) : ~(forall x : T, P x) <-> (exists x : T, ~P x).
Proof.
  apply: conj.
  + move=> HnotforallPx.
    apply: notnotEq.
    move=> HnotexistsnotPx.
    apply: HnotforallPx.
    move=> x.
    apply: notnotEq.
    move=> HnotforallPx.
    apply HnotexistsnotPx.
    exists x.
    by [].
  + case.
    move=> x HnotPx HnotforallPx.
    apply: HnotPx.
    move: x.
    by [].
Qed.
