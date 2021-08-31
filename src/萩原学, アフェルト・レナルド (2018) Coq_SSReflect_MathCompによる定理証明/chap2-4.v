From mathcomp
  Require Import ssreflect ssrnat.

Section naturalNumber.

Lemma add0nEqn (n : nat) : 0 + n = n.
Proof. by []. Qed.

Lemma addn3Eq2n1 (n : nat) : n + 3 = 2 + n + 1.
Proof.
rewrite addn1.
rewrite add2n.
rewrite addnC.
by [].
Qed.

Fixpoint sum n := if n is m.+1 then sum m + n else 0.

Lemma sumGauss (n : nat) : sum n * 2 = (n + 1) * n.
Proof.
elim: n => [// | n IHn].
rewrite mulnC.
rewrite (_ : sum (n.+1) = n.+1 + (sum n)); last first.
rewrite /=.
by rewrite addnC.
rewrite mulnDr.
rewrite mulnC in IHn.
rewrite IHn.
rewrite 2!addn1.
rewrite [_ * n]mulnC.
rewrite -mulnDl.
by [].
Qed.

End naturalNumber.
