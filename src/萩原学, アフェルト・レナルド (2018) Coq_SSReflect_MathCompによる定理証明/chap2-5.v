From mathcomp
  Require Import ssreflect ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Logic.

Lemma contrap : forall A B : Prop, (A -> B) -> (~B -> ~A).
Proof.
rewrite /not.
move => A0 B0 AtoB notB.
by move /AtoB.
Qed.

Variables A B C : Prop.

Lemma AndOrDistL : (A /\ C) \/ (B /\ C) <-> (A \/ B) /\ C.
Proof.
rewrite /iff.
apply: conj.
-case.
 +case=> AisTrue CisTrue.
  by apply: conj; [apply: or_introl | ].
 +case=> BisTrue CisTrue.
  by apply: conj; [apply: or_intror | ].
-case=> AorBisTrue CisTrue.
 case: AorBisTrue => [AisTrue | BisTrue].
 +by apply: or_introl.
 +by apply: or_intror.
Qed.

Lemma JDM (T : Type) (P : T -> Prop) :
  ~(exists (x : T), P x) <-> forall x, ~(P x).
Proof.
apply: conj => Hyp.
-move=> x0 HPx0.
 apply: Hyp.
 by apply: (ex_intro P x0).
-by case.
Qed.

Hypothesis ExMidLaw : forall P : Prop, P \/ ~P.

Lemma notnotEq (P : Prop) : ~ ~ P -> P.
Proof.
move=> HnotnotP.
-case: (ExMidLaw (~ P)).
 +by move /HnotnotP.
 +by case: (ExMidLaw P).
Qed.

End Logic.
