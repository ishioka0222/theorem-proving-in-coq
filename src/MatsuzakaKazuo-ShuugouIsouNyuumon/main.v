Require Import Coq.Sets.Ensembles.

Lemma Formula_1_4 : forall (T : Type) (A B C : Ensemble T), Included T A B /\ Included T B C -> Included T A C.
Proof.
  intros T A B C [H1 H2] t H3.
  apply (H2 t (H1 t H3)).
Qed.

Lemma Formula_1_5 : forall (T : Type) (A : Ensemble T), Included T (Empty_set T) A.
Proof.
  intros T A t.
  contradiction.
Qed.

Lemma Formula_2_2_1 : forall (T : Type) (A B : Ensemble T), Included T A (Union T A B).
Proof.
  intros T A B t H1.
  left.
  apply H1.
Qed.

Lemma Formula_2_2_2 : forall (T : Type) (A B : Ensemble T), Included T B (Union T A B).
Proof.
  intros T A B t H1.
  right.
  apply H1.
Qed.

Lemma Formula_2_3 : forall (T : Type) (A B C : Ensemble T), Included T A C /\ Included T B C -> Included T (Union T A B) C.
Proof.
  intros T A B C [H1 H2] t H3.
  case H3.
  apply H1.
  apply H2.
Qed.

Lemma Formula_2_4 : forall (T : Type) (A : Ensemble T), (Union T A A) = A.
Proof.
  intros T A.
  apply Extensionality_Ensembles.
  apply conj.
  intros t H.
  case H.
  intros t1 H1.
  assumption.
  intros t1 H1.
  assumption.
  apply (Formula_2_2_1 T A A).
Qed.

Lemma Formula_2_5 : forall (T : Type) (A B : Ensemble T), (Union T A B) = (Union T B A).
Proof.
  intros T.
  assert (forall (A B : Ensemble T), Included T (Union T A B) (Union T B A)) as H.
  intros A B t H1.
  case H1.
  apply (Formula_2_2_2 T B A).
  apply (Formula_2_2_1 T B A).
  intros A B.
  apply Extensionality_Ensembles.
  apply conj.
  apply (H A B).
  apply (H B A).
Qed.

Lemma Formula_2_6 : forall (T : Type) (A B C : Ensemble T), (Union T (Union T A B) C) = (Union T A (Union T B C)).
Proof.
  intros T A B C.
  apply Extensionality_Ensembles.
  apply conj.
  intros t H.
  case H.
  intros t1 H1.
  case H1.
  apply (Formula_2_2_1 T A (Union T B C)).
  intros t2 H2.
  apply (Formula_2_2_2 T A (Union T B C)).
  apply (Formula_2_2_1 T B C).
  assumption.
  intros t1 H1.
  apply (Formula_2_2_2 T A (Union T B C)).
  apply (Formula_2_2_2 T B C).
  assumption.
  intros t H.
  case H.
  intros t1 H1.
  apply (Formula_2_2_1 T (Union T A B) C).
  apply (Formula_2_2_1 T A B).
  assumption.
  intros t1 H1.
  case H1.
  intros t2 H2.
  apply (Formula_2_2_1 T (Union T A B) C).
  apply (Formula_2_2_2 T A B).
  assumption.
  intros t2 H2.
  apply (Formula_2_2_2 T (Union T A B) C).
  assumption.
Qed.

Lemma Formula_2_7 : forall (T : Type) (A B : Ensemble T), Included T A B <-> (Union T A B) = B.
Proof.
  intros T A B.
  apply conj.
  intro H1.
  apply Extensionality_Ensembles.
  apply conj.
  intros t H2.
  case H2.
  assumption.
  intros t1 H3.
  assumption.
  apply (Formula_2_2_2 T A B).
  intro H1.
  case H1.
  apply (Formula_2_2_1 T A B).
Qed.

Lemma Formula_2_8 : forall (T : Type) (A B C : Ensemble T), Included T A B -> Included T (Union T A C) (Union T B C).
Proof.
  intros T A B C H1 t1 H2.
  case H2.
  intros t2 H3.
  apply (Formula_2_2_1 T B C).
  apply H1.
  assumption.
  apply (Formula_2_2_2 T B C).
Qed.