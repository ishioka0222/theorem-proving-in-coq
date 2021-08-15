Require Import Coq.Logic.Classical_Prop.
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

Lemma Formula_2_9 : forall (T : Type) (A : Ensemble T), (Union T (Empty_set T) A) = A.
Proof.
  intros T A.
  apply (Formula_2_7).
  apply (Formula_1_5).
Qed.

Lemma Formula_2_2'_1 : forall (T : Type) (A B : Ensemble T), Included T (Intersection T A B) A.
Proof.
  intros T A B t1 H1.
  case H1.
  intros t2 H2 H3.
  assumption.
Qed.

Lemma Formula_2_2'_2 : forall (T : Type) (A B : Ensemble T), Included T (Intersection T A B) B.
Proof.
  intros T A B t1 H1.
  case H1.
  intros t2 H2 H3.
  assumption.
Qed.

Lemma Formula_2_3' : forall (T : Type) (A B C : Ensemble T), Included T C A /\ Included T C B -> Included T C (Intersection T A B).
Proof.
  intros T A B C [H1 H2] t1 H3.
  apply Intersection_intro.
  apply H1.
  assumption.
  apply H2.
  assumption.
Qed.

Lemma Formula_2_4' : forall (T : Type) (A : Ensemble T), (Intersection T A A) = A.
Proof.
  intros T A.
  apply Extensionality_Ensembles.
  apply conj.
  apply (Formula_2_2'_1 T A A).
  intros t1 H1.
  apply Intersection_intro.
  assumption.
  assumption.
Qed.

Lemma Formula_2_5' : forall (T : Type) (A B : Ensemble T), (Intersection T A B) = (Intersection T B A).
Proof.
  intros T.
  assert (forall (A B : Ensemble T), Included T (Intersection T A B) (Intersection T B A)) as H.
  intros A B t1 H1.
  apply Intersection_intro.
  case H1.
  intros t2 H2 H3.
  assumption.
  case H1.
  intros t2 H2 H3.
  assumption.
  intros A B.
  apply Extensionality_Ensembles.
  apply conj.
  apply (H A B).
  apply (H B A).
Qed.

Lemma Formula_2_6' : forall (T : Type) (A B C : Ensemble T), (Intersection T (Intersection T A B) C) = (Intersection T A (Intersection T B C)).
Proof.
  intros T A B C.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  apply Intersection_intro.
  case H1.
  intros t2 H2 H3.
  case H2.
  intros t3 H4 H5.
  assumption.
  apply Intersection_intro.
  case H1.
  intros t2 H2 H3.
  case H2.
  intros t3 H4 H5.
  assumption.
  case H1.
  intros t2 H2 H3.
  assumption.
  intros t1 H1.
  apply Intersection_intro.
  apply Intersection_intro.
  case H1.
  intros t2 H2 H3.
  assumption.
  case H1.
  intros t2 H2 H3.
  case H3.
  intros t3 H4 H5.
  assumption.
  case H1.
  intros t2 H2 H3.
  case H3.
  intros t3 H4 H5.
  assumption.
Qed.

Lemma Formula_2_7' : forall (T : Type) (A B : Ensemble T), Included T A B <-> (Intersection T A B) = A.
Proof.
  intros T A B.
  apply conj.
  intros H1.
  apply Extensionality_Ensembles.
  apply conj.
  intros t2 H2.
  case H2.
  intros t H3 H4.
  assumption.
  intros t1 H2.
  apply Intersection_intro.
  assumption.
  apply (H1 t1 H2).
  intros H1.
  case H1.
  apply (Formula_2_2'_2 T A B).
Qed.

Lemma Formula_2_8' : forall (T : Type) (A B C : Ensemble T), Included T A B -> Included T (Intersection T A C) (Intersection T B C).
Proof.
  intros T A B C H1 t1 H2.
  case H2.
  intros t2 H3 H4.
  apply Intersection_intro.
  apply (H1 t2 H3).
  assumption.
Qed.

Lemma Formula_2_9' : forall (T : Type) (A : Ensemble T), Intersection T (Empty_set T) A = (Empty_set T).
Proof.
  intros T A.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  case H1.
  intros t2 H2 H3.
  assumption.
  intros t1.
  contradiction.
Qed.

Lemma Formula_2_10 : forall (T : Type) (A B C : Ensemble T), Intersection T (Union T A B) C = Union T (Intersection T A C) (Intersection T B C).
Proof.
  intros T A B C.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  case H1.
  intros t2 H2.
  case H2.
  intros t3 H3 H4.
  apply Union_introl.
  apply Intersection_intro.
  assumption.
  assumption.
  intros t3 H3 H4.
  apply Union_intror.
  apply Intersection_intro.
  assumption.
  assumption.
  intros t1 H1.
  case H1.
  intros t2 H2.
  case H2.
  intros t3 H3 H4.
  apply Intersection_intro.
  apply Union_introl.
  assumption.
  assumption.
  intros t2 H2.
  case H2.
  intros t3 H3 H4.
  apply Intersection_intro.
  apply Union_intror.
  assumption.
  assumption.
Qed.

Lemma Formula_2_10' : forall (T : Type) (A B C : Ensemble T), Union T (Intersection T A B) C = Intersection T (Union T A C) (Union T B C).
Proof.
  intros T A B C.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  case H1.
  intros t2 H2.
  case H2.
  intros t3 H3 H4.
  apply Intersection_intro.
  apply Union_introl.
  assumption.
  apply Union_introl.
  assumption.
  intros t2 H2.
  apply Intersection_intro.
  apply Union_intror.
  assumption.
  apply Union_intror.
  assumption.
  intros t1 H1.
  case H1.
  intros t2 H2.
  case H2.
  intros t3 H3 H4.
  revert H3.
  case H4.
  intros t4 H5 H6.
  apply Union_introl.
  apply (Intersection_intro T A B).
  assumption.
  assumption.
  intros t4 H5 H6.
  apply Union_intror.
  assumption.
  intros t3 H3 H4.
  apply Union_intror.
  assumption.
Qed.

Lemma Formula_2_11 : forall (T : Type) (A B : Ensemble T), Intersection T (Union T A B) A = A.
Proof.
  intros T A B.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  case H1.
  intros t2 H2 H3.
  assumption.
  intros t1 H1.
  apply Intersection_intro.
  apply Union_introl.
  assumption.
  assumption. 
Qed.

Lemma Formula_2_11' : forall (T : Type) (A B : Ensemble T), Union T (Intersection T A B) A = A.
Proof.
  intros T A B.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  case H1.
  intros t2 H2.
  case H2.
  intros t3 H3 H4.
  assumption.
  intros t2 H2.
  assumption.
  intros t1 H1.
  apply Union_intror.
  assumption.
Qed.

Lemma Formula_2_12_1 : forall (T : Type) (A : Ensemble T), Union T A (Complement T A) = Full_set T.
Proof.
  intros T A.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  apply (Full_intro T t1).
  intros t1 H1.
  case (classic (In T A t1)).
  intros H2.
  apply Union_introl.
  assumption.
  intros H2.
  apply Union_intror.
  assumption.
Qed.

Lemma Formula_2_12_2 : forall (T : Type) (A : Ensemble T), Intersection T A (Complement T A) = Empty_set T.
Proof.
  intros T A.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  case H1.
  contradiction.
  intros t1.
  contradiction.
Qed.
