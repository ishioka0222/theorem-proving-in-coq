Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Powerset.
Require Import Coq.Sets.Powerset_facts.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Image.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

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

Lemma Formula_2_13 : forall (T : Type) (A : Ensemble T), Complement T (Complement T A) = A.
Proof.
  intros T A.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  apply NNPP.
  apply H1.
  intros t1 H1 H2.
  apply (H2 H1).
Qed.

Lemma Formula_2_14_1 : forall (T : Type), Complement T (Empty_set T) = Full_set T.
Proof.
  intros T.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  apply Full_intro.
  intros t1 H1 H2.
  case H1.
  contradiction.
Qed.

Lemma Formula_2_14_2 : forall (T : Type), Complement T (Full_set T) = Empty_set T.
Proof.
  intros T.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  apply False_ind.
  apply H1.
  apply Full_intro.
  intros t1 H1.
  case H1.
Qed.

Lemma Formula_2_15 : forall (T : Type) (A B : Ensemble T), Included T A B <-> Included T (Complement T B) (Complement T A).
Proof.
  intros T A B.
  apply conj.
  intros H1 t1 H2 H3.
  apply H2.
  apply H1.
  assumption.
  intros H1 t1 H2.
  apply NNPP.
  intros H3.
  apply (H1 t1 H3 H2).
Qed.

Lemma Formula_2_16 : forall (T : Type) (A B : Ensemble T), Complement T (Union T A B) = Intersection T (Complement T A) (Complement T B).
Proof.
  intros T A B.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  apply Intersection_intro.
  intros H2.
  apply H1.
  apply Union_introl.
  assumption.
  intros H3.
  apply H1.
  apply Union_intror.
  assumption.
  intros t1 H1.
  case H1.
  intros t2 H2 H3 H4.
  revert H2.
  revert H3.
  case H4.
  contradiction.
  contradiction.
Qed.

Lemma Formula_2_16' : forall (T : Type) (A B : Ensemble T), Complement T (Intersection T A B) = Union T (Complement T A) (Complement T B).
Proof.
  intros T A B.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1 H1.
  case (classic (In T A t1)).
  intro H2.
  right.
  intro H3.
  apply H1.
  apply Intersection_intro.
  assumption.
  assumption.
  intro H2.
  apply Union_introl.
  assumption.
  intros t1 H1.
  case H1.
  intros t2 H2 H3.
  apply H2.
  case H3.
  intros t3 H4 H5.
  assumption.
  intros t2 H2 H3.
  apply H2.
  case H3.
  intros t3 H4 H5.
  assumption.
Qed.

Lemma Formula_p18_l10 : forall (T : Type), (Full_set T) = (Empty_set T) -> (Power_set T (Full_set T)) = (Singleton (Ensemble T) (Empty_set T)).
Proof.
  intros T H1.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1.
  rewrite -> H1.
  intros H2.
  assert (t1 = Empty_set T) as H3.
  apply Extensionality_Ensembles.
  apply conj.
  rewrite <- H1.
  intros t2 H4.
  apply Full_intro.
  apply Empty_set_minimal.
  rewrite -> H3.
  apply In_singleton.
  intros t1 H2.
  apply Definition_of_Power_set.
  intros t2 H3.
  apply Full_intro.
Qed.

Lemma Formula_p18_l10' : forall (T : Type), (Power_set T (Empty_set T)) = (Singleton (Ensemble T) (Empty_set T)).
Proof.
  intros T.
  apply Extensionality_Ensembles.
  apply conj.
  intros t1.
  apply Power_set_ind.
  intros t2 H2.
  assert (t2 = Empty_set T) as H3.
  apply Extensionality_Ensembles.
  apply conj.
  assumption.
  apply Empty_set_minimal.
  rewrite -> H3.
  apply In_singleton.
  intros t1.
  apply Singleton_ind.
  apply Definition_of_Power_set.
  intros t2.
  contradiction.
Qed.

Lemma cardinal_is_additive : forall (T : Type) (cAcupB cA cB : nat) (A B : Ensemble T), Disjoint T A B -> cardinal T A cA -> cardinal T B cB -> cardinal T (Union T A B) cAcupB -> cA + cB = cAcupB.
Proof.
  intros T.
  induction cAcupB.
  intros.
  apply cardinalO_empty in H2.
  assert (A = Empty_set T).
  pose proof (Union_introl T A B).
  rewrite H2 in H3.
  apply less_than_empty in H3.
  exact H3.
  assert (B = Empty_set T).
  pose proof (Union_intror T A B).
  rewrite H2 in H4.
  apply less_than_empty in H4.
  exact H4.
  rewrite H3 in H0.
  apply cardinal_Empty in H0.
  rewrite H4 in H1.
  apply cardinal_Empty in H1.
  rewrite <- H0.
  rewrite <- H1.
  reflexivity.
  intros.
  apply cardinal_invert in H2.
  destruct H2 as [C].
  destruct H2 as [x].
  destruct H2 as [H2].
  destruct H3 as [H3].
  assert (In T (Union T A B) x).
  rewrite H2.
  apply Union_intror.
  apply In_singleton.
  destruct H5.
  remember (Subtract T A x) as A' eqn: H6.
  remember (Union T A' B) as A'cupB eqn: H11.
  assert (B = Subtract T B x).
  symmetry.
  apply Non_disjoint_union'.
  intro HxinB.
  assert (In T (Intersection T A B) x) by exact (Intersection_intro T A B x H5 HxinB).
  rewrite (Disjoint_Intersection T A B H) in H7.
  contradiction.
  assert (Disjoint T A' B).
  rewrite H6.
  apply Disjoint_intro.
  intros y H8.
  destruct H8.
  destruct H8.
  apply Disjoint_Intersection in H.
  assert (In T (Intersection T A B) x0) by exact (Intersection_intro T A B x0 H8 H9).
  rewrite H in H12.
  contradiction.
  assert (cardinal T A' (pred cA)).
  rewrite H6.
  apply card_soustr_1.
  exact H0.
  exact H5.
  assert (cardinal T A'cupB cAcupB).
  rewrite H11.
  rewrite H6.
  rewrite H7.
  unfold Subtract.
  rewrite <- Setminus_Union_l.
  rewrite <- Nat.pred_succ.
  apply card_soustr_1.
  rewrite H2.
  apply card_add.
  exact H4.
  exact H3.
  rewrite H2.
  apply Add_intro2.
  rewrite H11 in H10.
  rewrite <- (IHcAcupB (pred cA) cB A' B H8 H9 H1 H10).
  destruct cA.
  apply cardinalO_empty in H0.
  rewrite H0 in H5.
  contradiction H5.
  rewrite Nat.pred_succ.
  reflexivity.
  remember (Subtract T B x) as B' eqn: H6.
  remember (Union T A B') as A'cupB eqn: H11.
  assert (A = Subtract T A x).
  symmetry.
  apply Non_disjoint_union'.
  intro HxinA.
  assert (In T (Intersection T A B) x) by exact (Intersection_intro T A B x HxinA H5).
  rewrite (Disjoint_Intersection T A B H) in H7.
  contradiction.
  assert (Disjoint T A B').
  rewrite H6.
  apply Disjoint_intro.
  intros y H8.
  destruct H8.
  destruct H9.
  apply Disjoint_Intersection in H.
  assert (In T (Intersection T A B) x0) by exact (Intersection_intro T A B x0 H8 H9).
  rewrite H in H12.
  contradiction.
  assert (cardinal T B' (pred cB)).
  rewrite H6.
  apply card_soustr_1.
  exact H1.
  exact H5.
  assert (cardinal T A'cupB cAcupB).
  rewrite H11.
  rewrite H6.
  rewrite H7.
  unfold Subtract.
  rewrite <- Setminus_Union_l.
  rewrite <- Nat.pred_succ.
  apply card_soustr_1.
  rewrite H2.
  apply card_add.
  exact H4.
  exact H3.
  rewrite H2.
  apply Add_intro2.
  rewrite H11 in H10.
  rewrite <- (IHcAcupB cA (pred cB) A B' H8 H0 H9 H10).
  destruct cB.
  apply cardinalO_empty in H1.
  rewrite H1 in H5.
  contradiction H5.
  rewrite Nat.pred_succ.
  auto.
Qed.

Lemma setminus_disjoint : forall (T : Type) (A B : Ensemble T), Disjoint T (Setminus T A B) (Intersection T A B).
Proof.
  intros.
  apply Disjoint_intro.
  intro.
  intro.
  destruct H.
  destruct H.
  destruct H0.
  contradiction.
Qed.

Lemma setminus_union : forall (T : Type) (A B : Ensemble T), A = Union T (Setminus T A B) (Intersection T A B).
Proof.
  intro.
  intro.
  intro.
  apply Extensionality_Ensembles.
  apply conj.
  intro.
  intro.
  case (classic (In T B x)).
  intro.
  apply Union_intror.
  apply Intersection_intro.
  exact H.
  exact H0.
  intro.
  apply Union_introl.
  apply Setminus_intro.
  exact H.
  exact H0.
  intro.
  intro.
  destruct H.
  destruct H.
  exact H.
  destruct H.
  exact H.
Qed.

Lemma difference_intersection_disjoint : forall (T : Type) (A B : Ensemble T), Disjoint T (Union T (Setminus T A B) (Setminus T B A)) (Intersection T A B).
  intro.
  intro.
  intro.
  apply Disjoint_intro.
  intro.
  intro.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  contradiction.
  destruct H.
  destruct H0.
  contradiction.
Qed.

Lemma difference_intersection_union : forall (T : Type) (A B : Ensemble T), (Union T A B) = Union T (Union T (Setminus T A B) (Setminus T B A)) (Intersection T A B).
  intro.
  intro.
  intro.
  apply Extensionality_Ensembles.
  apply conj.
  intro.
  intro.
  destruct H.
  case (classic (In T B x)).
  intro.
  apply Union_intror.
  apply Intersection_intro.
  exact H.
  exact H0.
  intro.
  apply Union_introl.
  apply Union_introl.
  apply Setminus_intro.
  exact H.
  exact H0.
  case (classic (In T A x)).
  intro.
  apply Union_intror.
  apply Intersection_intro.
  exact H0.
  exact H.
  intro.
  apply Union_introl.
  apply Union_intror.
  apply Setminus_intro.
  exact H.
  exact H0.
  intro.
  intro.
  destruct H.
  destruct H.
  destruct H.
  apply Union_introl.
  exact H.
  destruct H.
  apply Union_intror.
  exact H.
  destruct H.
  apply Union_introl.
  exact H.
Qed.

Lemma difference_disjoint : forall (T : Type) (A B : Ensemble T), Disjoint T (Setminus T A B) (Setminus T B A).
Proof.
  intro.
  intro.
  intro.
  apply Disjoint_intro.
  intro.
  intro.
  destruct H.
  destruct H.
  destruct H0.
  contradiction.
Qed.

Lemma cardinal_is_strongly_additive : forall (T : Type) (cAcupB cAcapB cA cB : nat) (A B : Ensemble T), cardinal T A cA -> cardinal T B cB -> cardinal T (Intersection T A B) cAcapB -> cardinal T (Union T A B) cAcupB -> cA + cB - cAcapB = cAcupB.
Proof.
  intros T cAcupB cAcapB cA cB A B HcA HcB HcAcapB HcAcupB.
  remember (Setminus T A B) as AminusB eqn: HAminusB.
  remember (Setminus T B A) as BminusA eqn: HBminusA.
  remember (Intersection T A B) as AcapB eqn: HAcapB.
  assert (Finite T AminusB) as HAminusBisFinite.
  rewrite HAminusB.
  apply (Finite_downward_closed T A).
  apply (cardinal_finite T A cA HcA).
  intros x HxInAminusB.
  destruct HxInAminusB as [HxinA HxnotinB].
  exact HxinA.
  assert (Finite T BminusA) as HBminusAisFinite.
  rewrite HBminusA.
  apply (Finite_downward_closed T B).
  apply (cardinal_finite T B cB HcB).
  intros x HxInBminusA.
  destruct HxInBminusA as [HxinB HxnotinA].
  exact HxinB.
  apply finite_cardinal in HAminusBisFinite.
  destruct HAminusBisFinite as [cAminusB HcAminusB].
  apply finite_cardinal in HBminusAisFinite.
  destruct HBminusAisFinite as [cBminusA HcBminusA].
  pose proof (setminus_disjoint T A B) as HdisjAB.
  pose proof (setminus_union T A B) as HunionAB.
  pose proof (setminus_union T B A) as HunionBA.
  assert (cAminusB + cAcapB = cA) as HeqA.
  apply (cardinal_is_additive T cA cAminusB cAcapB AminusB AcapB).
  rewrite HAminusB.
  rewrite HAcapB.
  apply setminus_disjoint.
  exact HcAminusB.
  exact HcAcapB.
  rewrite HAminusB.
  rewrite HAcapB.
  rewrite <- HunionAB.
  exact HcA.
  assert (cBminusA + cAcapB = cB) as HeqB.
  apply (cardinal_is_additive T cB cBminusA cAcapB BminusA AcapB).
  rewrite HBminusA.
  rewrite HAcapB.
  rewrite Intersection_commutative.
  apply setminus_disjoint.
  exact HcBminusA.
  exact HcAcapB.
  rewrite HBminusA.
  rewrite HAcapB.
  rewrite Intersection_commutative.
  rewrite <- HunionBA.
  exact HcB.
  assert (Finite T (Union T (Setminus T A B) (Setminus T B A))) as HdiffABisFinite.
  apply (Finite_downward_closed T (Union T A B)).
  apply (cardinal_finite T (Union T A B) cAcupB HcAcupB).
  intro.
  intro.
  destruct H.
  destruct H.
  apply Union_introl.
  exact H.
  destruct H.
  apply Union_intror.
  exact H.
  apply finite_cardinal in HdiffABisFinite.
  destruct HdiffABisFinite as [cDiff HcDiff].
  assert (cAminusB + cBminusA = cDiff) as HcDiffEq.
  apply (cardinal_is_additive T cDiff cAminusB cBminusA AminusB BminusA).
  rewrite HAminusB.
  rewrite HBminusA.
  apply difference_disjoint.
  assumption.
  assumption.
  rewrite HAminusB.
  rewrite HBminusA.
  assumption.
  assert (cDiff + cAcapB = cAcupB) as HcDiffCap.
  apply (cardinal_is_additive T cAcupB cDiff cAcapB (Union T (Setminus T A B) (Setminus T B A)) AcapB).
  rewrite HAcapB.
  apply difference_intersection_disjoint.
  assumption.
  assumption.
  rewrite HAcapB.
  rewrite <- difference_intersection_union.
  assumption.
  rewrite <- HeqA.
  rewrite <- HeqB.
  rewrite <- HcDiffCap.
  rewrite <- HcDiffEq.
  lia.
Qed.

Lemma cardinality_power_set :
  forall (T : Type) (A : Ensemble T) (n : nat),
    cardinal T A n -> cardinal _ (Power_set _ A) (2 ^ n).
Proof.
  intros T A n.
  revert A.
  induction n.
  intros A HA0.
  inversion HA0.
  rewrite Formula_p18_l10'.
  rewrite <- Empty_set_zero'.
  apply card_add.
  apply card_empty.
  intro Hcont.
  contradiction.
  intros A HASn.
  apply (cardinal_invert T A (S n)) in HASn.
  destruct HASn as [A' Htemp].
  destruct Htemp as [a Htemp].
  destruct Htemp as [HAeqA'a Htemp].
  destruct Htemp as [HanotinA' HA'n].

  remember (fun (X : (Ensemble T)) => Included T X A /\ ~In T X a) as PA eqn: HPA.
  remember (fun (X : (Ensemble T)) => Included T X A /\ In T X a) as PA' eqn: HPA'.

  assert (Disjoint (Ensemble T) PA PA') as HdisjPAPA'.
  apply Disjoint_intro.
  intros X HXinCap.
  destruct HXinCap as [X HXinPA HXinPA'].
  rewrite HPA in HXinPA.
  destruct HXinPA.
  rewrite HPA' in HXinPA'.
  destruct HXinPA'.
  contradiction.

  assert (cardinal (Ensemble T) PA (2 ^ n)) as HPA2n.
  assert (PA = Power_set T A') as HeqPA.
  apply Extensionality_Ensembles.
  apply conj.
  intros X HXinPA.
  rewrite HPA in HXinPA.
  destruct HXinPA as [HXinclA HanotinX].
  rewrite HAeqA'a in HXinclA.
  assert (Included T X A') as HXinclA'.
  intros x HxinX.
  case (classic (In T A' x)).
  auto.
  intros HxinA'.
  pose proof (HXinclA x HxinX) as HxinA'a.
  destruct HxinA'a as [x HxinA'' | x HxinSinga].
  contradiction.
  apply Singleton_inv in HxinSinga.
  rewrite <- HxinSinga in HxinX.
  contradiction.
  apply Definition_of_Power_set.
  exact HXinclA'.
  intros x HxinPA'.
  destruct HxinPA' as [X HXinclA'].
  rewrite HPA.
  rewrite HAeqA'a.
  apply conj.
  intros x HxinX.
  apply Union_introl.
  exact (HXinclA' x HxinX).
  intros HainX.
  contradiction (HXinclA' a HainX).
  rewrite HeqPA.
  exact (IHn A' HA'n).

  remember (fun (X : Ensemble T) => Add T X a) as f eqn: Hf.

  assert ((Im (Ensemble T) (Ensemble T) (Full_set (Ensemble T)) f) = PA') as HImfeqPA'.
  apply Extensionality_Ensembles.
  apply conj.
  intros X HX.
  destruct HX as [X HX Y HfXeqY].
  rewrite HfXeqY.
  rewrite Hf.
  rewrite HPA'.
  apply conj.
  intros x HainXa.
  destruct HainXa as [x HxinX |].
Admitted.
