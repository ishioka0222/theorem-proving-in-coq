(* Suzuki, Michio - Group Theory. I *)
From mathcomp
  Require Import ssreflect.
Require Import Coq.Logic.Description.

(* Definition 1.1. *)
Structure group : Type := make_group
{
  G :> Set;
  inhab : inhabited G;
  mul : G -> G -> G;
  mul_assoc : forall a b c : G, mul (mul a b) c = mul a (mul b c);
  eq_l : forall a b : G, exists x : G, mul a x = b;
  eq_r : forall a b : G, exists y : G, mul y a = b;
}.

(* Definition 1.3. *)
Definition is_one (G : group) (e : G) :=
  forall g : G, mul G g e = g /\ mul G e g = g.

(* Theorem 1.2.(ii)' *)
Theorem one_exists_unique (G : group) :
  exists! one : G, is_one G one.
Proof.
  destruct (inhab G) as [a].
  destruct (eq_l G a a) as [e HaeEqa].
  destruct (eq_r G a a) as [e' He'aEqa].
  exists e.

  assert (forall g : G, mul G g e = g) as He_oner.
  + move=> g.
    destruct (eq_l G a g) as [u HauEqg].
    destruct (eq_r G a g) as [v HvaEqg].
    rewrite -HvaEqg.
    rewrite mul_assoc.
    rewrite HaeEqa.
    by [].

  assert (forall g : G, mul G e' g = g) as He'_onel.
  + move=> g.
    destruct (eq_l G a g) as [u HauEqg].
    destruct (eq_r G a g) as [v HvaEqg].
    rewrite -HauEqg.
    rewrite -mul_assoc.
    rewrite He'aEqa.
    by [].

  assert (e = e') as HeEqe'.
  + rewrite -(He_oner e').
    rewrite (He'_onel e).
    by [].

  split.
  + move=> g.
    split.
    + apply (He_oner g).
    + rewrite HeEqe'.
      rewrite (He'_onel g).
      by [].
  + move=> g Hg_one.
    destruct (Hg_one e) as [HegEqe HgeEqe].
    rewrite -(He_oner g).
    rewrite HgeEqe.
    by [].
Qed.

Definition one (G : group) : G.
  destruct (constructive_definite_description (is_one G) (one_exists_unique G)) as [one H].
  exact one.
Defined.

Theorem one_is_one (G : group) : is_one G (one G).
Proof.
  remember (one G) as e eqn: H.
  unfold one in H.
  destruct (constructive_definite_description (is_one G) (one_exists_unique G)) as [e' He'] in H.
  rewrite H.
  exact He'.
Qed.

Definition are_mutually_inverse (G : group) (a a' : G) :=
  mul G a a' = one G /\ mul G a' a = one G.

(* Theorem 1.2.(ii)'' *)
Theorem inverse_exists_unique (G : group) (a : G) :
  exists! a' : G, are_mutually_inverse G a a'.
Proof.
  destruct (eq_l G a (one G)) as [a' Haa'_eq_one].
  destruct (eq_r G a (one G)) as [a'' Ha''a_eq_one].

  assert (a' = a'') as Ha'_eq_a''.
  + rewrite -(proj1 ((one_is_one G) a'')).
    rewrite -Haa'_eq_one.
    rewrite -(mul_assoc G a'' a a').
    rewrite Ha''a_eq_one.
    rewrite (proj2 ((one_is_one G) a')).
    by [].

  rewrite -Ha'_eq_a'' in Ha''a_eq_one.
  exists a'.

  split.
  + split.
    + exact Haa'_eq_one.
    + exact Ha''a_eq_one.
  + move=> a''' [Hax_eq_one Hxa_eq_one].
    rewrite -(proj1 ((one_is_one G) a')).
    rewrite -Hax_eq_one.
    rewrite -(mul_assoc G a' a a''').
    rewrite Ha''a_eq_one.
    rewrite (proj2 ((one_is_one G) a''')).
    by [].
Qed.

Definition inv (G : group) : G -> G.
  move=> a.
  destruct (constructive_definite_description (are_mutually_inverse G a) (inverse_exists_unique G a)) as [a' H].
  exact a'.
Defined.

Theorem inv_is_inv (G : group) (a : G) : are_mutually_inverse G a (inv G a).
Proof.
  remember (inv G a) as a' eqn: H.
  unfold inv in H.
  destruct (constructive_definite_description (are_mutually_inverse G a) (inverse_exists_unique G a)) as [a'' Ha''] in H.
  rewrite H.
  exact Ha''.
Qed.

(* Theorem 1.2.(iii).1 *)
Theorem eq_l_ex_uni (G : group) :
  forall a b x : G, mul G a x = b -> x = mul G (inv G a) b.
Proof.
  move=> a b x Hax_eq_b.
  rewrite -Hax_eq_b.
  rewrite -mul_assoc.
  rewrite (proj2 (inv_is_inv G a)).
  rewrite (proj2 (one_is_one G x)).
  reflexivity.
Qed.

(* Theorem 1.2.(iii).2 *)
Theorem eq_r_ex_uni (G : group) :
  forall a b y : G, mul G y a = b -> y = mul G b (inv G a).
Proof.
  move=> a b y Hya_eq_b.
  rewrite -Hya_eq_b.
  rewrite mul_assoc.
  rewrite (proj1 (inv_is_inv G a)).
  rewrite (proj1 (one_is_one G y)).
  reflexivity.
Qed.

(* Corollary_p4_l7 *)
Structure group' : Type := make_group'
{
  G' :> Set;
  one' : G';
  inv' : G' -> G';
  mul' : G' -> G' -> G';
  mul_assoc' : forall a b c : G', mul' (mul' a b) c = mul' a (mul' b c);
  one_mul' : forall a : G', mul' one' a = a;
  mul_one' : forall a : G', mul' a one' = a;
  inv_mul' : forall a : G', mul' (inv' a) a = one';
  mul_inv' : forall a : G', mul' a (inv' a) = one';
}.

Definition group_to_group' : group -> group'.
  move=> G.
  exact (make_group'
    G
    (one G)
    (inv G)
    (mul G)
    (mul_assoc G)
    (fun a => proj2 (one_is_one G a))
    (fun a => proj1 (one_is_one G a))
    (fun a => proj2 (inv_is_inv G a))
    (fun a => proj1 (inv_is_inv G a))
   ).
Qed.

Theorem group'_to_group_sub_r (G' : group') :
  forall a b : G', exists x : G', mul' G' a x = b.
Proof.
  move=> a b.
  exists (mul' G' (inv' G' a) b).
  rewrite -mul_assoc'.
  rewrite mul_inv'.
  rewrite one_mul'.
  reflexivity.
Qed.

Theorem group'_to_group_sub_l (G' : group') :
  forall a b : G', exists y : G', mul' G' y a = b.
Proof.
  move=> a b.
  exists (mul' G' b (inv' G' a)).
  rewrite mul_assoc'.
  rewrite inv_mul'.
  rewrite mul_one'.
  reflexivity.
Qed.

Definition group'_to_group : group' -> group.
  move=> G'.
  exact (make_group
    G'
    (inhabits (one' G'))
    (mul' G')
    (mul_assoc' G')
    (group'_to_group_sub_r G')
    (group'_to_group_sub_l G')
  ).
Qed.

(* Theorem 1.4.1 *)
Theorem inv_inv (G : group) :
  forall a : G, inv G (inv G a) = a.
Proof.
  move=> a.

  pose proof (inverse_exists_unique G (inv G a)) as H.
  rewrite <- unique_existence in H.
  destruct H as [_ Huni].

  pose proof (inv_is_inv G (inv G a)) as Hinvinva.

  pose proof (inv_is_inv G a) as Ha.
  unfold are_mutually_inverse in Ha.
  rewrite <- and_comm in Ha.
  fold (are_mutually_inverse G (inv G a) a) in Ha.

  rewrite -(Huni a (inv G (inv G a)) Ha Hinvinva).
  reflexivity.
Qed.

(* Theorem 1.4.2 *)
Theorem mul_inv_rev (G : group) :
  forall a b : G, inv G (mul G a b) = mul G (inv G b) (inv G a).
Proof.
  move=> a b.

  pose proof (inverse_exists_unique G (mul G a b)) as H.
  rewrite <- unique_existence in H.
  destruct H as [_ Huni].

  pose proof (inv_is_inv G (mul G a b)) as H1.

  assert (are_mutually_inverse G (mul G a b) (mul G (inv G b) (inv G a))) as H2.
  + split.
    + rewrite (mul_assoc G a b (mul G (inv G b) (inv G a))).
      rewrite -(mul_assoc G b (inv G b) (inv G a)).
      rewrite (proj1 (inv_is_inv G b)).
      rewrite (proj2 (one_is_one G (inv G a))).
      rewrite (proj1 (inv_is_inv G a)).
      reflexivity.
    + rewrite (mul_assoc G (inv G b) (inv G a) (mul G a b)).
      rewrite -(mul_assoc G (inv G a) a b).
      rewrite (proj2 (inv_is_inv G a)).
      rewrite (proj2 (one_is_one G b)).
      rewrite (proj2 (inv_is_inv G b)).
      reflexivity.
  exact (Huni (inv G (mul G a b)) (mul G (inv G b) (inv G a)) H1 H2).
Qed.
