(* Suzuki, Michio - Group Theory. I *)
From mathcomp
  Require Import ssreflect.
Require Import Coq.Logic.Description.

(* Definition 1.1. *)
Structure Group : Type := mkGroup
{
  G :> Set;
  inhab : inhabited G;
  mul : G -> G -> G;
  mul_assoc : forall a b c : G, mul (mul a b) c = mul a (mul b c);
  inv_mul : forall a b : G, exists x : G, mul a x = b;
  mul_inv : forall a b : G, exists y : G, mul y a = b;
}.

(* Definition 1.3. *)
Definition is_one (G : Group) (e : G) :=
  forall g : G, mul G g e = g /\ mul G e g = g.

(* Theorem 1.2.(ii)' *)
Theorem one_exists_unique (G : Group) :
  exists! one : G, is_one G one.
Proof.
  destruct (inhab G) as [a].
  destruct (inv_mul G a a) as [e HaeEqa].
  destruct (mul_inv G a a) as [e' He'aEqa].
  exists e.

  assert (forall g : G, mul G g e = g) as He_oner.
  + move=> g.
    destruct (inv_mul G a g) as [u HauEqg].
    destruct (mul_inv G a g) as [v HvaEqg].
    rewrite -HvaEqg.
    rewrite mul_assoc.
    rewrite HaeEqa.
    by [].

  assert (forall g : G, mul G e' g = g) as He'_onel.
  + move=> g.
    destruct (inv_mul G a g) as [u HauEqg].
    destruct (mul_inv G a g) as [v HvaEqg].
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

Definition one (G : Group) : G.
  destruct (constructive_definite_description (is_one G) (one_exists_unique G)) as [one H].
  exact one.
Defined.

Theorem one_is_one (G : Group) : is_one G (one G).
Proof.
  remember (one G) as e eqn: H.
  unfold one in H.
  destruct (constructive_definite_description (is_one G) (one_exists_unique G)) as [e' He'] in H.
  rewrite H.
  exact He'.
Qed.

Definition are_mutually_inverse (G : Group) (a a' : G) :=
  mul G a a' = one G /\ mul G a' a = one G.

(* Theorem 1.2.(ii)'' *)
Theorem inverse_exists_unique (G : Group) (a : G) :
  exists! a' : G, are_mutually_inverse G a a'.
Proof.
  destruct (inv_mul G a (one G)) as [a' Haa'_eq_one].
  destruct (mul_inv G a (one G)) as [a'' Ha''a_eq_one].
  
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

Definition inv (G : Group) : G -> G.
  move=> a.
  destruct (constructive_definite_description (are_mutually_inverse G a) (inverse_exists_unique G a)) as [a' H].
  exact a'.
Defined.

Theorem inv_is_inv (G : Group) (a : G) : are_mutually_inverse G a (inv G a).
Proof.
  remember (inv G a) as a' eqn: H.
  unfold inv in H.
  destruct (constructive_definite_description (are_mutually_inverse G a) (inverse_exists_unique G a)) as [a'' Ha''] in H.
  rewrite H.
  exact Ha''.
Qed.
