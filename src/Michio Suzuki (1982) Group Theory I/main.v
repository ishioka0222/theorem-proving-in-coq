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
