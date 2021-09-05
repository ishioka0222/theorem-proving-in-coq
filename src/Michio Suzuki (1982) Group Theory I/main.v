(* Suzuki, Michio - Group Theory. I *)
From mathcomp
  Require Import ssreflect.
Require Import Coq.Sets.Ensembles.

(* Definition 1.1. *)
Structure Group (T : Type) : Type := mkGroup
{
  G :> Ensemble T;
  non_emp : exists x : T, In T G x;
  mul : T -> T -> T;
  mul_closed : forall a b : T, In T G a -> In T G b -> In T G (mul a b);
  mul_assoc : forall a b c : T, mul (mul a b) c = mul a (mul b c);
  inv_mul : forall a b : T, exists x, mul a x = b;
  mul_inv : forall a b : T, exists y, mul y a = b;
}.

(* Definition 1.3. *)
Definition is_one (T : Type) (G : Group T) (e : T) :=
  forall g : T, mul T G g e = g /\ mul T G e g = g.

(* Theorem 1.2.(ii)' *)
Theorem one_exists_unique (T : Type) (G : Group T) :
  exists! one : T, is_one T G one.
Proof.
  destruct (non_emp T G) as [a HaInG].
  destruct (inv_mul T G a a) as [e HaeEqa].
  destruct (mul_inv T G a a) as [e' He'aEqa].
  exists e.

  assert (forall g : T, mul T G g e = g) as He_oner.
  + move=> g.
    destruct (inv_mul T G a g) as [u HauEqg].
    destruct (mul_inv T G a g) as [v HvaEqg].
    rewrite -HvaEqg.
    rewrite mul_assoc.
    rewrite HaeEqa.
    by [].

  assert (forall g : T, mul T G e' g = g) as He'_onel.
  + move=> g.
    destruct (inv_mul T G a g) as [u HauEqg].
    destruct (mul_inv T G a g) as [v HvaEqg].
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
