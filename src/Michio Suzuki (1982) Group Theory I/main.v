(* Suzuki, Michio - Group Theory. I *)

(* Definition 1.1. *)
Structure Group : Type := mkGroup
{
  G :> Set;
  non_emp : exists (x : G), True;
  mul : G -> G -> G;
  mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c);
  inv_mul : forall a b, exists x, mul a x = b;
  mul_inv : forall a b, exists y, mul y a = b;
}.

Arguments mul {g} _ _.

(* Definition 1.3. *)
Definition is_identity (G : Group) (e : G) :=
  forall (g : G), mul g e = g /\ mul e g = g.

(* Theorem 1.2.(ii)' *)
Theorem one_exists_unique (G : Group) :
  exists! (one : G), is_identity G one.
Proof.
  destruct (non_emp G) as [a h0].
  destruct (inv_mul G a a) as [e h1].
  destruct (mul_inv G a a) as [e' h2].
  exists e.

  assert (forall g : G, mul g e = g) as h3.
    intro g.
      destruct (inv_mul G a g) as [u h3_1].
      destruct (mul_inv G a g) as [v h3_2].

      rewrite <- h3_2.
      rewrite -> mul_assoc.
      rewrite -> h1.
      reflexivity.

  assert (forall g : G, mul e' g = g) as h4.
    intro g.
      destruct (inv_mul G a g) as [u h4_1].
      destruct (mul_inv G a g) as [v h4_2].

      rewrite <- h4_1.
      rewrite <- mul_assoc.
      rewrite -> h2.
      reflexivity.

  assert (e = e') as h5.
    rewrite <- (h3 e').
    rewrite -> (h4 e).
    reflexivity.

  split.

  intro g.
  split.
    apply (h3 g).

    rewrite -> h5.
    rewrite -> (h4 g).
    reflexivity.

  intro g.
  intro h6.

  destruct (h6 e) as [h7 h8].
  rewrite <- (h3 g).
  rewrite -> h8.
  reflexivity.
Qed.
