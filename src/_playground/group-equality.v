From mathcomp
  Require Import ssreflect.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.JMeq.

Structure group : Type := make_group
{
  group_carrier : Set;
  group_inhab : inhabited group_carrier;
  group_mul : group_carrier -> group_carrier -> group_carrier;
  group_mul_assoc : forall a b c : group_carrier, group_mul (group_mul a b) c = group_mul a (group_mul b c);
  group_r_trans : forall a b : group_carrier, exists x : group_carrier, group_mul a x = b;
  group_l_trans : forall a b : group_carrier, exists y : group_carrier, group_mul y a = b;
}.

Theorem group_eq (G0 G1 : group) :
  group_carrier G0 = group_carrier G1
  -> JMeq (group_mul G0) (group_mul G1)
  -> G0 = G1.
Proof.
  move=> Hcarrier Hmul.
  destruct G0 as [carrier0 inhab0 mul0 mul_assoc0 eq_l0 eq_r0].
  destruct G1 as [carrier1 inhab1 mul1 mul_assoc1 eq_l1 eq_r1].
  simpl in * |- *.
  destruct Hcarrier.
  apply JMeq_eq in Hmul.
  destruct Hmul.
  f_equal; apply proof_irrelevance.
Qed.
