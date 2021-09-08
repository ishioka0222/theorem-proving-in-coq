(* Suzuki, Michio - Group Theory. I *)
From mathcomp
  Require Import ssreflect.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FinFun.
Require Import Coq.Logic.Classical_Prop.

(* Definition 1.1. *)
Structure group : Type := make_group
{
  group_carrier :> Set;
  group_inhab : inhabited group_carrier;
  group_mul : group_carrier -> group_carrier -> group_carrier;
  group_mul_assoc : forall a b c : group_carrier, group_mul (group_mul a b) c = group_mul a (group_mul b c);
  group_eq_l : forall a b : group_carrier, exists x : group_carrier, group_mul a x = b;
  group_eq_r : forall a b : group_carrier, exists y : group_carrier, group_mul y a = b;
}.

(* Definition 1.3. *)
Definition is_group_one (G : group) (e : G) :=
  forall g : G, group_mul G g e = g /\ group_mul G e g = g.

(* Theorem 1.2.(ii)' *)
Theorem group_one_exists_unique (G : group) :
  exists! group_one : G, is_group_one G group_one.
Proof.
  destruct (group_inhab G) as [a].
  destruct (group_eq_l G a a) as [e Hae_eq_a].
  destruct (group_eq_r G a a) as [e' He'a_eq_a].
  exists e.

  assert (forall g : G, group_mul G g e = g) as He_oner.
  + move=> g.
    destruct (group_eq_l G a g) as [u Hau_eq_g].
    destruct (group_eq_r G a g) as [v Hva_eq_g].
    rewrite -Hva_eq_g.
    rewrite group_mul_assoc.
    rewrite Hae_eq_a.
    by [].

  assert (forall g : G, group_mul G e' g = g) as He'_onel.
  + move=> g.
    destruct (group_eq_l G a g) as [u Hau_eq_g].
    destruct (group_eq_r G a g) as [v Hva_eq_g].
    rewrite -Hau_eq_g.
    rewrite -group_mul_assoc.
    rewrite He'a_eq_a.
    by [].

  assert (e = e') as He_eq_e'.
  + rewrite -(He_oner e').
    rewrite (He'_onel e).
    by [].

  split.
  + move=> g.
    split.
    + apply (He_oner g).
    + rewrite He_eq_e'.
      rewrite (He'_onel g).
      by [].
  + move=> g Hg_one.
    destruct (Hg_one e) as [Heg_eq_e Hge_eq_e].
    rewrite -(He_oner g).
    rewrite Hge_eq_e.
    by [].
Qed.

Definition group_one (G : group) : G.
  destruct (constructive_definite_description (is_group_one G) (group_one_exists_unique G)) as [group_one H].
  exact group_one.
Defined.

Theorem group_one_is_group_one (G : group) : is_group_one G (group_one G).
Proof.
  remember (group_one G) as e eqn: H.
  unfold group_one in H.
  destruct (constructive_definite_description (is_group_one G) (group_one_exists_unique G)) as [e' He'] in H.
  rewrite H.
  exact He'.
Qed.

Definition are_mut_inv (G : group) (a a' : G) :=
  group_mul G a a' = group_one G /\ group_mul G a' a = group_one G.

(* Theorem 1.2.(ii)'' *)
Theorem group_inv_ex_uni (G : group) (a : G) :
  exists! a' : G, are_mut_inv G a a'.
Proof.
  destruct (group_eq_l G a (group_one G)) as [a' Haa'_eq_one].
  destruct (group_eq_r G a (group_one G)) as [a'' Ha''a_eq_one].

  assert (a' = a'') as Ha'_eq_a''.
  + rewrite -(proj1 ((group_one_is_group_one G) a'')).
    rewrite -Haa'_eq_one.
    rewrite -(group_mul_assoc G a'' a a').
    rewrite Ha''a_eq_one.
    rewrite (proj2 ((group_one_is_group_one G) a')).
    by [].

  rewrite -Ha'_eq_a'' in Ha''a_eq_one.
  exists a'.

  split.
  + split.
    + exact Haa'_eq_one.
    + exact Ha''a_eq_one.
  + move=> a''' [Hax_eq_one Hxa_eq_one].
    rewrite -(proj1 ((group_one_is_group_one G) a')).
    rewrite -Hax_eq_one.
    rewrite -(group_mul_assoc G a' a a''').
    rewrite Ha''a_eq_one.
    rewrite (proj2 ((group_one_is_group_one G) a''')).
    by [].
Qed.

Definition group_inv (G : group) : G -> G.
  move=> a.
  destruct (constructive_definite_description (are_mut_inv G a) (group_inv_ex_uni G a)) as [a' H].
  exact a'.
Defined.

Theorem group_inv_is_group_inv (G : group) (a : G) : are_mut_inv G a (group_inv G a).
Proof.
  remember (group_inv G a) as a' eqn: H.
  unfold group_inv in H.
  destruct (constructive_definite_description (are_mut_inv G a) (group_inv_ex_uni G a)) as [a'' Ha''] in H.
  rewrite H.
  exact Ha''.
Qed.

(* Theorem 1.2.(iii).1 *)
Theorem group_eq_l_ex_uni (G : group) :
  forall a b x : G, group_mul G a x = b -> x = group_mul G (group_inv G a) b.
Proof.
  move=> a b x Hax_eq_b.
  rewrite -Hax_eq_b.
  rewrite -group_mul_assoc.
  rewrite (proj2 (group_inv_is_group_inv G a)).
  rewrite (proj2 (group_one_is_group_one G x)).
  reflexivity.
Qed.

(* Theorem 1.2.(iii).2 *)
Theorem group_eq_r_ex_uni (G : group) :
  forall a b y : G, group_mul G y a = b -> y = group_mul G b (group_inv G a).
Proof.
  move=> a b y Hya_eq_b.
  rewrite -Hya_eq_b.
  rewrite group_mul_assoc.
  rewrite (proj1 (group_inv_is_group_inv G a)).
  rewrite (proj1 (group_one_is_group_one G y)).
  reflexivity.
Qed.

(* Corollary_p4_l7 *)
Structure group' : Type := make_group'
{
  group'_carrier :> Set;
  group'_one : group'_carrier;
  group'_inv : group'_carrier -> group'_carrier;
  group'_mul : group'_carrier -> group'_carrier -> group'_carrier;
  group'_mul_assoc : forall a b c : group'_carrier, group'_mul (group'_mul a b) c = group'_mul a (group'_mul b c);
  group'_one_mul : forall a : group'_carrier, group'_mul group'_one a = a;
  group'_mul_one : forall a : group'_carrier, group'_mul a group'_one = a;
  group'_inv_mul : forall a : group'_carrier, group'_mul (group'_inv a) a = group'_one;
  group'_mul_inv : forall a : group'_carrier, group'_mul a (group'_inv a) = group'_one;
}.

Definition group_to_group' : group -> group'.
  move=> G.
  exact (make_group'
    G
    (group_one G)
    (group_inv G)
    (group_mul G)
    (group_mul_assoc G)
    (fun a => proj2 (group_one_is_group_one G a))
    (fun a => proj1 (group_one_is_group_one G a))
    (fun a => proj2 (group_inv_is_group_inv G a))
    (fun a => proj1 (group_inv_is_group_inv G a))
   ).
Qed.

Theorem group'_to_group_sub_r (G' : group') :
  forall a b : G', exists x : G', group'_mul G' a x = b.
Proof.
  move=> a b.
  exists (group'_mul G' (group'_inv G' a) b).
  rewrite -group'_mul_assoc.
  rewrite group'_mul_inv.
  rewrite group'_one_mul.
  reflexivity.
Qed.

Theorem group'_to_group_sub_l (G' : group') :
  forall a b : G', exists y : G', group'_mul G' y a = b.
Proof.
  move=> a b.
  exists (group'_mul G' b (group'_inv G' a)).
  rewrite group'_mul_assoc.
  rewrite group'_inv_mul.
  rewrite group'_mul_one.
  reflexivity.
Qed.

Definition group'_to_group : group' -> group.
  move=> G'.
  exact (make_group
    G'
    (inhabits (group'_one G'))
    (group'_mul G')
    (group'_mul_assoc G')
    (group'_to_group_sub_r G')
    (group'_to_group_sub_l G')
  ).
Qed.

(* Theorem 1.4.1 *)
Theorem inv_inv (G : group) :
  forall a : G, group_inv G (group_inv G a) = a.
Proof.
  move=> a.

  pose proof (group_inv_ex_uni G (group_inv G a)) as H.
  rewrite <- unique_existence in H.
  destruct H as [_ Huni].

  pose proof (group_inv_is_group_inv G (group_inv G a)) as Hinvinva.

  pose proof (group_inv_is_group_inv G a) as Ha.
  unfold are_mut_inv in Ha.
  rewrite <- and_comm in Ha.
  fold (are_mut_inv G (group_inv G a) a) in Ha.

  rewrite -(Huni a (group_inv G (group_inv G a)) Ha Hinvinva).
  reflexivity.
Qed.

(* Theorem 1.4.2 *)
Theorem group_mul_inv_rev (G : group) :
  forall a b : G, group_inv G (group_mul G a b) = group_mul G (group_inv G b) (group_inv G a).
Proof.
  move=> a b.

  pose proof (group_inv_ex_uni G (group_mul G a b)) as H.
  rewrite <- unique_existence in H.
  destruct H as [_ Huni].

  pose proof (group_inv_is_group_inv G (group_mul G a b)) as H1.

  assert (are_mut_inv G (group_mul G a b) (group_mul G (group_inv G b) (group_inv G a))) as H2.
  + split.
    + rewrite (group_mul_assoc G a b (group_mul G (group_inv G b) (group_inv G a))).
      rewrite -(group_mul_assoc G b (group_inv G b) (group_inv G a)).
      rewrite (proj1 (group_inv_is_group_inv G b)).
      rewrite (proj2 (group_one_is_group_one G (group_inv G a))).
      rewrite (proj1 (group_inv_is_group_inv G a)).
      reflexivity.
    + rewrite (group_mul_assoc G (group_inv G b) (group_inv G a) (group_mul G a b)).
      rewrite -(group_mul_assoc G (group_inv G a) a b).
      rewrite (proj2 (group_inv_is_group_inv G a)).
      rewrite (proj2 (group_one_is_group_one G b)).
      rewrite (proj2 (group_inv_is_group_inv G b)).
      reflexivity.
  exact (Huni (group_inv G (group_mul G a b)) (group_mul G (group_inv G b) (group_inv G a)) H1 H2).
Qed.

(* Definition 2.1 *)
Definition subset (S : Set) := S -> Prop.

Structure subgroup (G : group) : Type := make_subgroup
{
  subgroup_carrier :> subset G;
  subgroup_inhab : inhabited (sig subgroup_carrier);
  subgroup_mul_mem : forall a b : G, subgroup_carrier a -> subgroup_carrier b -> subgroup_carrier (group_mul G a b);
  subgroup_inv_mem : forall a : G, subgroup_carrier a -> subgroup_carrier (group_inv G a);
}.

(* 2.2.(a) *)
Theorem subgroup_one_mem (G : group) (H : subgroup G) :
  subgroup_carrier G H (group_one G).
Proof.
  destruct (subgroup_inhab G H) as [Hinhab].
  destruct Hinhab as [a Ha_in_H].
  
  pose proof (subgroup_inv_mem G H a Ha_in_H) as Hainv_in_H.
  pose proof (subgroup_mul_mem G H a (group_inv G a) Ha_in_H Hainv_in_H) as Hmul_in_H.
  rewrite (proj1 (group_inv_is_group_inv G a)) in Hmul_in_H.
  exact Hmul_in_H.
Qed.

Definition subgroup_incl (G : group) (H : subgroup G) :
  (sig (subgroup_carrier G H)) -> G.
Proof.
  move=> [a Ha].
  exact a.
Defined.

Theorem subgroup_incl_is_injective (G : group) (H : subgroup G) :
  Injective (subgroup_incl G H).
Proof.
  move=> [x Hx] [y Hy] Heq.
  unfold subgroup_incl in Heq.
  move: Hx Hy.
  rewrite -Heq.
  move=> Hx Hy.
  apply f_equal.
  apply proof_irrelevance.
Qed.

Definition subgroup_mul (G : group) (H : subgroup G) :
  (sig (subgroup_carrier G H)) -> (sig (subgroup_carrier G H)) -> (sig (subgroup_carrier G H)).
Proof.
  move=> [a Ha] [b Hb].
  exists (group_mul G a b).
  exact (subgroup_mul_mem G H a b Ha Hb).
Defined.

Theorem subgroup_mul_assoc (G : group) (H : subgroup G) :
  forall a b c : (sig (subgroup_carrier G H)),
    subgroup_mul G H (subgroup_mul G H a b) c =
      subgroup_mul G H a (subgroup_mul G H b c).
Proof.
  (* TODO *)
Admitted.

Theorem subgroup_group_eq_l (G : group) (H : subgroup G) :
  forall a b : (sig (subgroup_carrier G H)),
  exists x : (sig (subgroup_carrier G H)),
  subgroup_mul G H a x = b.
Proof.
  (* TODO *)
Admitted.

Theorem subgroup_group_eq_r (G : group) (H : subgroup G) :
  forall a b : (sig (subgroup_carrier G H)),
  exists y : (sig (subgroup_carrier G H)),
  subgroup_mul G H y a = b.
Proof.
  (* TODO *)
Admitted.

(* 2.2.(b) *)
Theorem subgroup_is_group (G : group) :
  (subgroup G) -> group.
Proof.
  move=> H.
  exact (make_group
    (sig (subgroup_carrier G H))
    (subgroup_inhab G H)
    (subgroup_mul G H)
    (subgroup_mul_assoc G H)
    (subgroup_group_eq_l G H)
    (subgroup_group_eq_r G H)
  ).
Defined.
