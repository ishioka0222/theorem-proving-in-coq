(* Suzuki, Michio - Group Theory. I *)
From mathcomp
  Require Import ssreflect.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FinFun.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Basics.

(* Definition 1.1. *)
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
  destruct G0 as [carrier0 inhab0 mul0 mul_assoc0 r_trans0 l_trans0].
  destruct G1 as [carrier1 inhab1 mul1 mul_assoc1 r_trans1 l_trans1].
  simpl in * |- *.
  destruct Hcarrier.
  apply JMeq_eq in Hmul.
  destruct Hmul.
  f_equal; apply proof_irrelevance.
Qed.

(* Definition 1.3. *)
Definition is_group_one (G : group) (e : group_carrier G) :=
  forall g : group_carrier G, group_mul G g e = g /\ group_mul G e g = g.

(* Theorem 1.2.(ii)' *)
Theorem group_one_exists_unique (G : group) :
  exists! group_one : group_carrier G, is_group_one G group_one.
Proof.
  destruct (group_inhab G) as [a].
  destruct (group_r_trans G a a) as [e Hae_eq_a].
  destruct (group_l_trans G a a) as [e' He'a_eq_a].
  exists e.

  assert (forall g : group_carrier G, group_mul G g e = g) as He_oner.
  + move=> g.
    destruct (group_r_trans G a g) as [u Hau_eq_g].
    destruct (group_l_trans G a g) as [v Hva_eq_g].
    rewrite -Hva_eq_g.
    rewrite group_mul_assoc.
    rewrite Hae_eq_a.
    by [].

  assert (forall g : group_carrier G, group_mul G e' g = g) as He'_onel.
  + move=> g.
    destruct (group_r_trans G a g) as [u Hau_eq_g].
    destruct (group_l_trans G a g) as [v Hva_eq_g].
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

Definition group_one (G : group) : group_carrier G
  := let 'exist one Hone := (constructive_definite_description (is_group_one G) (group_one_exists_unique G)) in one.

Theorem group_one_is_group_one (G : group) : is_group_one G (group_one G).
Proof.
  remember (group_one G) as e eqn: H.
  unfold group_one in H.
  destruct (constructive_definite_description (is_group_one G) (group_one_exists_unique G)) as [e' He'] in H.
  rewrite H.
  exact He'.
Qed.

Definition are_mut_inv (G : group) (a a' : group_carrier G) :=
  group_mul G a a' = group_one G /\ group_mul G a' a = group_one G.

(* Theorem 1.2.(ii)'' *)
Theorem group_inv_ex_uni (G : group) (a : group_carrier G) :
  exists! a' : group_carrier G, are_mut_inv G a a'.
Proof.
  destruct (group_r_trans G a (group_one G)) as [a' Haa'_eq_one].
  destruct (group_l_trans G a (group_one G)) as [a'' Ha''a_eq_one].

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

Definition group_inv (G : group) : group_carrier G -> group_carrier G
  := fun a => let 'exist a' Ha' := (constructive_definite_description (are_mut_inv G a) (group_inv_ex_uni G a)) in a'.

Theorem group_inv_is_group_inv (G : group) (a : group_carrier G) : are_mut_inv G a (group_inv G a).
Proof.
  remember (group_inv G a) as a' eqn: H.
  unfold group_inv in H.
  destruct (constructive_definite_description (are_mut_inv G a) (group_inv_ex_uni G a)) as [a'' Ha''] in H.
  rewrite H.
  exact Ha''.
Qed.

Theorem group_one_mul (G : group) :
  forall a : group_carrier G,
  group_mul G (group_one G) a = a.
Proof.
  move=> a.
  exact (proj2 ((group_one_is_group_one G) a)).
Qed.

Theorem group_mul_one (G : group) :
  forall a : group_carrier G,
  group_mul G a (group_one G) = a.
Proof.
  move=> a.
  exact (proj1 ((group_one_is_group_one G) a)).
Qed.

Theorem group_inv_mul (G : group) :
  forall a : group_carrier G,
  group_mul G (group_inv G a) a = group_one G.
Proof.
  move=> a.
  exact (proj2 ((group_inv_is_group_inv G) a)).
Qed.

Theorem group_mul_inv (G : group) :
  forall a : group_carrier G,
  group_mul G a (group_inv G a) = group_one G.
Proof.
  move=> a.
  exact (proj1 ((group_inv_is_group_inv G) a)).
Qed.

(* Theorem 1.2.(iii).1 *)
Theorem group_r_trans_ex_uni (G : group) :
  forall a b x : group_carrier G, group_mul G a x = b -> x = group_mul G (group_inv G a) b.
Proof.
  move=> a b x Hax_eq_b.
  rewrite -Hax_eq_b.
  rewrite -group_mul_assoc.
  rewrite (proj2 (group_inv_is_group_inv G a)).
  rewrite (proj2 (group_one_is_group_one G x)).
  reflexivity.
Qed.

(* Theorem 1.2.(iii).2 *)
Theorem group_l_trans_ex_uni (G : group) :
  forall a b y : group_carrier G, group_mul G y a = b -> y = group_mul G b (group_inv G a).
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
  group'_carrier : Set;
  group'_one : group'_carrier;
  group'_inv : group'_carrier -> group'_carrier;
  group'_mul : group'_carrier -> group'_carrier -> group'_carrier;
  group'_mul_assoc : forall a b c : group'_carrier, group'_mul (group'_mul a b) c = group'_mul a (group'_mul b c);
  group'_one_mul : forall a : group'_carrier, group'_mul group'_one a = a;
  group'_mul_one : forall a : group'_carrier, group'_mul a group'_one = a;
  group'_inv_mul : forall a : group'_carrier, group'_mul (group'_inv a) a = group'_one;
  group'_mul_inv : forall a : group'_carrier, group'_mul a (group'_inv a) = group'_one;
}.

Definition group_to_group' : group -> group'
  := fun G => (make_group'
    (group_carrier G)
    (group_one G)
    (group_inv G)
    (group_mul G)
    (group_mul_assoc G)
    (fun a => proj2 (group_one_is_group_one G a))
    (fun a => proj1 (group_one_is_group_one G a))
    (fun a => proj2 (group_inv_is_group_inv G a))
    (fun a => proj1 (group_inv_is_group_inv G a))
  ).

Theorem group'_to_group_sub_r (G' : group') :
  forall a b : group'_carrier G', exists x : group'_carrier G', group'_mul G' a x = b.
Proof.
  move=> a b.
  exists (group'_mul G' (group'_inv G' a) b).
  rewrite -group'_mul_assoc.
  rewrite group'_mul_inv.
  rewrite group'_one_mul.
  reflexivity.
Qed.

Theorem group'_to_group_sub_l (G' : group') :
  forall a b : group'_carrier G', exists y : group'_carrier G', group'_mul G' y a = b.
Proof.
  move=> a b.
  exists (group'_mul G' b (group'_inv G' a)).
  rewrite group'_mul_assoc.
  rewrite group'_inv_mul.
  rewrite group'_mul_one.
  reflexivity.
Qed.

Definition group'_to_group : group' -> group
  := fun G' => (make_group
    (group'_carrier G')
    (inhabits (group'_one G'))
    (group'_mul G')
    (group'_mul_assoc G')
    (group'_to_group_sub_r G')
    (group'_to_group_sub_l G')
  ).

Theorem group_to_group'_to_group_is_id :
  compose group'_to_group group_to_group' = id.
Proof.
  apply functional_extensionality.
  move=> G.
  destruct G.
  unfold id.
  unfold compose.
  unfold group_to_group'.
  unfold group'_to_group.
  simpl.
  f_equal; apply proof_irrelevance.
Qed.

Theorem group'_to_group_to_group'_is_id :
  compose group_to_group' group'_to_group = id.
Proof.
  apply functional_extensionality.
  move=> G'.
  destruct G'.
  unfold id.
  unfold compose.
  unfold group_to_group'.
  unfold group'_to_group.
  simpl.
  f_equal.
  (* TODO *)
Admitted.

(* Theorem 1.4.1 *)
Theorem inv_inv (G : group) :
  forall a : group_carrier G, group_inv G (group_inv G a) = a.
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
  forall a b : group_carrier G, group_inv G (group_mul G a b) = group_mul G (group_inv G b) (group_inv G a).
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
  subgroup_carrier : subset (group_carrier G);
  subgroup_inhab : inhabited (sig subgroup_carrier);
  subgroup_mul_mem : forall a b : group_carrier  G, subgroup_carrier a -> subgroup_carrier b -> subgroup_carrier (group_mul G a b);
  subgroup_inv_mem : forall a : group_carrier G, subgroup_carrier a -> subgroup_carrier (group_inv G a);
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
  (sig (subgroup_carrier G H)) -> group_carrier G
  := fun p => let 'exist x Hx := p in x.

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
  (sig (subgroup_carrier G H)) -> (sig (subgroup_carrier G H)) -> (sig (subgroup_carrier G H))
  := fun p q =>
    let 'exist a Ha := p in
    let 'exist b Hb := q in
      (exist (subgroup_carrier G H) (group_mul G a b) (subgroup_mul_mem G H a b Ha Hb)).

Theorem subgroup_mul_assoc (G : group) (H : subgroup G) :
  forall a b c : (sig (subgroup_carrier G H)),
    subgroup_mul G H (subgroup_mul G H a b) c =
      subgroup_mul G H a (subgroup_mul G H b c).
Proof.
  move=> [a Ha] [b Hb] [c Hc].
  apply (subgroup_incl_is_injective G H).
  unfold subgroup_mul.
  unfold subgroup_incl.
  exact (group_mul_assoc G a b c).
Qed.

Theorem subgroup_group_r_trans (G : group) (H : subgroup G) :
  forall a b : (sig (subgroup_carrier G H)),
  exists x : (sig (subgroup_carrier G H)),
  subgroup_mul G H a x = b.
Proof.
  move=> [a Ha] [b Hb].

  set (c := group_mul G (group_inv G a) b).
  set (Hc := subgroup_mul_mem G H (group_inv G a) b (subgroup_inv_mem G H a Ha) Hb).

  exists (exist (subgroup_carrier G H) c Hc).

  apply (subgroup_incl_is_injective G H).
  unfold subgroup_mul.
  unfold subgroup_incl.
  unfold c.
  rewrite -(group_mul_assoc G).
  rewrite (group_mul_inv G).
  rewrite (group_one_mul G).
  reflexivity.
Qed.

Theorem subgroup_group_l_trans (G : group) (H : subgroup G) :
  forall a b : (sig (subgroup_carrier G H)),
  exists y : (sig (subgroup_carrier G H)),
  subgroup_mul G H y a = b.
Proof.
  move=> [a Ha] [b Hb].

  set (c := group_mul G b (group_inv G a)).
  set (Hc := subgroup_mul_mem G H b (group_inv G a) Hb (subgroup_inv_mem G H a Ha)).

  exists (exist (subgroup_carrier G H) c Hc).

  apply (subgroup_incl_is_injective G H).
  unfold subgroup_mul.
  unfold subgroup_incl.
  unfold c.
  rewrite (group_mul_assoc G).
  rewrite (group_inv_mul G).
  rewrite (group_mul_one G).
  reflexivity.
Qed.


(* 2.2.(b) *)
Definition subgroup_to_group (G : group) :
  (subgroup G) -> group
  := fun H => (make_group
    (sig (subgroup_carrier G H))
    (subgroup_inhab G H)
    (subgroup_mul G H)
    (subgroup_mul_assoc G H)
    (subgroup_group_r_trans G H)
    (subgroup_group_l_trans G H)
  ).

(* 2.2.(c) *)
Theorem subgroup_one_is_group_one (G : group) (H : subgroup G) :
  subgroup_incl G H (group_one (subgroup_to_group G H)) = group_one G.
Proof.
  pose proof (group_one_exists_unique (subgroup_to_group G H)) as Hone_ex_uni.
  rewrite <- unique_existence in Hone_ex_uni.
  destruct Hone_ex_uni as [Hone_ex Hone_uni].

  set (one0 := group_one (subgroup_to_group G H)).
  set (one1 := (exist (subgroup_carrier G H) (group_one G) (subgroup_one_mem G H))).
  assert (one0 = one1) as Hyp0.
  + assert (is_group_one (subgroup_to_group G H) one1) as His_one.
    + move=> x.
      destruct x as [x Hx].
      split.
      + apply subgroup_incl_is_injective.
        simpl.
        rewrite (group_mul_one G).
        reflexivity.
      + apply subgroup_incl_is_injective.
        simpl.
        rewrite (group_one_mul G).
        reflexivity.
    + exact (Hone_uni one0 one1 (group_one_is_group_one (subgroup_to_group G H)) His_one).

  rewrite Hyp0.
  simpl.
  reflexivity.
Qed.
