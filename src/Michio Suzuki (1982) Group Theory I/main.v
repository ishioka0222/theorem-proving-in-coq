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

Theorem group_one_inv (G : group) :
  group_inv G (group_one G) = group_one G.
Proof.
  pose proof (group_inv_ex_uni G (group_one G)) as Hex_uni.
  rewrite <- unique_existence in Hex_uni.
  destruct Hex_uni as [Hex Huni].
  apply (Huni (group_inv G (group_one G)) (group_one G)).
  + exact (group_inv_is_group_inv G (group_one G)).
  + split; rewrite group_one_mul; reflexivity.
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

Theorem group'_eq (G0 G1 : group') :
  group'_carrier G0 = group'_carrier G1
  -> JMeq (group'_mul G0) (group'_mul G1)
  -> G0 = G1.
Proof.
  move => Hcarrier Hmul.
  destruct G0 as [carrier0 one0 inv0 mul0 mul_assoc0 one_mul0 mul_one0 inv_mul0 mul_inv0].
  destruct G1 as [carrier1 one1 inv1 mul1 mul_assoc1 one_mul1 mul_one1 inv_mul1 mul_inv1].
  simpl in * |- *.
  destruct Hcarrier.
  apply JMeq_eq in Hmul.
  destruct Hmul.

  assert (one0 = one1) as Hone.
  + rewrite -(one_mul0 one1).
    rewrite (mul_one1 one0).
    reflexivity.
  destruct Hone.

  assert (inv0 = inv1) as Hinv.
  + apply functional_extensionality.
    move=> x.
    rewrite -(mul_one0 (inv0 x)).
    rewrite -(mul_inv1 x).
    rewrite -mul_assoc0.
    rewrite (inv_mul0 x).
    rewrite (one_mul0 (inv1 x)).
    reflexivity.
  destruct Hinv.

  f_equal; apply proof_irrelevance.
Qed.

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
  apply group'_eq.
  simpl.
  reflexivity.
  simpl.
  apply JMeq_refl.
Qed.

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

(* (2.2).(a) *)
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

(* (2.2).(b) *)
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

(* (2.2).(c).1 *)
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

(* (2.2).(c).2 *)
Theorem subgroup_inv_is_group_inv (G : group) (H : subgroup G) :
  compose (subgroup_incl G H) (group_inv (subgroup_to_group G H))
  = compose (group_inv G) (subgroup_incl G H).
Proof.
  apply functional_extensionality.
  move=> [x Hx].
  unfold compose.
  simpl.

  pose proof (group_inv_ex_uni (subgroup_to_group G H) (exist (subgroup_carrier G H) x Hx)) as Hinv_ex_uni.
  rewrite <- unique_existence in Hinv_ex_uni.
  destruct Hinv_ex_uni as [Hinv_ex Hinv_uni].

  set (inv0 := group_inv (subgroup_to_group G H) (exist (subgroup_carrier G H) x Hx)).
  set (inv1 := (exist (subgroup_carrier G H) (group_inv G (subgroup_incl G H (exist (subgroup_carrier G H) x Hx))) (subgroup_inv_mem G H x Hx))).
  assert (inv0 = inv1) as Hyp0.
  + assert (are_mut_inv (subgroup_to_group G H) (exist (subgroup_carrier G H) x Hx) inv1) as His_inv.
    + split.
      + apply subgroup_incl_is_injective.
        simpl.
        rewrite (group_mul_inv G).
        rewrite (subgroup_one_is_group_one G H).
        reflexivity.
      + apply subgroup_incl_is_injective.
        simpl.
        rewrite (group_inv_mul G).
        rewrite (subgroup_one_is_group_one G H).
        reflexivity.
    + exact (Hinv_uni inv0 inv1 (group_inv_is_group_inv (subgroup_to_group G H) (exist (subgroup_carrier G H) x Hx)) His_inv).

  rewrite Hyp0.
  simpl.
  reflexivity.
Qed.

(* (2.3).1 *)
Definition maximum_subgroup_carrier (G : group) : subset (group_carrier G)
  := fun x => True.

Theorem maximum_subgroup_inhab (G : group) :
  inhabited (sig (maximum_subgroup_carrier G)).
Proof.
  destruct (group_inhab G) as [x].

  assert (maximum_subgroup_carrier G x) as Hyp.
  + unfold maximum_subgroup_carrier.
    exact.
  exact (inhabits (exist (maximum_subgroup_carrier G) x Hyp)).
Qed.

Theorem maximum_subgroup_mul_mem (G : group) :
  forall a b : group_carrier G,
  maximum_subgroup_carrier G a ->
  maximum_subgroup_carrier G b ->
  maximum_subgroup_carrier G (group_mul G a b).
Proof.
  move=> a b Ha Hb.
  unfold maximum_subgroup_carrier.
  exact I.
Qed.

Theorem maximum_subgroup_inv_mem (G : group) :
  forall a : group_carrier G,
  maximum_subgroup_carrier G a ->
  maximum_subgroup_carrier G (group_inv G a).
Proof.
  move=> a Ha.
  unfold maximum_subgroup_carrier.
  exact I.
Qed.

Definition maximum_subgroup (G : group) : subgroup G
  := (make_subgroup G
    (maximum_subgroup_carrier G)
    (maximum_subgroup_inhab G)
    (maximum_subgroup_mul_mem G)
    (maximum_subgroup_inv_mem G)
  ).

(* (2.3).2 *)
Definition minimum_subgroup_carrier (G : group) : subset (group_carrier G)
  := fun x => x = group_one G.

Theorem minimum_subgroup_carrier_sub0 (G : group) :
  forall x : group_carrier G,
  minimum_subgroup_carrier G x
  -> x = group_one G.
Proof.
  move=> x Hx.
  unfold minimum_subgroup_carrier in Hx.
  exact Hx.
Qed.

Theorem minimum_subgroup_inhab (G : group) :
  inhabited (sig (minimum_subgroup_carrier G)).
Proof.
  set (one := group_one G).
  assert (minimum_subgroup_carrier G one) as Hyp.
  + unfold minimum_subgroup_carrier.
    unfold one.
    reflexivity.
  exact (inhabits (exist (minimum_subgroup_carrier G) one Hyp)).
Qed.

Theorem minimum_subgroup_mul_mem (G : group) :
  forall a b : group_carrier G,
  minimum_subgroup_carrier G a ->
  minimum_subgroup_carrier G b ->
  minimum_subgroup_carrier G (group_mul G a b).
Proof.
  unfold minimum_subgroup_carrier.
  move=> a b Ha Hb.
  rewrite Ha Hb.
  rewrite group_mul_one.
  reflexivity.
Qed.

Theorem minimum_subgroup_inv_mem (G : group) :
  forall a : group_carrier G,
  minimum_subgroup_carrier G a ->
  minimum_subgroup_carrier G (group_inv G a).
Proof.
  unfold minimum_subgroup_carrier.
  move=> a Ha.
  rewrite Ha.
  exact (group_one_inv G).
Qed.

Definition minimum_subgroup (G : group) : subgroup G
  := (make_subgroup G
    (minimum_subgroup_carrier G)
    (minimum_subgroup_inhab G)
    (minimum_subgroup_mul_mem G)
    (minimum_subgroup_inv_mem G)
  ).

Definition is_proper_subset (S : Set) (T : subset S) :=
  exists s : S, ~(T s).

(* Definition 2.4 *)
Definition is_proper_subgroup (G : group) (H : subgroup G) :=
  is_proper_subset (group_carrier G) (subgroup_carrier G H).
