From mathcomp
  Require Import ssreflect.
Require Import Coq.Logic.JMeq.
Require Import Coq.Logic.EqdepFacts.

(* fooのようなRecordは等値性を簡単に証明できる *)

Record foo := make_foo
{
  foo_carrier : Set;
}.

Theorem foo_eq (F F' : foo) :
  foo_carrier F = foo_carrier F'
  -> F = F'.
Proof.
  move=> Hcarrier.
  destruct F, F'.
  simpl in * |-.
  f_equal.
  exact Hcarrier.
Qed.

(* barのようなRecordはfooと同じようには等値性の証明ができない？ *)

Record bar := make_bar
{
  bar_carrier : Set;
  bar_star : bar_carrier;
}.

Theorem bar_eq (B B' : bar) :
  bar_carrier B = bar_carrier B'
  -> JMeq (bar_star B) (bar_star B')
  -> B = B'.
Proof.
  destruct B as [Bcarrier Bstar].
  destruct B' as [B'carrier B'star].
  simpl.
  move=> Hcarrier Hstar.
  pose proof (JMeq_eq_dep (U := Set) (fun X => X) Hcarrier Hstar) as Heq.
  apply eq_dep_eq_sigT in Heq.
  dependent rewrite Heq.
  reflexivity.
Qed.
