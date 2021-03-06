From mathcomp
  Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition mySet (M : Type) := M -> Prop.
Definition belong {M : Type} (A : mySet M) (x : M) :
  Prop := A x.
Notation "x ∊ A" := (belong A x) (at level 11).
Axiom axiom_mySet : forall (M : Type) (A : mySet M),
  forall (x : M), (x ∊ A) \/ ~(x ∊ A).

Definition myEmptySet {M : Type} : mySet M := fun _ => False.
Definition myMotherSet {M : Type} : mySet M := fun _ => True.

Definition mySub {M} := fun (A B : mySet M) =>
  (forall (x : M), (x ∊ A) -> (x ∊ B)).
Notation "A ⊂ B" := (mySub A B) (at level 11).

Section 包含関係.
Variable M : Type.

Lemma Sub_Mother (A : mySet M) : A ⊂ myMotherSet.
Proof. by []. Qed.

Lemma Sub_Empty (A : mySet M) : myEmptySet ⊂ A.
Proof. by []. Qed.

Lemma rfl_Sub (A : mySet M) : (A ⊂ A).
Proof. by []. Qed.

Lemma transitive_Sub (A B C : mySet M) :
  (A ⊂ B) -> (B ⊂ C) -> (A ⊂ C).
Proof. by move=> H1 H2 t H3; apply: H2; apply: H1. Qed.

End 包含関係.

Definition eqmySet {M : Type} :=
  fun (A B : mySet M)=> (A ⊂ B /\ B ⊂ A).
Axiom axiom_ExteqmySet : forall {M : Type} (A B : mySet M),
  eqmySet A B -> A = B.

Section 等号.
Variable Mother : Type.

Lemma rfl_eqS (A : mySet Mother) : A = A.
Proof. by []. Qed.

Lemma sys_eqS (A B : mySet Mother) : A = B -> B = A.
Proof. move=> H. by rewrite H. Qed.

End 等号.

Definition myComplement {M : Type} (A : mySet M) : mySet M :=
  fun (x : M) => ~(A x).
Notation "A ^c" := (myComplement A) (at level 11).

Definition myCup {M : Type} (A B : mySet M) : mySet M :=
  fun (x : M) => (x ∊ A) \/ (x ∊ B).
Notation "A ∪ B" := (myCup A B) (at level 11).

Section 演算.
Variable M : Type.

Lemma cEmpty_Mother : (@myEmptySet M)^c = myMotherSet.
Proof.
apply: axiom_ExteqmySet; rewrite /eqmySet.
by apply: conj; rewrite /mySub /myComplement // => x Hfull.
Qed.

Lemma cc_cancel (A : mySet M) : (A^c)^c = A.
apply: axiom_ExteqmySet; rewrite /eqmySet.
apply: conj; rewrite /mySub /myComplement => x H //.
by case: (axiom_mySet A x).
Qed.

Lemma cMother_Empty : (@myMotherSet M)^c = myEmptySet.
Proof. by rewrite -cEmpty_Mother cc_cancel. Qed.

Lemma myCupA (A B C : mySet M) : (A ∪ B) ∪ C = A ∪ (B ∪ C).
Proof.
apply: axiom_ExteqmySet.
rewrite /eqmySet /mySub.
apply: conj => x [H1 | H2].
- case: H1 => t.
  + by apply: or_introl.
  + by apply: or_intror; apply: or_introl.
- by apply: or_intror; apply: or_intror.
- by apply: or_introl; apply: or_introl.
- case: H2 => t.
  + by apply: or_introl; apply: or_intror.
  + by apply: or_intror.
Qed.

Lemma myUnionCompMother (A : mySet M) : A ∪ (A^c) = myMotherSet.
Proof.
apply: axiom_ExteqmySet; rewrite /eqmySet /mySub; apply: conj => [x | x HM].
- by case.
- by case: (axiom_mySet A x); [apply: or_introl | apply: or_intror].
Qed.
End 演算.
