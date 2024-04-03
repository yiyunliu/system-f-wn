(** * Proof irrelevance model *)
Require Import typing.
From Hammer Require Import Tactics.
From Coq Require Import ssreflect Lia.
From Equations Require Import Equations.


Fixpoint size_ty {m} (A : ty m) :=
  match A with
  | Bot => 1
  | Unit => 1
  | Fun A B => 1 + size_ty A + size_ty B
  | Forall A => 1 + size_ty A
  | var_ty _ => 1
  end.

#[tactic=hauto]
  Equations I {m} (A : ty m) (η : fin m -> Prop) : Prop by wf (size_ty A) lt :=
  I Bot η := False;
  I Unit η := True;
  I (Fun A B) η := I A η -> I B η;
  I (Forall A) η := forall (P : Prop), I A (P .: η);
  I (var_ty i) η := η i.

Lemma I_renaming_iff {m} (A : ty m)
  (η0 : fin m -> Prop):
  forall n (η1 : fin n -> Prop)
    (ξ : fin m -> fin n),
    (forall i, η0 i = η1 (ξ i)) ->
    I A η0 <-> I (ren_ty ξ A) η1.
Proof.
  move : η0.
  elim : m / A.
  - qauto l:on rew:db:I.
  - hauto q:on rew:db:I.
  - move => m A ihA η0 n η1 ξ hξ /=.
    simp I.
    split => h P; [rewrite -ihA | rewrite ihA]; eauto; hauto q:on inv:option.
  - sfirstorder.
  - sfirstorder.
Qed.

Lemma I_weakening_iff {m} (A : ty m)
  (η : fin m -> Prop)
  (P : Prop)  :
  I A η <-> I (ren_ty shift A) (P .: η).
Proof. by apply I_renaming_iff. Qed.

Lemma I_morphing {m} (A : ty m)
  (η0 : fin m -> Prop) :
  forall n (η1 : fin n -> Prop)
    (ξ : fin m -> ty n),
    (forall (i : fin m), η0 i <-> I (ξ i) η1) ->
    I A η0 <-> I (subst_ty ξ A) η1.
Proof.
  move : η0.
  elim : m / A.
  - hauto l:on rew:db:I.
  - hauto l:on rew:db:I.
  - move => n A ihA η0 m η1 ξ ih0 /=.
    split; simp I.
    + move => /= h P.
      rewrite -ihA; eauto.
      destruct i as [i|].
      * simpl.
        asimpl.
        rewrite -I_weakening_iff; eauto.
      * simpl. sfirstorder.
    + move => /= h P.
      rewrite ihA; eauto.
      destruct i as [i|].
      * simpl.
        asimpl.
        rewrite -I_weakening_iff; eauto.
      * hauto l:on rew:db:I.
  - hauto l:on rew:db:I.
  - hauto l:on rew:db:I.
Qed.

Definition η_ok {n m} (η : fin m -> Prop) (Γ : context n m) := forall i, I (Γ i) η.

Lemma η_ok_cons {n m} (η : fin m -> Prop) (Γ : context n m) A :
  η_ok η Γ ->
  I A η ->
  η_ok η (A .: Γ).
Proof. hauto lq:on unfold:η_ok inv:option. Qed.

Definition SemWt {n m} (Γ : context n m) (a : tm n m) (A : ty m) :=
  forall η, η_ok η Γ -> I A η.

Lemma fundamental_lemma {n m} (Γ : context n m) (a : tm n m) (A : ty m)
  (h : Wt Γ a A) : SemWt Γ a A.
  elim : n m Γ a A / h.
  - hauto lq:on unfold:η_ok, SemWt.
  - move => n m Γ A a B _ ha η hη.
    simp I => ?.
    by have /ha : η_ok η (A .: Γ) by eauto using η_ok_cons.
  - hauto lq:on unfold:SemWt rew:db:I.
  - move => n m Γ a A _ ha η hη.
    simp I => P.
    suff /ha : η_ok (P .: η) (Γ >> ren_ty shift) by done.
    rewrite /η_ok.
    move => i. asimpl.
    by rewrite -I_weakening_iff.
  - move => n m Γ a A B _ ha η hη.
    rewrite /SemWt in ha.
    move /ha : (hη) {ha}.
    simp I.
    rewrite -I_morphing; eauto.
    destruct i as [i|]=>//.
    hauto l:on.
  - hauto l:on unfold:SemWt rew:db:I.
Qed.

Lemma false_is_impossible a :
  ~ Wt (null : context 0 0) a (Forall (var_ty var_zero)).
Proof.
  move /fundamental_lemma => h.
  rewrite /SemWt in h.
  move : h.
  have η : fin 0 -> Prop by move => [].
  move /(_ η).
  simp I. apply.
  rewrite /η_ok. move => [].
Qed.
