Require Import typing.
From Coq Require Import ssreflect Relations.Relation_Operators.
From Hammer Require Import Tactics.

Definition candidate (P : tm 0 0 -> Prop) : Prop :=
  forall a b, Red a b -> P b -> P a.

Definition candidate_assn m := fin m -> tm 0 0 -> Prop.

Definition ty_assn m := fin m -> ty 0.

Definition candidate_assn_ok {m} (η : candidate_assn m) :=
  forall i, candidate (η i).

Definition Reds {n m} := clos_refl_trans_1n (tm n m) Red.

Fixpoint I {m} (A : ty m)
  (η : candidate_assn m) (a : tm 0 0) : Prop :=
  match A with
  | Bot => False
  | Unit => Reds a unit
  | var_ty i => η i a
  | Fun A B => forall b, I A η b -> I B η (App a b)
  | Forall A => forall B P, candidate P -> I A (P .: η) (TApp a B)
  end.

Lemma I_renaming_iff {m} (A : ty m)
  (η0 : candidate_assn m) (a : tm 0 0) :
  forall n (η1 : candidate_assn n)
    (ξ : fin m -> fin n),
    (forall i, η0 i = η1 (ξ i)) ->
    I A η0 a <-> I (ren_ty ξ A) η1 a.
Proof.
  move : η0 a.
  elim : m / A.
  - qauto l:on.
  - hauto q:on.
  - move => n A ih0 η0 a m η1 ξ hξ.
    split.
    (* Should factor this part out *)
    + move => /= h0 B P hP.
      rewrite -ih0; eauto.
      hauto q:on inv:option.
    + move => /= h0 B P hP.
      rewrite ih0; eauto.
      hauto q:on inv:option.
  - sfirstorder.
  - sfirstorder.
Qed.

Lemma I_weakening_iff {m} (A : ty m)
  (η : candidate_assn m) (a : tm 0 0)
  (P : tm 0 0 -> Prop) (h : candidate P) :
  I A η a <-> I (ren_ty shift A) (P .: η) a.
Proof. by apply I_renaming_iff. Qed.

Lemma I_morphing {m} (A : ty m)
  (η0 : candidate_assn m) (a : tm 0 0) :
  forall n (η1 : candidate_assn n)
    (ξ : fin m -> ty n),
    (forall (i : fin m), forall b, η0 i b <-> I (ξ i) η1 b) ->
    I A η0 a <-> I (subst_ty ξ A) η1 a.
Proof.
  move : η0 a.
  elim : m / A.
  - sfirstorder.
  - hauto l:on.
  - move => n A ihA η0 a m η1 ξ ih0.
    split.
    + move => /= h B P hP.
      rewrite -ihA; eauto.
      destruct i as [i|].
      * simpl.
        asimpl.
        move => b.
        rewrite -I_weakening_iff; eauto.
      * done.
    + move => /= h B P hP.
      rewrite ihA; eauto.
      destruct i as [i|].
      * simpl.
        asimpl.
        move => b.
        rewrite -I_weakening_iff; eauto.
      * done.
  - sfirstorder.
  - sfirstorder.
Qed.

Lemma I_backward_clos {m} (η : candidate_assn m) A a :
  candidate_assn_ok η ->
  I A η a ->
  forall b, Red b a -> I A η b.
Proof.
  elim : A η a.
  - sfirstorder.
  - hauto q:on ctrs:Red.
  - hauto ctrs:Red l:on inv:option unfold:candidate_assn_ok.
  - hauto lq:on ctrs:Red, clos_refl_trans_1n.
  - sfirstorder.
Qed.

Lemma I_backward_clos' {m} (η : candidate_assn m) A a :
  candidate_assn_ok η ->
  I A η a ->
  forall b, Reds b a -> I A η b.
Proof.
  move => ? ? ?.
  induction 1; hauto l:on use:I_backward_clos.
Qed.

Lemma I_candidate {m} (η : candidate_assn m) A :
  candidate_assn_ok η ->
  candidate (I A η).
Proof.
  sauto lq:on use:I_backward_clos' unfold:candidate.
Qed.

Definition tm_assn m := fin m -> tm 0 0.

Definition tm_assn_ok {n m} (γ : tm_assn n) (Γ : context n m) (η : candidate_assn m) :=
  forall (i : fin n), I (Γ i) η (γ i).

Lemma tm_assn_ok_cons {n m} (γ : tm_assn n) (Γ : context n m) (η : candidate_assn m)
  (a : tm 0 0) (A : ty m) :
  I A η a ->
  tm_assn_ok γ Γ η ->
  tm_assn_ok (a .: γ) (A .: Γ) η.
Proof. hauto l:on inv:option unfold:tm_assn, tm_assn_ok. Qed.

Lemma tm_assn_ok_cons_ty {n m} (γ : tm_assn n) (Γ : context n m) (η : candidate_assn m)
  (a : tm 0 0) (P : tm 0 0 -> Prop) :
  candidate P ->
  tm_assn_ok γ Γ η ->
  tm_assn_ok γ (Γ >> ren_ty shift) (P .: η).
Proof.
  move => hP hγ.
  rewrite /tm_assn_ok => i.
  asimpl.
  by apply I_weakening_iff.
Qed.

Definition SemWt {n m} (Γ : context n m) (a : tm n m) (A : ty m) :=
  forall γ δ η, tm_assn_ok γ Γ η -> candidate_assn_ok η -> I A η (subst_tm γ δ a).

Lemma fundamental_lemma {n m} (Γ : context n m) (a : tm n m) (A : ty m)
  (h : Wt Γ a A) : SemWt Γ a A.
Proof.
  elim : n m Γ a A / h.
  - sfirstorder unfold:SemWt, candidate_assn_ok, tm_assn_ok.
  - rewrite /SemWt.
    move => n m Γ A a B h0 ih0 γ δ η hγ hη.
    simpl.
    move => b hb.
    move /(_ (b .: γ) δ η ltac:(hauto l:on use:tm_assn_ok_cons) ltac:(done)) in ih0.
    apply : I_backward_clos; eauto.
    apply R_AppAbs'; by asimpl.
  - hauto l:on unfold:SemWt, candidate_assn_ok, tm_assn_ok.
  - rewrite /SemWt.
    move => n m Γ a A h0 h1 γ δ η hγ hη.
    simpl.
    move => B P hP.
    move /(_ γ (B .: δ) (P .: η)
             ltac:(qauto l:on use:tm_assn_ok_cons_ty)
                    ltac:(sauto unfold:candidate_assn_ok)) in h1.
    apply : I_backward_clos; eauto.
    hauto lq:on inv:option unfold:candidate_assn_ok.
    apply R_TAppAbs'; by asimpl.
  - move => n m Γ a A B h0 ih0.
    rewrite /SemWt in ih0 *.
    move => γ δ η h_γ_ok h_η_ok /=.
    move /(_ γ δ η h_γ_ok h_η_ok) => /= in ih0.
    move /(_ (subst_ty δ B) (I B η) ltac:(hauto l:on use:I_candidate)) in ih0.
    rewrite -I_morphing; eauto.
    hauto lq:on inv:option.
  - sfirstorder.
Qed.

Lemma termination (a : tm 0 0) (h : Wt null a Unit) : Reds a unit.
Proof.
  have h0 : SemWt null a Unit by hauto lq:on use:fundamental_lemma.
  rewrite /SemWt in h0.
  specialize (h0 ids).
  specialize (h0 ids).
  specialize (h0 null).
  move /(_ ltac:(hauto lq:on unfold:tm_assn_ok inv:option)
                  ltac:(hauto lq:on unfold:candidate_assn_ok inv:option)) in h0.
  asimpl in h0.
  sfirstorder.
Qed.
