From Coq Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics Hammer.
From Coq Require Import
  micromega.Lia Relation_Operators Operators_Properties.
From WR Require Export syntax.
From Coq Require Import Relations.Relation_Operators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition context n m := fin n -> ty m.

(* Statics *)
Inductive Wt {n m} (Γ : context n m) : tm n m -> ty m -> Prop :=
| T_Var i :
  (* ----------- *)
  Wt Γ (var_tm i) (Γ i)

| T_Abs A a B :
  Wt (A .: Γ) a B ->
  (* ----------------- *)
  Wt Γ (Lam A a) (Fun A B)

| T_App a A B b :
  Wt Γ a (Fun A B) ->
  Wt Γ b A ->
  (* ---------- *)
  Wt Γ (App a b) B

| T_TAbs a A :
  Wt (Γ >> ren_ty shift) a A ->
  (* ------------------------ *)
  Wt Γ (TLam a) (Forall A)

| T_TApp a A B :
  Wt Γ a (Forall A) ->
  (* ------------------------------ *)
  Wt Γ (TApp a B) (subst_ty (B..) A)

| T_Unit :
  (* ---------------------- *)
  Wt Γ unit Unit.

#[export]Hint Constructors Wt : core.

Lemma T_TApp' {n m} (Γ : context n m) a A B0 B :
  B0 = (subst_ty (B..) A) ->
  Wt Γ a (Forall A) ->
  Wt Γ (TApp a B) B0.
Proof. qauto ctrs:Wt. Qed.

Lemma T_Var' {n m} ( Γ : context n m) i A :
  A = Γ i ->
  (* ----------- *)
  Wt Γ (var_tm i) A.
Proof. move => *; subst; auto. Qed.

Definition is_renaming {n m n' m'}
  (Γ : context n m)
  (Δ : context n' m')
  (ξ0 : fin n -> fin n')
  (ξ1 : fin m -> fin m') :=
  forall (i : fin n),
    ren_ty ξ1 (Γ i) = Δ (ξ0 i).

Definition is_renaming_lam_ext {n m n' m'}
  (Γ : context n m)
  (Δ : context n' m')
  (ξ0 : fin n -> fin n')
  (ξ1 : fin m -> fin m')
  A :
  is_renaming Γ Δ ξ0 ξ1 ->
  is_renaming (A .: Γ) (ren_ty ξ1 A .: Δ) (upRen_tm_tm ξ0) (upRen_tm_ty ξ1).
Proof. hauto lq:on rew:off inv:option unfold:is_renaming. Qed.

Definition is_renaming_tlam_ext {n m n' m'}
  (Γ : context n m)
  (Δ : context n' m')
  (ξ0 : fin n -> fin n')
  (ξ1 : fin m -> fin m')
  (h : is_renaming Γ Δ ξ0 ξ1) :
  is_renaming (Γ >> ren_ty shift) (Δ >> ren_ty shift) (upRen_ty_tm ξ0) (upRen_ty_ty ξ1).
Proof.
  move : h.
  rewrite /is_renaming => h i.
  asimpl.
  rewrite -h.
  by asimpl.
Qed.

#[export]Hint Unfold is_renaming : core.
#[export]Hint Resolve is_renaming_lam_ext : core.

Lemma renaming {n m} a A
  (Γ : context n m)
  (h : Wt Γ a A) :
  forall n' m'
  (ξ0 : fin n -> fin n')
  (ξ1 : fin m -> fin m')
  (Δ : context n' m'),
  is_renaming Γ Δ ξ0 ξ1 ->
  Wt Δ (ren_tm ξ0 ξ1 a) (ren_ty ξ1 A).
Proof.
  elim : n m Γ a A / h.
  - hauto lq:on ctrs:Wt unfold:is_renaming.
  - move => * /=; eauto using is_renaming_lam_ext.
  - hauto q:on ctrs:Wt.
  - move => * /=; eauto using is_renaming_tlam_ext.
  - move => * /=.
    apply : T_TApp'; eauto.
    by asimpl.
  - sfirstorder.
Qed.

Lemma weakening_tm {n m} a A
  (Γ : context n m)
  (h : Wt Γ a A)
  (B : ty m) :
  Wt (B .: Γ) (ren_tm shift id a) A.
Proof.
  replace A with (ren_ty id A); last by asimpl.
  apply renaming with (Γ := Γ); auto.
  rewrite /is_renaming => i.
  by asimpl.
Qed.

Definition is_morphing {n m n' m'}
  (Γ : context n m)
  (Δ : context n' m')
  (ξ0 : fin n -> tm n' m')
  (ξ1 : fin m -> ty m') :=
  forall (i : fin n),
    Wt Δ (ξ0 i) (subst_ty ξ1 (Γ i)).

Lemma up_tm_ty_is_id {n m}
  (ξ : fin n -> ty m) :
  up_tm_ty ξ = ξ.
  by asimpl. Qed.

Definition is_morphing_lam_ext {n m n' m'}
  (Γ : context n m)
  (Δ : context n' m')
  (ξ0 : fin n -> tm n' m')
  (ξ1 : fin m -> ty m')
  A :
  is_morphing Γ Δ ξ0 ξ1 ->
  is_morphing (A .: Γ) (subst_ty ξ1 A .: Δ) (up_tm_tm ξ0) ξ1.
Proof.
  rewrite /is_morphing => h.
  destruct i as [i|].
  - simpl.
    asimpl.
    eauto using weakening_tm.
  - asimpl.
    simpl.
    apply T_Var'; by asimpl.
Qed.

Definition is_morphing_tlam_ext {n m n' m'}
  (Γ : context n m)
  (Δ : context n' m')
  (ξ0 : fin n -> tm n' m')
  (ξ1 : fin m -> ty m') :
  is_morphing Γ Δ ξ0 ξ1 ->
  is_morphing (Γ >> ren_ty shift) (Δ >> ren_ty shift) (up_ty_tm ξ0) (up_ty_ty ξ1).
Proof.
  rewrite /is_morphing => h i.
  asimpl.
  move /(_ i) in h.
  apply renaming with (ξ0 := id) (ξ1 := shift) (Δ := Δ >> ren_ty shift) in h;
    [by asimpl in h | sfirstorder unfold:is_renaming].
Qed.

Lemma morphing {n m} a A
  (Γ : context n m)
  (h : Wt Γ a A) :
  forall n' m'
    (ξ0 : fin n -> tm n' m')
    (ξ1 : fin m -> ty m')
    (Δ : context n' m'),
    is_morphing Γ Δ ξ0 ξ1 ->
    Wt Δ (subst_tm ξ0 ξ1 a) (subst_ty ξ1 A).
Proof.
  elim : n m Γ a A / h.
  - sfirstorder unfold:is_morphing ctrs:Wt.
  - move => n m Γ A a B h0 ih0 * /=.
    apply T_Abs.
    rewrite up_tm_ty_is_id.
    eauto using is_morphing_lam_ext.
  - hauto q:on ctrs:Wt.
  - move => n m Γ a A h0 ih0 n' m' ξ0 ξ1 Δ hξ /=.
    apply T_TAbs.
    eauto using is_morphing_tlam_ext.
  - move => * /=.
    apply : T_TApp'; eauto; by asimpl.
  - sfirstorder.
Qed.

Lemma Wt_subst_tm {n m} a b A B
  (Γ : context n m)
  (h0 : Wt (A .: Γ) a B)
  (h1 : Wt Γ b A) :
  Wt Γ (subst_tm (b..) ids a) B.
Proof.
  replace B with (subst_ty ids B); last by asimpl.
  apply morphing with (Γ := A .: Γ) (ξ0 := b..) (ξ1 := ids); first done.
  rewrite /is_morphing.
  destruct i as [i|].
  - apply T_Var'; by asimpl.
  - simpl; asimpl; done.
Qed.

Lemma Wt_subst_ty {n m} a A (B : ty m)
  (Γ : context n m)
  (h0 : Wt (Γ >> ren_ty shift) a A) :
  Wt Γ (subst_tm ids (B..) a) (subst_ty (B..) A).
Proof.
  apply : morphing; first by eassumption.
  move => i /=.
  apply T_Var'; by asimpl.
Qed.

(* Dynamics *)
Inductive Red {n m} : tm n m -> tm n m -> Prop :=
| R_App a0 a1 b :
  Red a0 a1 ->
  Red (App a0 b) (App a1 b)
| R_AppAbs A a b :
  Red (App (Lam A a) b) (subst_tm (b..) ids a)
| R_TApp a b A :
  Red a b ->
  Red (TApp a A) (TApp b A)
| R_TAppAbs a A :
  Red (TApp (TLam a) A) (subst_tm ids (A..) a).

#[export]Hint Constructors Red : core.

Lemma R_AppAbs' {n m} (A : ty m) (a : tm (S n) m) b0 b :
  b0 = subst_tm (b..) ids a ->
  Red (App (Lam A a) b) b0.
Proof. hauto lq:on ctrs:Red. Qed.

Lemma R_TAppAbs' {n m} (a : tm n (S m)) A b :
  b = (subst_tm ids (A..) a) ->
  Red (TApp (TLam a) A) b.
Proof. hauto lq:on ctrs:Red. Qed.

Lemma preservation {n m} (Γ : context n m) a b A
  (h : Red a b) :
  Wt Γ a A ->
  Wt Γ b A.
Proof.
  move : Γ A.
  elim : a b / h.
  - hauto lq:on inv:Wt ctrs:Wt.
  - hauto lq:on use:Wt_subst_tm inv:Wt.
  - hauto lq:on inv:Wt ctrs:Wt.
  - hauto lq:on use:Wt_subst_ty ctrs:Wt inv:Wt.
Qed.

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
