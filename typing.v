From Coq Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics.
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
  Wt Γ (TApp a B) (subst_ty (B..) A).

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
