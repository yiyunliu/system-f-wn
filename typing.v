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
  Wt Γ (App a b) B
| T_TAbs a A :
  Wt (Γ >> ren_ty shift) a A ->
  Wt Γ (TLam a) (Forall A)
| T_TApp a A B :
  Wt Γ a (Forall A) ->
  Wt Γ (TApp a B) (subst_ty (B..) A).

Lemma renaming {n m}
  (Γ : context n m)
  (ξ : fin n -> )
