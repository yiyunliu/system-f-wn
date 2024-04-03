tm : Type
ty : Type

Lam : ty -> (tm -> tm) -> tm
App : tm -> tm -> tm
TLam : (ty -> tm) -> tm
TApp : tm -> ty -> tm
unit : tm
bot  : tm

Fun : ty -> ty -> ty
Forall : (ty -> ty) -> ty
Unit : ty
Bot : ty