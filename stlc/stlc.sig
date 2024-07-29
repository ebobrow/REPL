tm : Type
ty : Type

tmapp : tm -> tm -> tm
tmabs : ty -> (tm -> tm) -> tm
tmtrue : tm
tmfalse : tm
tmif : tm -> tm -> tm -> tm

tyarr : ty -> ty -> ty
tybool : ty
