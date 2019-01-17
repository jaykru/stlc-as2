tm: Type
ty : Type
bool : ty
arrow : ty -> ty -> ty
				   
app : tm -> tm -> tm
lam : ty -> (tm -> tm) -> tm

ttrue : tm
tfalse : tm
tif : tm -> tm -> tm -> tm
