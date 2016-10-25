include "SyntaxSharp.dfy"

/* ------ */
/* Subst  */
/* ------ */


/* substitute global var [x] with free identifier [vr] in term [t] */
function subst_mterm (t: term, x: Mident, vr: Ident) : term
{
	match t
		case Tmvalue(v) 		=> t
		case Tmvar(id)			=> t
		case Tmderef(ref)		=> if x.v == t.ref.v then Tmvar(vr) else t
		case Tmbin(op1,op2,op)	=> Tmbin(subst_mterm(t.op1,x,vr),
										 subst_mterm(t.op2,x,vr), 
										 op)
}


/* substitute global var [x] with free identifier [vr] in formula [f] */
function subst_fmla (f: fmla, x: Mident, vr: Ident) : fmla
{
	match f
		case Fterm(t)			=>	Fterm(subst_mterm(f.t,x,vr))
		case Fand(a1,a2)		=>	Fand(subst_fmla(f.a1,x,vr),subst_fmla(f.a2,x,vr))
		case Fnot(n1)			=>	Fnot(subst_fmla(f.n1,x,vr))
		case Fimplies(i1,i2)	=>	Fimplies(subst_fmla(f.i1,x,vr),subst_fmla(f.i2,x,vr))
		case Flet(id,expr,fm)	=> 	Flet(f.id, subst_mterm(f.expr,x,vr), subst_fmla(f.fm,x,vr))
		case Fforall(v,ty,f1)	=>	Fforall(f.v,f.ty,subst_fmla(f.f1,x,vr))
}

/* whether identifier [vr] is fresh in term [t] */
predicate fresh_in_term(vr: Ident, t: term)
{
	match t
		case Tmvalue(v) 		=> true
		case Tmvar(id)			=> t.id.v != vr.v
		case Tmderef(ref)		=> true
		case Tmbin(op1,op2,op)	=> fresh_in_term(vr, t.op1) && fresh_in_term(vr, t.op2) 
}

/* whether identifier [vr] is fresh in formula [f] */
predicate fresh_in_fmla(vr: Ident, f:fmla)
 decreases f;
{
	match f
		case Fterm(t)			=>	fresh_in_term(vr, f.t)
		case Fand(a1,a2)		=>	fresh_in_fmla(vr, f.a1) && fresh_in_fmla(vr, f.a2)
		case Fnot(n1)			=>  fresh_in_fmla(vr, f.n1)
		case Fimplies(i1,i2)	=>	fresh_in_fmla(vr, f.i1) && fresh_in_fmla(vr, f.i2)
		case Flet(id,expr,fm)	=>  f.id.v != vr.v && fresh_in_term(vr, f.expr) && fresh_in_fmla(vr, f.fm)
		case Fforall(v,ty,f1)	=>	vr.v != f.v.v && fresh_in_fmla(vr, f.f1)
}



