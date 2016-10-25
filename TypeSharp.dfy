include "SyntaxSharp.dfy"
include "SemanticsSharp.dfy"


/* ------ */
/* Type   */
/* ------ */

function type_value(v: Val): Dtype
{
	match v
		case Vnull => Dunit
		case Vint(i) => Dint
		case Vbool(b) => Dbool
}

function get_reftype(ref: Mident, tenv: map<int, Dtype>): Dtype
{
	if(ref.v in tenv) then tenv[ref.v] else Dunit
}

function get_vartype(id: Ident, tstack: seq<prod<int, Dtype>>): Dtype
{
	if tstack == [] then
		Dunit
	else
		if id.v == first(tstack[0]) then second(tstack[0]) else get_vartype(id, tstack[1..])
}


/* check the types in [env/stack] is in consistent with [type env/stack]*/
predicate compatible( env: map<int,Val>,  stack: seq<prod<int, Val>>,
					 tenv: map<int,Dtype>, tstack: seq<prod<int, Dtype>>)
{
     forall ref: Mident :: type_value(get_env(ref, env)) == get_reftype(ref, tenv)
 &&  forall v: Ident :: type_value(get_stack(v, stack)) == get_vartype(v, tstack)
}

predicate compatible_env(env: map<int,Val>, tenv: map<int,Dtype>)
{
     forall ref: Mident :: type_value(get_env(ref, env)) == get_reftype(ref, tenv)  
}

predicate compatible_stack(stack: seq<prod<int, Val>>, tstack: seq<prod<int, Dtype>>)
{
	forall v: Ident :: type_value(get_stack(v, stack)) == get_vartype(v, tstack)
}

function type_operator(op: operator, t1: Dtype, t2: Dtype): Dtype
{
	if (op.Oplus? && t1.Dint? && t2.Dint?) then Dint
	else if (op.Ominus? && t1.Dint? && t2.Dint?) then Dint
	else if (op.Omulti? && t1.Dint? && t2.Dint?) then Dint
	else if (op.Ole? && t1.Dint? && t2.Dint?) then Dbool
	else 	Dunit
}

function type_term(tenv: map<int,Dtype>, tstack: seq<prod<int, Dtype>>, t:term) : Dtype
{
	match t 
		case Tmvalue(v) 		=>	type_value(t.v)
		case Tmvar(id)    		=>	get_vartype(t.id, tstack) 
		case Tmderef(ref)		=>	get_reftype(t.ref, tenv) 
		case Tmbin(op1,op2,op)	=>	type_operator(t.op, 
												  type_term(tenv, tstack, t.op1), 
												  type_term(tenv, tstack, t.op2))
}

predicate type_fmla(tenv: map<int, Dtype>, tstack: seq<prod<int, Dtype>>, f: fmla)
  decreases f;
{
	match f
		case Fterm(t)	=>	type_term(tenv,tstack,f.t) == Dbool
		case Fand(a1,a2) =>	type_fmla(tenv,tstack,f.a1) && type_fmla(tenv,tstack,f.a2)
		case Fnot(n1)	=>	type_fmla(tenv,tstack,f.n1)
		case Fimplies(i1,i2)	=> type_fmla(tenv,tstack,f.i1) && type_fmla(tenv,tstack,f.i2)
		case Flet(id,expr,fm)	=> type_fmla(tenv,[pair(id.v, type_term(tenv,tstack,expr))]+tstack,f.fm)
		case Fforall(v,ty,f1)	=>	type_fmla(tenv,[pair(f.v.v,f.ty)]+tstack,f.f1)
}



predicate type_stmt(tenv: map<int, Dtype>, tstack: seq<prod<int, Dtype>>, s: stmt)
{
	s.Sskip?
||	(s.Sseq? && type_stmt(tenv,tstack,s.s1) && type_stmt(tenv,tstack,s.s2))
||	(s.Sassign? && ( get_reftype(s.id,tenv) == type_term(tenv,tstack,s.expr)))
||	(s.Sif? && type_term(tenv,tstack,s.grd)==Dbool && type_stmt(tenv,tstack,s.thn) && type_stmt(tenv,tstack,s.els))
||	(s.Sassert? && type_fmla(tenv,tstack,s.fm))
||	(s.Swhile? && type_term(tenv,tstack,s.cond)==Dbool && type_stmt(tenv,tstack,s.body) && type_fmla(tenv,tstack,s.inv))
}


