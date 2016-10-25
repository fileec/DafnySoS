
include "SyntaxSharp.dfy"
include "DataStructures.dfy"
/* --------------------- */
/* Operational Semantics */
/* --------------------- */


/* 
 Def. program state:	
	- env, the heap
	- stack, the local stack
	- st, the statement to be executed
 */
datatype state =  
  error /* in the case of diverge or exception */
| conf (env:map<int,Val>, stack:seq<prod<int, Val>>, st:stmt)

/* Get the value of a global variable from env */
function get_env(ref: Mident, env: map<int, Val>): Val
{
  if(ref.v in env) then env[ref.v] else Vnull
}

/* Get the value of a local variable from stack */
function get_stack(id: Ident, stack: seq<prod<int, Val>>): Val
{
	if stack == [] then
		Vnull
	else
		if id.v == first(stack[0]) then second(stack[0]) else get_stack(id, stack[1..])
}


/* 
  Evaluate binary operations. 
*/
function eval_bin(x: Val, y: Val, op: operator): Val
{
	if(x.Vint? && y.Vint? && op.Oplus?) then
		Vint(x.i+y.i)
	else if(x.Vint? && y.Vint? && op.Ominus?) then
		Vint(x.i-y.i)
	else if(x.Vint? && y.Vint? && op.Omulti?) then
		Vint(x.i*y.i)
	else if(x.Vint? && y.Vint? && op.Ole?) then
		Vbool(x.i<=y.i)
	else Vnull
}

/* Evaluate a term to a value on a given env and stack */
function eval_term(env: map<int, Val>, stack: seq<prod<int, Val>>, t: term): Val
{
	if(t.Tmvalue?) then
		t.v
	else if(t.Tmvar?) then
		get_stack(t.id, stack)
	else if(t.Tmderef?) then
		get_env(t.ref, env)
	else 
		eval_bin(eval_term(env, stack, t.op1), eval_term(env,stack, t.op2), t.op)
}





/* Evaluate a formula to a bool on a given env and stack */
predicate eval_fmla(env: map<int, Val>, stack: seq<prod<int, Val>>, f: fmla)
  decreases f;
{
	if(f.Fterm?) then
	/* Fterm */			eval_term(env, stack, f.t) == Vbool(true)
	else if(f.Fand?) then
	/* Fand */			eval_fmla(env, stack, f.a1) && eval_fmla(env, stack, f.a2)
	else if(f.Fnot?) then
	/* Fnot */			! eval_fmla(env, stack, f.n1)
	else if(f.Fimplies?) then
	/* Fimplies */		eval_fmla(env, stack, f.i1) ==> eval_fmla(env, stack, f.i2)
	else if(f.Flet?) then
	/* Flet */			eval_fmla(env, [pair(f.id.v, eval_term(env,stack,f.expr))]+stack, f.fm)
	else
	/* FForall */
		if(f.ty.Dint?) then
				forall nVal: int :: eval_fmla(env, [pair(f.v.v, Vint(nVal))]+stack, f.f1)
		else if(f.ty.Dbool?) then
				forall bVal: bool :: eval_fmla(env, [pair(f.v.v, Vbool(bVal))]+stack, f.f1)
		else
				eval_fmla(env, [pair(f.v.v, Vnull)]+stack, f.f1)
}


/* Def. Valid formula. f evaluate to true on all program state. */
predicate valid_fmla(f: fmla)
{
	forall env: map<int, Val>, stack: seq<prod<int, Val>> :: eval_fmla(env, stack, f)
}

/* Small-step operational semantics. */
function step (env:map<int,Val>, stack:seq<prod<int, Val>>, s:stmt) : state
{
	if (s.Sassign?) then	
	/* assign */			conf(env[s.id.v:=eval_term(env,stack,s.expr)], stack, Sskip)
	else if (s.Sseq?  && !s.s1.Sskip?) then
	/* seq_skip_free */ 	var c := step(env, stack, s.s1); 
							match c 
								case error => error
								case conf(env, stack, st) => conf(c.env, c.stack, Sseq(c.st, s.s2))		
	else if (s.Sseq? && s.s1.Sskip? ) then						
	/* seq_skip */			conf(env, stack, s.s2)
	else if (s.Sif? && Vbool(true) == eval_term(env, stack, s.grd) ) then
	/* if_true */			conf(env, stack, s.thn)
	else if (s.Sif? && Vbool(false) == eval_term(env, stack, s.grd) ) then
	/* if_false */     		conf(env, stack, s.els)
	else if (s.Sassert? && eval_fmla(env, stack, s.fm)) then
	/* assert_pass */		conf(env, stack, Sskip)
	else if (s.Swhile? && eval_term(env, stack, s.cond) == Vbool(true) && eval_fmla(env, stack, s.inv)) then
	/* while_true */ 		conf(env, stack, Sseq(s.body, s))
	else if (s.Swhile? && eval_term(env, stack, s.cond) == Vbool(false) && eval_fmla(env, stack, s.inv)) then
	/* while_false */ 		conf(env, stack, Sskip)
	else
	/* Undefined cases*/ 	error
}

/* the reflexive transitive closure of step, manifests all the possible final states (Sskip) a initial state can move into. */
predicate multi_steps
  (env  :map<int,Val>, stack  :seq<prod<int, Val>>, s  :stmt, 
   env'':map<int,Val>, stack'':seq<prod<int, Val>>, s'':stmt,
   n: int)
   decreases n;
{
     /* reflexive  */			(n==0 && env'' == env && stack'' == stack && s''==s )
||   /* transitive */			(n>0 && step(env, stack, s).conf? && var c := step(env, stack, s); multi_steps(c.env, c.stack, c.st, env'', stack'', s'', n-1)) 
}

