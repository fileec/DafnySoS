include "SyntaxSharp.dfy"
include "SemanticsSharp.dfy"
include "TypeSharp.dfy"
include "DataStructures.dfy"




/* Lemma type_inversion */
ghost method type_inversion(v: Val)
  ensures match type_value(v)
		case Dunit => v == Vnull
		case Dint  => exists i: int :: v == Vint(i)
		case Dbool => exists b: bool :: v == Vbool(b)
  ;
{}

/* TODO: WHY INDUCT ON [ty] (seems necessary when in Tmbin case) ?*/
/* In here, we use an variation of [compatible], for Dafny cannot prove the reverse order of that conjunction (under which the manual [destruct] is needed). */
ghost method {:induction t,ty} eval_type_term(
			    t: term,   env : map<int, Val>,    stack: seq<prod<int, Val>>, 
				ty: Dtype, tenv: map<int, Dtype>, tstack: seq<prod<int, Dtype>>)
  ensures (compatible_env(env, tenv) && compatible_stack(stack, tstack)) ==>
			(type_term(tenv, tstack, t) == ty) ==> 
				(type_value(eval_term(env, stack, t)) == ty);
{} 


ghost method {:induction expr} Lemma(
	env : map<int, Val>, stack: seq<prod<int, Val>>, expr: term,
	tenv: map<int, Dtype>, tstack: seq<prod<int, Dtype>>)
 requires compatible_env(env, tenv);
 requires compatible_stack(stack, tstack);
 ensures type_value(eval_term(env,stack,expr)) == type_term(tenv,tstack,expr);
{}


ghost method {:induction s, step(env, stack, s)} step_type_preservation (
	env : map<int, Val>, stack: seq<prod<int, Val>>, s: stmt,
	tenv: map<int, Dtype>, tstack: seq<prod<int, Dtype>>)
  requires step(env, stack, s).conf?;
  requires compatible_env(env, tenv) && compatible_stack(stack, tstack);
  requires type_stmt(tenv, tstack, s);
  ensures var c := step(env, stack, s);
			type_stmt(tenv, tstack, c.st) && compatible_env(c.env, tenv) && compatible_stack(c.stack, tstack);
{

	var c := step(env, stack, s);
	if(c.st.Sskip?){
		if(s.Sassign?){		
			Lemma(env,stack,s.expr,tenv,tstack);
		}
		
	}
}






