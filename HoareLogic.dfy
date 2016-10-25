include "SemanticsSharp.dfy"
include "SyntaxSharp.dfy"
include "Substitution.dfy"

/* ------ */
/* HOARE  */
/* ------ */

/* Def. a valid triple is */
predicate valid_triple(
p: fmla, s: stmt, q: fmla)
{
forall env: map<int,Val>, stack:seq<prod<int,Val>> ::
	eval_fmla(env, stack, p) ==> 
		forall env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int ::
			multi_steps(env, stack, s, env'', stack'', Sskip, n) ==> 
				eval_fmla(env'',stack'',q)
}



