include "SyntaxSharp.dfy"
include "SemanticsSharp.dfy"
include "DataStructures.dfy"





/* Lemma steps_non_neg */
ghost method steps_non_neg(env  :map<int,Val>, stack  :seq<prod<int, Val>>, s  :stmt, 
						   env'':map<int,Val>, stack'':seq<prod<int, Val>>, s'':stmt, n: int)
  ensures (multi_steps(env, stack, s, env'', stack'', s, n) ==> n>=0);
{}




