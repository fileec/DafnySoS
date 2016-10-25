include "SyntaxSharp.dfy"
include "SemanticsSharp.dfy"
include "Substitution.dfy"
include "DataStructures.dfy"


/* the bug seems related with injective of datatype 
	might be move to [type] from [datatype] for Mident
*/
ghost method {:induction e} eval_subst_mterm 
	(e: term, x: Mident, v: Ident, 
	 env:map<int,Val>,stack:seq<prod<int,Val>>)
  requires fresh_in_term(v,e);
  ensures 
  eval_term(env,stack,subst_mterm(e,x,v)) == 
	eval_term(env[x.v:=get_stack(v,stack)],stack,e);
{}

/* induction on f make the verification worse, seems cause a loop */
ghost method eval_subst_fmla 
	(f: fmla, x: Mident, v: Ident, 
	 env:map<int,Val>,stack:seq<prod<int,Val>>)
  requires fresh_in_fmla(v,f);
  ensures 
  eval_fmla(env,stack,subst_fmla(f,x,v)) <==> 
	eval_fmla(env[x.v:=get_stack(v,stack)],stack,f);
{
	if(f.Fterm?){
		if(f.t.Tmbin?){
			eval_subst_mterm(f.t,x,v,env,stack);
		}	
	}else if(f.Flet?){
		eval_subst_mterm(f.expr,x,v,env,stack);
	}
}

ghost method {:induction t} eval_term_change_free(
id: Ident, v: Val, t: term,
env:map<int,Val>, stack:seq<prod<int,Val>>)
  requires fresh_in_term(id, t);
  ensures  eval_term(env,[pair(id.v,v)]+stack,t) == eval_term(env,stack,t);
{}

/* TODO: NOT FINISHED */
ghost method {:induction f} eval_fmla_change_free(
id: Ident, v: Val, f: fmla,
env:map<int,Val>, stack:seq<prod<int,Val>>)
  requires fresh_in_fmla(id, f);
  free ensures  eval_fmla(env,[pair(id.v,v)]+stack,f) <==> eval_fmla(env,stack,f);
{
	if(f.Fterm?){
		eval_term_change_free(id,v,f.t,env,stack);
	}else if(f.Flet?){
	
		
	//eval_fmla_change_free2(id,v,f.fm,env,stack);
	//assert eval_fmla(env,[pair(id.v,v)]+stack,f) <==> eval_fmla(env,stack,f);
	}else if(f.Fforall?){
		
		if(f.ty.Dunit?){
			// expand def. eval_fmla
			assert eval_fmla(env,[pair(f.v.v, Vnull)]+stack,f.f1) <==> eval_fmla(env,stack,f); 
			assert eval_fmla(env,[pair(f.v.v, Vnull)]+([pair(id.v,v)]+stack),f.f1) <==> eval_fmla(env,[pair(id.v,v)]+stack,f);
			
			// invoke swap_equiv lemma
			eval_swap_fmla(f.v,id,Vnull,v,f.f1,env,[],stack);
			assert eval_fmla(env,[pair(id.v,v)]+[pair(f.v.v, Vnull)]+stack,f.f1) <==>
			eval_fmla(env,[pair(f.v.v, Vnull)]+[pair(id.v,v)]+stack,f.f1);
			
			// invoke induction hypothesis
			eval_fmla_change_free(id,v,f.f1,env,[pair(f.v.v, Vnull)]+stack);
			assert eval_fmla(env,[pair(id.v,v)]+([pair(f.v.v, Vnull)]+stack),f.f1) <==> eval_fmla(env,[pair(f.v.v, Vnull)]+stack,f.f1);
			// hint dafny seq+ is associative
			assert [pair(id.v,v)]+([pair(f.v.v, Vnull)]+stack) == [pair(id.v,v)]+[pair(f.v.v, Vnull)]+stack;
			assert eval_fmla(env,[pair(id.v,v)]+([pair(f.v.v, Vnull)]+stack),f.f1) <==> eval_fmla(env,[pair(id.v,v)]+[pair(f.v.v, Vnull)]+stack,f.f1);
			assert eval_fmla(env,[pair(f.v.v, Vnull)]+[pair(id.v,v)]+stack,f.f1) <==> eval_fmla(env,[pair(f.v.v, Vnull)]+stack,f.f1);
			// hint dafny seq+ is associative
			assert [pair(f.v.v, Vnull)]+[pair(id.v,v)]+stack == [pair(f.v.v, Vnull)]+([pair(id.v,v)]+stack);
			
			assert eval_fmla(env,stack,f) <==> eval_fmla(env,[pair(id.v,v)]+stack,f);
			
			
			
			
		}
		
		
		
	}


}


predicate in_stack(id: Ident, stack: seq<prod<int, Val>>)
{
	if stack == [] then
		false
	else
		if id.v == first(stack[0]) then true else in_stack(id, stack[1..])
}

ghost method Lists_Lemma(id: Ident, Stk: seq<prod<int, Val>>, rest: seq<prod<int,Val>>)
	free ensures in_stack(id,Stk) ==> get_stack(id, Stk+rest) == get_stack(id, Stk);
	free ensures !in_stack(id,Stk) ==> get_stack(id,Stk+rest) == get_stack(id,rest);
{

}


 // something wrong with the list concatation
ghost method {:induction t} eval_swap_term(
id1: Ident, id2: Ident, v1: Val, v2: Val, t: term,
env:map<int,Val>, hdStk:seq<prod<int,Val>>, tlStk: seq<prod<int,Val>>)
  requires id1 != id2;
  ensures eval_term(env, hdStk+[pair(id1.v,v1)]+[pair(id2.v,v2)]+tlStk, t) ==
		  eval_term(env, hdStk+[pair(id2.v,v2)]+[pair(id1.v,v1)]+tlStk, t);
{
	if(t.Tmvar?){
		if(hdStk == []){
			assert get_stack(t.id, [pair(id1.v,v1)]+[pair(id2.v,v2)]+tlStk) == 
		get_stack(t.id, [pair(id2.v,v2)]+[pair(id1.v,v1)]+tlStk);	
			
		}else{
			// Tools have trouble to understand seq concat is right assoc.
			assert hdStk+([pair(id2.v,v2)]+[pair(id1.v,v1)]+tlStk) ==
				hdStk+[pair(id2.v,v2)]+[pair(id1.v,v1)]+tlStk;
				
			assert hdStk+([pair(id1.v,v1)]+[pair(id2.v,v2)]+tlStk) ==
			hdStk+[pair(id1.v,v1)]+[pair(id2.v,v2)]+tlStk;
				
			var s1 := [pair(id1.v,v1)]+[pair(id2.v,v2)]+tlStk;
			var s2 := [pair(id2.v,v2)]+[pair(id1.v,v1)]+tlStk;		
			Lists_Lemma(t.id, hdStk, s1);
			Lists_Lemma(t.id, hdStk, s2);	
			
			if(!in_stack(t.id, hdStk)){
				assert get_stack(t.id,s1) == get_stack(t.id,s2);
			}
			
		}	
	}
}


ghost method {:induction f} eval_swap_fmla(
id1: Ident, id2: Ident, v1: Val, v2: Val, f: fmla,
env:map<int,Val>, hdStk:seq<prod<int,Val>>, tlStk: seq<prod<int,Val>>)
  requires id1 != id2;
  free ensures eval_fmla(env, hdStk+[pair(id1.v,v1)]+[pair(id2.v,v2)]+tlStk, f) <==>
		  eval_fmla(env, hdStk+[pair(id2.v,v2)]+[pair(id1.v,v1)]+tlStk, f);