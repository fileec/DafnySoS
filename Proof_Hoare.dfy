include "SyntaxSharp.dfy"
include "SemanticsSharp.dfy"
include "DataStructures.dfy"
include "HoareLogic.dfy"
include "Proof_Subst.dfy"


ghost method skip_rule(
q: fmla)
	ensures valid_triple(q,Sskip,q);
{}


ghost method assert_rule(
f: fmla, q: fmla)
  requires valid_fmla(Fimplies(q, f));
  ensures  valid_triple(q, Sassert(f), q);
{

}


// dafny has trouble to expand the definition of eval_fmla(Fand)
ghost method if_rule(
t: term, p: fmla, q: fmla, s1: stmt, s2: stmt)
  requires valid_triple(Fand(p,      Fterm(t)),s1,q);	// H1
  requires valid_triple(Fand(p,Fnot(Fterm(t))),s2,q);	// H2
  ensures  valid_triple(p,Sif(t,s1,s2),q);
{
	// Unfold valid_triple in H1
	assert forall env: map<int,Val>, stack:seq<prod<int,Val>> ::
	eval_fmla(env, stack, Fand(p,      Fterm(t))) ==> 
		forall env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int ::
			multi_steps(env, stack, s1, env'', stack'', Sskip, n) ==> 
				eval_fmla(env'',stack'',q);	

	// important rewriting
	assert forall env: map<int,Val>, stack:seq<prod<int,Val>> ::
	eval_fmla(env, stack, Fand(p,      Fterm(t))) <==> eval_fmla(env, stack, p) && eval_fmla(env, stack, Fterm(t));
	
	// unfold eval_fmla(env, stack, Fand(p,      Fterm(t))) in H1, 
	assert forall env: map<int,Val>, stack:seq<prod<int,Val>> ::
		eval_fmla(env, stack, p) && eval_fmla(env, stack, Fterm(t)) ==> 
		forall env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int ::
			multi_steps(env, stack, s1, env'', stack'', Sskip, n) ==> 
				eval_fmla(env'',stack'',q);	
	
	

	// unfold eval_fmla(env, stack, Fterm(t)) in H1		
	assert forall env: map<int,Val>, stack:seq<prod<int,Val>> ::
	eval_fmla(env, stack, p) && eval_term(env, stack, t) == Vbool(true) ==> 
		forall env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int ::
			multi_steps(env, stack, s1, env'', stack'', Sskip, n) ==> 
					eval_fmla(env'',stack'',q);	
	
	// Unfold valid_triple in H2
	assert forall env: map<int,Val>, stack:seq<prod<int,Val>> ::
	eval_fmla(env, stack, Fand(p,      Fand(p,Fnot(Fterm(t))))) ==> 
		forall env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int ::
			multi_steps(env, stack, s2, env'', stack'', Sskip, n) ==> 
				eval_fmla(env'',stack'',q);	
	
	// important rewriting
	assert forall env: map<int,Val>, stack:seq<prod<int,Val>> ::
	eval_fmla(env, stack, Fand(p, Fand(p,Fnot(Fterm(t))))) <==> eval_fmla(env, stack, p) && eval_fmla(env, stack, Fnot(Fterm(t)));
	
	
	// Unfold Fand(p,      Fand(p,Fnot(Fterm(t)))) in H2
	assert forall env: map<int,Val>, stack:seq<prod<int,Val>> ::
	eval_fmla(env, stack, p) && eval_fmla(env, stack, Fnot(Fterm(t))) ==> 
		forall env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int ::
			multi_steps(env, stack, s2, env'', stack'', Sskip, n) ==> 
				eval_fmla(env'',stack'',q);	
	
	// Unfold eval_fmla(env, stack, Fnot(Fterm(t))) in H2
	assert forall env: map<int,Val>, stack:seq<prod<int,Val>> ::
	eval_fmla(env, stack, p) && eval_term(env, stack, t) == Vbool(false) ==> 
		forall env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int ::
			multi_steps(env, stack, s2, env'', stack'', Sskip, n) ==> 
					eval_fmla(env'',stack'',q);	
										
	// conclusion			
	assert forall env: map<int,Val>, stack:seq<prod<int,Val>> ::
	eval_fmla(env, stack, p) ==> 
		forall env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int ::
			multi_steps(env, stack, Sif(t,s1,s2), env'', stack'', Sskip, n) ==> 
					eval_fmla(env'',stack'',q);			
				
				
}


/* indicate assign_rule is a base case of multi-steps */
ghost method assign_rule_lemma
(env: map<int,Val>, stack:seq<prod<int,Val>> , x: Mident, t: term,
 env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int)
  requires multi_steps(env, stack, Sassign(x,t), env'', stack'', Sskip, n);
  ensures (env''==  env[x.v:=eval_term(env,stack,t)] && stack''== stack && n == 1) ;	
{}


ghost method assign_rule(
p: fmla, x: Mident, fresh_id: Ident, t: term)
  requires fresh_in_fmla(fresh_id,p);
  ensures valid_triple(Flet(fresh_id,t,subst_fmla(p,x,fresh_id)), Sassign(x,t), p);
{
	forall env: map<int,Val>, stack:seq<prod<int,Val>>  
	/* such that */	| eval_fmla(env, stack, Flet(fresh_id,t,subst_fmla(p,x,fresh_id)))
		ensures forall env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int ::
			multi_steps(env, stack, Sassign(x,t), env'', stack'', Sskip, n) ==> 
					eval_fmla(env'',stack'',p);	
	{
		
		assert eval_fmla(env, [pair(fresh_id.v, eval_term(env,stack,t))]+stack, subst_fmla(p,x,fresh_id));
		
		
		forall  env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int | multi_steps(env, stack, Sassign(x,t), env'', stack'', Sskip, n)
		   ensures eval_fmla(env'',stack'',p);
		{
			assign_rule_lemma(env,stack,x,t,env'',stack'',n);
			eval_subst_fmla(p,x,fresh_id,env,[pair(fresh_id.v, eval_term(env,stack,t))]+stack);
			
			assert n == 1;
			assert stack == stack'';
			assert env[x.v:=eval_term(env,stack,t)] == env''; 
			assert eval_fmla(env'',[pair(fresh_id.v, eval_term(env,stack,t))]+stack,p);
			assert fresh_in_fmla(fresh_id,p);
			
			eval_fmla_change_free(fresh_id, eval_term(env,stack,t),p, env'', stack);
			
			assert eval_fmla(env'',[pair(fresh_id.v, eval_term(env,stack,t))]+stack,p) <==> eval_fmla(env'', stack, p);
			assert eval_fmla(env'', stack, p);	
			
		}	
	}	
}


ghost method {:induction n} many_step_seq
(env: map<int,Val>, env'': map<int,Val>,
 stk: seq<prod<int,Val>>, stk'': seq<prod<int,Val>>,
 s1: stmt, s2: stmt, n: int)
  decreases n;
  requires multi_steps(env,stk,Sseq(s1,s2),env'',stk'',Sskip, n);
  ensures  (exists ienv: map<int,Val>, istk: seq<prod<int,Val>>, n1: int, n2: int ::
	  multi_steps(env,stk,s1,ienv,istk,Sskip,n1) && 
	  multi_steps(ienv,istk,s2,env'',stk'',Sskip,n2) &&
	  n == 1+n1+n2);
{
	if(n != 0){
	    var c := step(env, stk, Sseq(s1,s2));
		assert c.conf? && multi_steps(c.env, c.stack, c.st, env'', stk'', Sskip, n-1);
		
		if(s1.Sskip?){
			assert c == conf(env, stk, s2);
			assert multi_steps(env, stk, s2, env'', stk'', Sskip, n-1);
			assert multi_steps(env, stk, s1, env, stk, Sskip, 0);
			assert (exists ienv: map<int,Val>, istk: seq<prod<int,Val>>, n1: int, n2: int ::
						multi_steps(env,stk,s1,ienv,istk,Sskip,n1) && 
						multi_steps(ienv,istk,s2,env'',stk'',Sskip,n2) &&
						n == 1+n1+n2);	// where n1 = 0, n2 = n-1, ienv = env, istk = stk.
	  
		}else{
			assert c.conf?;
			var c2 := step(env, stk, s1);
			assert c == conf(c2.env, c2.stack, Sseq(c2.st, s2));
			assert multi_steps(c2.env,c2.stack,Sseq(c2.st, s2),env'',stk'',Sskip, n-1);
			
			many_step_seq(c2.env, env'', c2.stack, stk'', c2.st, s2, n-1);	// induction hypothesis
			assert (exists ienv: map<int,Val>, istk: seq<prod<int,Val>>, n1: int, n2: int ::
	  multi_steps(c2.env,c2.stack,c2.st,ienv,istk,Sskip,n1) && 
	  multi_steps(ienv,istk,s2,env'',stk'',Sskip,n2) &&
	  n-1 == 1+n1+n2);	
			assert (exists ienv: map<int,Val>, istk: seq<prod<int,Val>>, n1: int, n2: int ::
	  multi_steps(c2.env,c2.stack,c2.st,ienv,istk,Sskip,n1) && 
	  multi_steps(env,stk,s1,ienv,istk,Sskip,n1+1) && 
	  multi_steps(ienv,istk,s2,env'',stk'',Sskip,n2) &&
	  n-1+1 == 1+n1+1+n2);
		}
	}


}


ghost method  seq_rule(p: fmla, r:fmla, q: fmla, s1: stmt, s2: stmt)
  requires valid_triple(p,s1,r);
  requires valid_triple(r,s2,q);
  ensures valid_triple(p,Sseq(s1,s2),q);
{
	forall env: map<int,Val>, stack:seq<prod<int,Val>>  
		| eval_fmla(env, stack, p)
		ensures forall env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int ::
			multi_steps(env, stack, Sseq(s1,s2), env'', stack'', Sskip, n) ==> 
					eval_fmla(env'',stack'',q);	
	{
		
		forall  env'': map<int,Val>, stack'':seq<prod<int,Val>>, n:int | multi_steps(env, stack, Sseq(s1,s2), env'', stack'', Sskip, n)
		   ensures eval_fmla(env'',stack'',q);
		{
			many_step_seq(env, env'', stack, stack'', s1,s2,n);
		}	
	}	
}



ghost method while_rule_lemma
(env: map<int,Val>, stk:seq<prod<int,Val>> , e: term, inv: fmla, body: stmt,
 env'': map<int,Val>, stk'':seq<prod<int,Val>>, n:int)
  decreases n;
  requires multi_steps(env, stk, Swhile(e,inv,body), env'', stk'', Sskip, n);
  ensures eval_fmla(env'',stk'',(Fand(Fnot(Fterm(e)),inv))) ;	
{
			if(eval_term(env, stk, e) == Vbool(false)){
				assert eval_fmla(env,stk,(Fnot(Fterm(e))));
				var c := step(env,stk,Swhile(e,inv,body));
				assert c == conf(env, stk, Sskip);
				assert multi_steps(c.env, c.stack, c.st, env'', stk'', Sskip, n-1);	// important
				assert multi_steps(env, stk, Sskip, env'', stk'', Sskip, n-1);
				assert eval_fmla(env'',stk'',(Fand(Fnot(Fterm(e)),inv)));
			}else{
			
				
				var c := step(env,stk,Swhile(e,inv,body));
				assert c == conf(env, stk, Sseq(body, Swhile(e,inv,body)));
				assert multi_steps(env, stk, Sseq(body, Swhile(e,inv,body)), env'', stk'', Sskip, n-1);
				many_step_seq(env,env'',stk,stk'',body,Swhile(e,inv,body),n-1);
				
				assert eval_fmla(env, stk, Fand(inv, Fterm(e)));
				
				
				forall ienv: map<int,Val>, istk: seq<prod<int,Val>>, n1: int, n2: int
					|	multi_steps(env,stk,body,ienv,istk,Sskip,n1) && 
						multi_steps(ienv,istk,Swhile(e,inv,body),env'',stk'',Sskip,n2) &&
						eval_fmla(ienv,istk,inv) &&
						n - 1 == 1+n1+n2
					ensures eval_fmla(env'',stk'',(Fand(Fnot(Fterm(e)),inv))); 
				{
					while_rule_lemma(ienv, istk, e,inv,body,env'',stk'',n2);
				}
				
				
			
				
			}


}


ghost method  while_rule(
e: term, inv: fmla, body: stmt)
  requires valid_triple(Fand(inv, Fterm(e)),body,inv);	// H1
  ensures  valid_triple(inv ,Swhile(e,inv,body),(Fand(Fnot(Fterm(e)),inv)));
{

	
	// rewriting Lemma
	assert forall env: map<int,Val>, stk:seq<prod<int,Val>> ::
	eval_fmla(env, stk, Fand(inv, Fterm(e))) <==> eval_fmla(env, stk, inv) && eval_fmla(env, stk, (Fterm(e)));
				
	assert forall env: map<int,Val>, stk:seq<prod<int,Val>> ::
	eval_fmla(env, stk, Fand(Fnot(Fterm(e)),inv)) <==> eval_fmla(env, stk, inv) && eval_fmla(env, stk, Fnot(Fterm(e)));

	
	forall env: map<int,Val>, stk:seq<prod<int,Val>> |
		eval_fmla(env, stk, inv) 
	   ensures forall env'': map<int,Val>, stk'':seq<prod<int,Val>>, n:int :: 
			multi_steps(env, stk, Swhile(e,inv,body), env'', stk'', Sskip, n) ==> eval_fmla(env'',stk'',(Fand(Fnot(Fterm(e)),inv)));
	{
		forall env'': map<int,Val>, stk'':seq<prod<int,Val>>, n:int | 
			multi_steps(env, stk, Swhile(e,inv,body), env'', stk'', Sskip, n)
		  ensures eval_fmla(env'',stk'',(Fand(Fnot(Fterm(e)),inv)));
		{
			
			
			while_rule_lemma(env,stk,e,inv,body,env'',stk'',n);
			
			
		}
	
	}
	
	
	
		

	
	
}



