* Author: Zheng Cheng
* Date: 2014.10


This is my current attempt to model a IMP-like proof system, and prove its soundness (all in Dafny). The goal is to develop a tool-kit for similar activities (e.g. prove the soundness of ASM proof system), and benefit the proof for the transformation's operational correctness. 


* Repository structure
	- DataStructure.dfy # Aux data structures used in this project.
	- SyntaxSharp.dfy	# Syntax of IMP
	- SemanticsSharp.dfy# Semantics of IMP
	- TypeSharp.dfy		# Type system of IMP
	- Substitution.dfy	# Define substitution rules for term and formula
	- HoareLogic.dfy	# Define |= {p} S {q}, semantics entailment
	- Proofs			# Proofs PL properties for IMP 
		- ProofSemantics.dfy
		- ProofType.dfy			# Lemma for type soundness.
		- ProofSubst.dfy		# Lemma for substitution.
		- ProofHoare.dfy		# Prove Hoare logic is sound with respect to operational semantics of IMP.

* Technical Problems:
	- How to encode inductive predicate of Coq nicely.
		- Dafny don't support axioms.
		- This is not a big problem, just out of curiosity of the essence of inductive predicate.
		
* Technical justification. There are several reasons that why a theorem is not discharged automatically:
	- The formula needs rewriting, the following helps:
		- rewrite A && B to B && A
		- Unfold the function definition
		- A+B+C to A+(B+C)
	- Exchange between functional and relational definitions, to see which one is better.
			- functional avoid existence quantifier
			- relational avoid it to be 'total'
	- Exchange between data types definition, e.g. local stack is better defined as stack rather than map.
	- The data structures involved in the formula is inductively defined, which needs a structural case analysis (destruct) to locate which case cause the problem.
		- In this case, the trace/error messages from Dafny sometimes helped.
	- Forget to apply proved lemma.
	
	
* Useful features of Dafny:
	- {:verify false} means not verify the current method/function.
	- Proving forall x :: P(x) ==> Q(x)
	- Opaque functions in Dafny 

	

* Dafny heads-up:
	- Be careful with the match expression, the formal parameter can conflict with the case's constructor fields without error message.
	- No automatic lemma application finding. 
	- Don't rely on {: inductive n} too much. 
	- No recompilation in Dafny, e.g. in <syntax>, add Flet expression, in <type>, not add Flet expression. In the <prooftype>, which depends on <type>, still acts like the Flet not being added.
	




