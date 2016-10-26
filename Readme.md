Overview
=====
The goal of this project is using the Dafny verification language to specify the design of a toy imperative language (WHILE-like). The design includes the syntax, small step operational semantics, type system and proof system of the language. Consequently, we can enjoy the verification capability of Dafny to prove theorem/lemma such as type soundness by stepping, the soundness of proof system.


Repository structure
=====
	- DataStructure.dfy : Aux data structures used in this project.
	- SyntaxSharp.dfy	: Syntax of WHILE.
	- SemanticsSharp.dfy: Small step operational semantics of WHILE.
	- TypeSharp.dfy		: Type system of WHILE.
	- Substitution.dfy	: Define substitution rules for term and formula.
	- HoareLogic.dfy	: Define |= {p} S {q}, semantics entailment.
	- Proofs			: Proofs for WHILE 
		- ProofSemantics.dfy	# proof for stepping.
		- ProofType.dfy			# proof for type soundness.
		- ProofSubst.dfy		# proof for substitution.
		- ProofHoare.dfy		# proof Hoare logic is sound with respect to the operational semantics of WHILE.


Dafny heads-up:
=====
I enjoy very much using Dafny in this project. However, there are some experience I want to share with people. Hopefully, we can work out some of them in the near future to improve Dafny.
* Dafny is naturally incomplete (a trade-off for its automation), e.g.
   * Dafny does not encode all the axioms for lists (for performance reason I think). For example, Dafny does not know that for list concatenation, A+B+C <==> A+(B+C).
   * Some features of Dafny is based on pattern matching (e.g. triggers). Do not get surprised if we have to rewrite a formula to trigger the matching. 
* Unlike Boogie, Dafny don't support global axioms directly. Some work around is required to encode inductive predicate.
* When a proof depends on an inductively defined abstract data type, it would be nice to automatically expand the definition of abstract data type to locate which case cause the proof unverified. 
* Be careful with the match expression, the formal parameter can conflict with the case's constructor fields without error message.
* It would be really nice if we can know which lemma is useful/suitable in the current context.
* The semantics {: inductive n} is not very clear. 
* Choose the native-supported abstract data type if possible (e.g. set/seq, for performance and axiom consistent reasons), and define our own only when necessary.
* There are various of hidden experimental features of Dafny. I recommend the following resources to get to know them:
   * The [blog of lexicalscope](http://www.lexicalscope.com/blog/).
   * The [Dafny community](https://dafny.codeplex.com/discussions).


Contact
=====
> Zheng Cheng: cz0590@gmail.com


