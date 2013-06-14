ControlHTT
==========
Author: Jennifer Paykin
Email: jpaykin (at) gmail (dot) com

An adaptation of Hoare Type Theory for control software in Coq.
Hoare Type Theory is a dependent type theory using Hoare logic
developed by Nanevski and Morrisett (http://ynot.cs.harvard.edu/papers/htt.pdf).

To compile the implementation (all files excluding example.v), run:
	make all

File List
=========

mymatrices.v   : A library for real, integer and boolean matrices, 
	supplimenting the matrices library from the Coq standard library 
	(http://coq.inria.fr/V8.2pl1/contribs/Matrices.html).
	Includes pointwise numerical operations, matrix multiplication,
	and transposition.

syntax.v       : Defines the syntax of an effectful functional language
	with matrix primitives and a global heap referenced by integer pointers.
	Defines a notion of free variables.

context.v      : Defines a type context as a list of variable-type bindings.
	Builds a library for looking up variables and reasoning about equivalence
	of contexts.

substitution.v : Defines hereditary and monadic substitution relations, as 
	well as normal heap substitution.

typing.v       : Defines beta reduction, eta expansion and the typing
	relation for all syntactic forms. Includes sequent calculus.

properties.v   : A library of lemmas relating to the typing relation and free variables.
	Includes axioms upon which other lemmas depend: 
		check_intro_term_canon
		infer_postcondition_canon
		check_type_canon
		check_prop_subst

example.v      : Uses Hoare Type Theory to prove the Lyapunov
	stability of a simple open-loop controller.