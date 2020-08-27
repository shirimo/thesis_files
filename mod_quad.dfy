
//Big O Notations :the formal way to express the upper bound of an algorithm's running time

//Ο(n) = { f(n) : there exists c > 0 and n0 such that f(n) ≤ c*n for all n > n0}
module QuadraticNotation
{

	predicate IsOn2 (n: nat ,t: nat )
	{
		exists f: nat -> nat :: IsQuadratic(f) && t<=f(n)
	}
	predicate IsQuadraticFrom (c :nat, n0: nat, f: nat -> nat)
	{
		forall n: nat :: 0 < n0 <= n ==> f(n) <= c*n*n
	}
	predicate IsQuadratic(f: nat -> nat)  
	{
		exists c :nat, n0: nat :: IsQuadraticFrom(c, n0, f)
	}
	lemma quadratic (c :nat, n0: nat, f: nat -> nat)
		requires IsQuadraticFrom(c,n0,f)
		ensures IsQuadratic(f)
	{}
}
abstract module QuadraticProofInterface
{
	import opened QuadraticNotation
	function f(n: nat) : nat
	
	lemma quadraticCalcLemma(n: nat) returns(c: nat, n0: nat)
		ensures IsQuadraticFrom(c, n0, f)
		
	lemma On2Proof(n: nat , t: nat )
		requires t<=f(n)
		ensures IsOn2(n,t)
	{
		var c,n0 := quadraticCalcLemma(n);
		quadratic(c,n0,f);
	}
}