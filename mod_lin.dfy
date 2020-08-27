module LinearNotation
{
	predicate IsLinear (f: nat -> nat)  
	{
		exists c :nat, n0: nat :: IsLinearFrom(c, n0, f)
	}
	predicate IsLinearFrom (c :nat, n0: nat, f: nat -> nat)
	{
		forall n: nat :: n0 <= n ==> f(n) <= c * n
	}
	lemma linear (c :nat, n0: nat, f: nat -> nat)
		requires IsLinearFrom(c,n0,f)
		ensures IsLinear(f)
	{}
	predicate IsOn (n: nat ,t: nat )
	{
		exists f: nat -> nat :: IsLinear(f) && t<=f(n)
	}
}

abstract module LinearProofInterface
{
	import opened LinearNotation
	function f(n: nat) : nat
	
	lemma linearCalcLemma(n: nat) returns(c: nat, n0: nat)
		ensures IsLinearFrom(c,n0,f)
		
	lemma OnProof(n: nat , t: nat )
		requires t<=f(n)
		ensures IsOn(n,t)
	{
		var c,n0 := linearCalcLemma(n);
		linear(c,n0,f);
	}
}