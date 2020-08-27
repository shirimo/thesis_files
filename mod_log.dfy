module Log2Rules
{
	function Log2(x: nat) : nat
		requires x>0
		decreases x
	{
		natDivision(x,2);
		if x==1 then 0 else 1+ Log2(x/2)
	}
	lemma natDivision(a: nat, b: nat)
	  requires b>0 
	  ensures a/b == (a as real / b as real).Floor
	  
	{
	  assert a == (a / b) * b + (a % b);
	  assert a as real == (a / b) as real * b as real + (a % b) as real;
	  assert a as real / b as real == (a / b) as real + (a % b) as real / b as real;
	}
	lemma log2Mono (x: nat, y: nat)
		requires x>0 && y>0
		ensures y>=x ==> Log2(y)>=Log2(x)
		decreases x,y 
	{
		if (x!=1 && y!=1) { log2Mono(x-1,y-1); }
	}		
}
module Log2Notation
{
	import opened Log2Rules
	predicate IsOLog2n(n: nat ,t: nat )
	{
		exists h: nat -> nat :: IsLog2(h) && t<=h(n)
	}
	predicate IsLog2(h: nat -> nat)  
	{
		exists c :nat, n0: nat :: IsLog2From(c, n0, h)
	}
	predicate IsLog2From(c :nat, n0: nat, h: nat -> nat)
	{
		forall n: nat :: 0 < n0 <= n ==> h(n) <= Log2(n) * c
	}
	lemma logarithmic(c :nat, n0: nat, h: nat -> nat)
		requires IsLog2From(c, n0, h)
		ensures IsLog2(h)
	{}
}
abstract module LogarithmicProofInterface
{
	import opened Log2Notation
	function f(n: nat) : nat

	lemma logarithmicCalcLemma(n: nat)returns(c :nat, n0:nat)
		requires n>0
		ensures IsLog2From(c,n0,f)		
	lemma OLog2nProof(n: nat , t: nat )
		requires n>0
		requires t<=f(n)
		ensures IsOLog2n(n,t)
	{
		var c,n0 := logarithmicCalcLemma(n);
		logarithmic(c,n0,f);
	}
}