module PowerRules
{	
	function Power(n: nat, c: nat): nat
		decreases c
	{ 
		if c==0 then 1 else if n==0 then 0 else n * Power(n,c-1)
	}
	
	lemma mul_inequality(x: nat, y: nat)
		requires x <= y;
		ensures  forall z: nat :: x*z <= y*z;
	{}
	lemma powerMono (x: nat ,y: nat )
		requires y>=x>0
		ensures forall n: nat :: Power(n,y)>=Power(n,x)
		decreases x,y 
	{
		if (x!=1 && y!=1) { powerMono(x-1,y-1); }
	}
	function method PowerCalc(n: nat, c: nat): nat
		requires n>0
		ensures PowerCalc(n,c) == Power(n,c)
		ensures PowerCalc(n,c) >= 1
		decreases c
	{if (c==0) then 1 else n * PowerCalc(n,c-1)}
	
	lemma expAttribute1(n: nat )
		ensures 2*Power(2,n)==Power(2,n+1)
	{}
}

module ExpNotation
{
	import opened PowerRules 
	predicate IsOExpn (n: nat ,t: nat )
	{
		exists f: nat -> nat :: IsExpo(f) && t<=f(n)
	}
	predicate IsExpo (f: nat -> nat)  
	{
		exists c :nat, n0: nat :: IsExpoFrom(c,n0,f)
	}
	predicate IsExpoFrom (c :nat, n0: nat, f: nat -> nat)
	{
		forall n: nat ::  0 < n0 <= n ==> f(n) <= Power(2,Power(n,c))
	}
	lemma expoential (c :nat, n0: nat, f: nat -> nat)
		requires IsExpoFrom(c,n0,f)
		ensures IsExpo(f)
	{}
	
}
abstract module ExpProofInterface
{
	import opened ExpNotation
	import opened PowerRules
	function f(n: nat) : nat
	lemma expCalcLemma(n: nat)returns(c :nat, n0:nat)
		ensures IsExpoFrom(c, n0, f)	
	lemma OExpnProof(n: nat , t: nat )
		requires t<=f(n)
		ensures IsOExpn(n,t)
	{
		var c,n0 := expCalcLemma(n);
		expoential(c,n0,f);
	}
}
