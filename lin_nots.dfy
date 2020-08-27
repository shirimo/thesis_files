predicate IsOn (n: nat ,t: nat )
{
	exists f: nat -> nat :: IsLinear(f) && t<=f(n)
}
predicate IsLinear (f: nat -> nat)  
{
	exists c :nat, n0: nat :: IsLinearFrom(c,n0,f)
}
predicate IsLinearFrom (c :nat, n0: nat, f: nat -> nat)
{
	forall n: nat :: n0 <= n ==> f(n) <= c * n
}
lemma linear(c :nat, n0: nat, f: nat -> nat)
	requires IsLinearFrom(c,n0,f)
	ensures IsLinear(f)
{}


predicate IsLinearOrUp(f: nat -> nat)
{
	exists c :nat, n0: nat :: IsLinearOrUpFrom(c,n0,f)
}
predicate IsLinearOrUpFrom(c: nat ,n0: nat, f: nat -> nat)
{
	forall n: nat :: n>=n0 ==> f(n)>=c*n
}
lemma linearOrUp(c :nat, n0: nat, f: nat -> nat)
	requires IsLinearOrUpFrom(c,n0,f)
	ensures IsLinearOrUp(f)
{}


predicate IsEqLinear(f: nat -> nat)
{
	exists c1 :nat, c2 :nat, n0: nat :: IsEqLinearFromTo(c1,c2,n0,f)
}
predicate IsEqLinearFromTo(c1: nat ,c2: nat, n0: nat, f: nat -> nat)
{
	forall n: nat :: n>=n0 ==> c1*n<=f(n)<=c2*n
}
lemma linearEq(c1: nat ,c2: nat, n0: nat, f: nat -> nat)
	requires IsEqLinearFromTo(c1,c2,n0,f)
	ensures IsEqLinear(f)
{}

function f(n: nat) : nat
{
    n + 2
}

lemma OLinearCalcLemma(n: nat) returns(c: nat, n0: nat)
	ensures IsLinearFrom(c, n0, f)
	ensures IsLinear(f)
{	
	if n>=2
	{
		calc <=={
			f(n) <= c*n;
			f(n) <= 2*n <= c*n;
			c==3 && n0==2 && n0<=n && (f(n) <= 2*n == c*n);    
		}
	}
	
	c, n0 := 2, 2;
	linear(c, n0, f);
}

lemma OmegaLinearCalcLemma(n: nat) returns(c: nat, n0: nat)
	ensures IsLinearOrUpFrom(c,n0,f)
	ensures IsLinearOrUp(f)
{		
	calc <=={
		f(n) >=c*n;
		f(n) >= 1*n >= c*n;
		c==1 && n0==1 && n0<=n && (f(n) >= n == c*n);    
	}
	c, n0 := 1, 1;
	linearOrUp(c,n0,f);
}

lemma ThetaLinearCalcLemma(n: nat) returns(c1: nat, c2: nat, n0: nat)
	ensures IsEqLinearFromTo(c1,c2,n0,f)
	ensures IsEqLinear(f)
{		
	var n10, n20;
	c1, n10 := OmegaLinearCalcLemma(n);
	c2, n20 := OLinearCalcLemma(n);
	if n10>n20
	{
		n0 := n10;
	}
	else
	{
		n0 := n20;
	}
	linearEq(c1,c2,n0,f);
}