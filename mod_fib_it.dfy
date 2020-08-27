include "mod_lin.dfy"

module FIBHelper
{
	function Fib(n: nat): nat
	{
		if n<=1 then n else Fib(n - 1) + Fib(n - 2)
	}
}

abstract module FiboItInterface refines LinearProofInterface
{
	import opened FIBHelper
	method ComputeFib(n: nat) returns (x: nat, ghost t: nat)
	   ensures x == Fib(n)
	   ensures IsOn(n,t)
}

module FiboIt refines FiboItInterface
{
	function f(n: nat) : nat
	{
		n+2
	}
	lemma linearCalcLemma(n: nat) returns(c: nat, n0: nat)
	{	
		if n==0
		{
			assert forall k: nat :: f(n) >= k * n;
		}
		else
		{
			assert 1<=n;
			calc <=={
				f(n)<=c*n;
				f(n)<=2*n+1<=c*n;
				f(n)<=2*n+1<=3*n<=c*n;
				c==3 && n0==1 && n0<=n && (f(n)<=2*n+1<=3*n<= c*n);    
			}
		}
		
		c, n0 := 3, 1;
	}
	predicate FibLoop(n: nat, x: nat, a: nat, i: nat)
	{
		0<i<=n && a==Fib(i-1) && x==Fib(i)
	}
	method ComputeFib(n: nat) returns (x: nat, ghost t: nat)
		ensures x == Fib(n)
		ensures IsOn(n,t)
	{
		if n<=1 
		{ 
			x := n; 
			t := 1;
		}
		else
		{
			var i,a:= 1,0;
			x := 1;
			t := 3;
			while i < n
			  invariant FibLoop(n,x,a,i)
			  invariant t==i+2
			{
			  a, x := x, a+x;
			  i := i+1;
			  t := t+1;
			}
		}
		OnProof(n,t);
	}
}	