include "mod_exp.dfy"
include "mod_fib_it.dfy"

abstract module FiboRecInterface refines ExpProofInterface
{
	import opened FIBHelper
	method ComputeFib(n: nat) returns (x: nat, ghost t: nat)	
		ensures x == Fib(n)
		ensures IsOExpn(n,t)
}
module FiboRec refines FiboRecInterface
{
	function f(n: nat) : nat
	{
		3*Power(2,n)
	}
	
	lemma expCalcLemma(n: nat) returns(c: nat, n0: nat)
		ensures IsExpoFrom(c, n0, f)
	{
		
			calc <=={
				f(n)<=Power(2,Power(n,c));
				{calc1(n);}
				f(n)<=Power(2,n+2)<=Power(2,Power(n,c));
			}
			if n>=2
			{
				calc <=={
					f(n)<=Power(2,n+2)<=Power(2,Power(n,c));
					{calc2(n);}
					f(n)<=Power(2,n+2)<=Power(2,Power(n,2))<=Power(2,Power(n,c));
				}
			}
			c, n0 := 2,2;
			expLemmaHelper1 (c, n0);
			calc1(n);
			assert forall k: nat  :: f(k)<=Power(2,k+2);
			expLemmaHelper2 (c, n0);
	}
	
	lemma calc1(n: nat)
		ensures f(n)<=Power(2,n+2);
	{
		calc{
				f(n);
			==
				3*Power(2,n);
			<=
				4*Power(2,n);
			==
				2*Power(2,n+1);
			==
				Power(2,n+2);
			}
	}
	
	lemma calc2(n: nat)
		requires f(n)<=Power(2,n+2)
		ensures n>=2 ==> f(n)<=Power(2,Power(n,2))
	{
		if n>=2
		{
			calc<={
				f(n);
			
				Power(2,n+2);
				{powerMono(n+2,n+n);}
				Power(2,n+n);
			
				Power(2,2*n);
				{mul_inequality(2,n);powerMono(2*n,n*n);}
				Power(2,n*n);
			
				Power(2,Power(n,2));
			}
		}
	}

	lemma expLemmaHelper1 (c: nat, n0: nat)
		requires c==2 && n0==2
		ensures IsExpoFrom(c,n0,g)
	{
		assert forall n: nat ,m: nat :: m>n>0 ==> Power(2,m)>= 2*Power(2,n);
		assert forall n: nat :: n>=n0 ==>g(n)<=Power(2,2*n);
		assert forall n: nat :: n>=n0 ==>g(n)<=Power(2,n*n);
		assert forall n: nat :: n>=n0 ==>g(n)<=Power(2,Power(n,c));
	}
	
	function g(n: nat) : nat
	{
		Power(2,n+2)
	}

	lemma expLemmaHelper2 (c: nat, n0: nat)
		requires IsExpoFrom(c,n0,g)
		requires forall n: nat :: n>=n0 ==>f(n)<=g(n);
		ensures IsExpoFrom(c,n0,f)
	{}
	
	
	method ComputeFib(n: nat) returns (x: nat, ghost t: nat)	
		ensures x == Fib(n)
		ensures IsOExpn(n,t)
	{
		x,t := ComputeFibRec(n);
		OExpnProof(n,t);
	}
	
	method ComputeFibRec(n: nat) returns (x: nat, ghost t: nat)
		ensures x == Fib(n)
		ensures t == FibTime(n)<=3*Power(2,n)
		
	{
		if n<=1 
		{ 
			x := n; 
			t := 1;
		}
		else
		{
			var x1, x2;
			ghost var t1, t2;
			x1,t1 := ComputeFibRec(n-1);
			x2,t2 := ComputeFibRec(n-2);
			x := x1+x2;
			t := t1+t2+4;
			monoFib(t1,t2,n-1,n-2);
			fibTimeExp(n);
		}
		
	}
	
	function FibTime(n: nat): nat
	{
		if n<=1 then 1 else FibTime(n - 1)+FibTime(n - 2)+4
	}

	function method FibTimeCalc(n: nat): nat
		ensures FibTimeCalc(n)==FibTime(n)
	{
		if n<=1 then 1 else FibTimeCalc(n-1)+FibTimeCalc(n-2)+4
	}
	
	lemma fibTimeExp(n: nat)
		ensures FibTime(n)<=3*Power(2,n)
	{
		if n>1
		{
			var t1 :=FibTimeCalc(n-1);
			var t2 :=FibTimeCalc(n-2);
			monoFib(t1,t2,n-1,n-2);
			assert FibTime(n)<= 2*FibTime(n-1)+4;
			assert FibTime(n)<= 6*FibTime(n-1);
			fibTimeExp(n-1);
			expAttribute1(n-1);
		}
	}
	
	lemma monoFib(t1: nat ,t2: nat , n1: nat ,n2: nat )
		requires n1>=n2
		requires t1==FibTime(n1) && t2==FibTime(n2)
		ensures t1>=t2
	{
		if n2<n1-1
		{
			var t1' := FibTimeCalc(n1-1);
			monoFib(t1',t2,n1-1,n2);
		}
	}
}