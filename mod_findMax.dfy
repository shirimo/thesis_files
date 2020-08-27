include "mod_lin.dfy"

abstract module FindMaxInterface refines LinearProofInterface
{
	predicate FindMaxPosts(q: seq<int>, max_ind: int)
	{
		0<=max_ind<|q| && forall k :: 0<=k<|q| ==> q[k]<=q[max_ind]
	}
	method findMax(q: seq<int>) returns (max_ind: int, ghost t: nat)
		requires |q|>0
		ensures  FindMaxPosts(q,max_ind)
		ensures IsOn(|q|,t)
}

module FindMax refines FindMaxInterface
{
	function f(n: nat) : nat
	{
		n+1
	}
	lemma linearCalcLemma(n: nat) returns(c: nat, n0: nat)
	{	
		if n==0
		{
			assert forall k: nat :: f(n)>=k*n;
		}
		else
		{
			assert 1<=n;
			calc <=={
				f(n)<=c*n;
				f(n)<=2*n<=c*n;
				c==2 && n0==1 && n0<=n && (f(n)<=2*n<= c*n);    
			}
		}
		
		c, n0 := 2, 1;
	}
	predicate FMLoop(q: seq<int>,i: int, max_ind: int)
	{
		0<=i<=|q| && 0<=max_ind<|q| && forall k :: 0<=k<i ==> q[k]<=q[max_ind]
	}
	method findMax(q: seq<int>) returns(max_ind: int, ghost t: nat)
	{
		t := 1;
		var i := 0;
		max_ind := 0;
		while i < |q|
			invariant FMLoop(q,i,max_ind)
			invariant t == i+1
			decreases |q| - i
		{
			if q[i] >= q[max_ind]
				{max_ind := i;}
			i := i + 1;
			t := t + 1;
		}
		OnProof(|q|,t);
	}
}
