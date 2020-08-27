include "mod_quad.dfy"
include "mod_sort.dfy"

abstract module InsertionSortInterface refines QuadraticProofInterface
{
	import opened SortHelpers
	method insertionSort(a: array<int>) returns(ghost t: nat)
		modifies a
		ensures SortPosts(a[..],old(a[..]))
		ensures IsOn2(a.Length,t)
}

module InsertionSort refines InsertionSortInterface
{
	function f(n: nat) : nat
	{
		1 + (n*(n+1)/2)
	}
	lemma quadraticCalcLemma(n: nat) returns(c: nat, n0: nat)
	{
		calc <=={
				f(n) <= c*n*n;
			}
			if n>0
			{
				calc <=={
					f(n) <= 1+(n*(2*n)/2) <= c*n*n;
					f(n) <= 1+(n*(2*n)/2) == 1+n*n <= c*n*n;
					f(n) <= 1+(n*(2*n)/2) == 1+n*n <= 2*n*n <= c*n*n;
					(c==2 && n0==1 && n0<=n) &&(f(n) <= 1+(n*(2*n)/2) == 1+n*n <= 2*n*n <= c*n*n);
				}
			}
			c, n0 := 2, 1;
	}

	predicate IsValidouterloop(q: seq<int>, oldq: seq<int>, i: int)
	{
		0<=i<=|q|==|oldq| && Sorted(q[..i]) && multiset(oldq) == multiset(q)
	}

	predicate IsValidInnerloop(q: seq<int>, oldq: seq<int>, outerq: seq<int>, j: int , i: int, oldi: int)
	{
	   (0<=j<=i==oldi<|q|==|oldq|==|outerq|) && (forall k :: j<k<=i ==> q[j]<q[k])
	   && (q[0..j]==oldq[0..j]) && (q[j+1..i+1]==oldq[j..i]) 
	   && Sorted(q[..j]) && Sorted(q[j+1.. i+1]) && multiset(q) == multiset(oldq)
	}

	method insertionSort(a: array<int>) returns(ghost t: nat)
	{
		t := 0;
		if a.Length>0
		{
			var i := 1;
			t := t+1;
			while(i < a.Length)
				invariant IsValidouterloop(a[..], old(a[..]), i)
				invariant t <= 1+APSum(i)
			{  
				ghost var t1 := sortSubArr(a,a[..],i);       
				ghost var t' := t;
				i := i + 1; 
				t := t + t1;   
			}
		}
		Gauss(a.Length);
		On2Proof(a.Length,t);
	}
		
	predicate SortSubArrPosts(q: seq<int>, oldq: seq<int>, i: int) 
	{	
		0<i<|q|==|oldq| && Sorted(q[..i+1]) && multiset(q)==multiset(oldq)
	}

	method sortSubArr(a: array<int>, olda: seq<int>, i: int) returns(ghost t: nat)
		modifies a
		requires 0<i<a.Length==|olda| && IsValidouterloop(a[..], olda, i)
		ensures SortSubArrPosts(a[..],olda,i)
		ensures t <= i
	{ 
		t := 0;
		var j := i;
		ghost var oldi := i;
		ghost var q := a[..];      
		while(0<j &&  a[j]< a[j-1])
			invariant IsValidInnerloop(a[..],q,olda,j,i,oldi)
			invariant 0 <= t <= (i-j)  
			decreases j                                 
		{
			ghost var q' := a[..];
			ghost var t2 := swap(a, j-1, j);
			afterSwap(a[..],q,q',j,i);
			j := j - 1;
			t := t + t2;             
		}
	}
	predicate AfterSwapPres(q: seq<int>, oldq: seq<int>,preSwapQ: seq<int>, j: int, i: int)
	{
		1<|q|==|oldq|==|preSwapQ| && 0<j<=i<|q|
		&& oldq[0..j]==preSwapQ[..j] &&  preSwapQ[j+1..i+1]==oldq[j..i]
		&& Swapped(q,preSwapQ, j-1,j) && multiset(q)==multiset(oldq)==multiset(preSwapQ)
	}

	lemma afterSwap(q: seq<int>, oldq: seq<int>,preSwapQ: seq<int>, j: int, i: int)
		requires AfterSwapPres(q,oldq,preSwapQ,j,i)
		ensures q[j..i+1]==oldq[j-1..i]
	{}
}