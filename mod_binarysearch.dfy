include "mod_log.dfy"
include "mod_sort.dfy"
abstract module BinarySearchInterface refines LogarithmicProofInterface
{
	import opened SortHelpers
	import opened Log2Rules
	method binarySearch(q: seq<int>, key: int) returns (r: int, ghost t: nat)
		requires |q|>0 && Sorted(q) 
		ensures BinaryPosts(q,r,key)
		ensures IsOLog2n(|q|,t)

	predicate BinaryPosts(q: seq<int>,r: int, key: int)
	{
		(0<=r ==> r<|q| && q[r]==key) && (r<0 ==> key !in q[..])
	}
}

module LogarithmicProofBinarySearch refines BinarySearchInterface
{
	function f(n: nat) : nat
	{
		2*Log2(n+1) + 1
	}
	
	lemma logarithmicCalcLemma(n: nat)returns(c :nat, n0:nat)
	{	
		calc {
			f(n);
		==
			2*Log2(n+1) + 1;
		<=
			2*Log2(n+1) + Log2(n+1);
		==
			3*Log2(n+1);
		<=  {assert n>=1; log2Mono(n+1,2*n);}
			3*Log2(2*n);
		== 
			3*(1+Log2(n)); 
		}
		assert f(n)<= 3*(1+Log2(n));
		assert n>=2 ==> (f(n)<=6*Log2(n));
		c, n0 := 6, 2;
	}
	
	predicate BinaryLoop(q: seq<int>,lo: int, hi: int,r: int, key: int)
	{
		0<=lo<=hi<=|q| && (r<0 ==> key !in q[..lo] && key !in q[hi..]) && (0<=r ==> r<|q| && q[r]==key)
	}

	method binarySearch(q: seq<int>, key: int) 
		returns (r: int, ghost t: nat)
	{
		t := 0;
		r:= -1;
		if |q|>0
		{
			var lo, hi := 0, |q|;
			while lo < hi
				invariant BinaryLoop(q, lo, hi, r, key)
				invariant t <= TBS(q, 0, |q|, key) - TBS(q, lo, hi, key)
				decreases hi-lo
			{
				var mid := (lo+hi)/2;
				assert (lo+hi)/2 == (lo+((hi-lo)/2));
				if key < q[mid] 
				{
					hi := mid;
				} 
				else if q[mid] < key 
				{
					lo := mid + 1;
				} 
				else 
				{
					r := mid;
					hi := lo;
				}
				t := t+1;
			}
			TBSisLog(q,0,|q|,key);
			log2Mono(|q|,|q|+1);
			OLog2nProof(|q|,t);
		}
	}
	
	function TBS(q: seq<int>,lo: int, hi: int, key: int) : nat
		requires 0 <= lo <= hi <= |q|
		decreases hi-lo
	{
		var mid := (lo+hi)/2;
		if (hi-lo==0|||q|==0) then 0 else if  key==q[mid] || (hi-lo==1) then 1 else if key<q[mid] then 1 + TBS(q,lo,mid,key) else 1 + TBS(q,mid+1,hi,key)
	}
	
	lemma TBSisLog (q: seq<int>,lo: nat, hi: nat, key: int)
		requires |q|>0
		requires 0 <= lo < hi <= |q|
		decreases hi-lo
		ensures TBS(q,lo,hi,key) <= 2*Log2(hi-lo)+1
	{
		var mid := (lo+hi)/2;
		if key<q[mid] && 1<hi-lo
		{
			TBSisLog(q,lo,mid,key);
		}
		else if key>q[mid] && hi-lo>2
		{
			log2Mono(hi-(mid+1),(hi-lo)/2);
			TBSisLog(q,mid+1,hi,key);
		}
	}
	
	predicate TBSisOLog2n(q: seq<int>,lo: nat, hi: nat, key: int)
		requires |q|>0
		requires 0 <= lo < hi <= |q|
	{
		exists f: nat->nat ,c: nat, n0: nat :: IsLog2From(c, n0, f) &&  TBS(q,lo,hi,key)<=f(|q|)
	}
}
