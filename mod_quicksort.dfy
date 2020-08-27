include "mod_quad.dfy"
include "mod_sort.dfy"

abstract module QuickSortInterface refines QuadraticProofInterface
{
	import opened SortHelpers
	method quickSort(a: array<int>) returns(ghost t: nat)
		modifies a
		ensures SortPosts(a[..],old(a[..]))
		ensures IsOn2(a.Length,t) 
}

module QuickSort refines QuickSortInterface
{
	function f(n: nat) : nat
	{
		1+3*(n*(n+1)/2)	
	}

	lemma quadraticCalcLemma(n: nat) returns(c: nat, n0: nat)

	{
		calc <=={
				f(n) <= c*n*n;
			}
			if n>0
			{
				calc <=={
					f(n) <= 1+3*(n*(2*n)/2) <= c*n*n;
					f(n) <= 1+3*(n*(2*n)/2) == 1+3*n*n <= c*n*n;
					f(n) <= 1+3*(n*(2*n)/2) == 1+3*n*n <= 4*n*n <= c*n*n;
					(c==4 && n0==1 && n0<=n) &&(f(n) <= 1+3*(n*(2*n)/2) == 1+3*n*n <= 4*n*n <= c*n*n);
				}
			}
			c, n0 := 4, 1;
	}
	
	predicate SeqSmallerThanNum(q: seq<int>, num: int)
	{
		forall x :: x in q ==> x <= num
	}
	
	predicate SeqBiggerThanNum(q: seq<int>, num: int)
	{
		forall x :: x in q ==> x >= num
	}
	
	predicate PartitionLoop(q: seq<int>, oldq: seq<int>, from: int, to: int, r: int, le: int, piv: int)
		requires |q|>1 && 0 <= from < to <= |q|==|oldq|
	{
		0<=from<=le<=r<to<=|q| && multiset(q) == multiset(oldq) && q[r]==piv && SeqSmallerThanNum(q[from..le],q[r]) && SeqBiggerThanNum(q[r..to],q[r]) && SubMultisets(q, oldq, from, to)
	}
	
	predicate Partitioned(q: seq<int>, oldq: seq<int>, from: int, to: int, r: int)
	{	
		|oldq|==|q|>1 && multiset(q) == multiset(oldq) 
		&& 0<=from<=r<to<=|q| 
		&& SeqSmallerThanNum(q[from..r+1],q[r]) 
		&& SeqBiggerThanNum(q[r..to],q[r]) 
		&& SubMultisets(q, oldq, from, to)
	}

	lemma smallSubSeq(q1: seq<int>,q2: seq<int>, num: int)
		requires |q1|>=0 && |q2|>=0 && q2<=q1
		requires SeqSmallerThanNum(q1,num)
		ensures SeqSmallerThanNum(q2,num)
	{
		assert forall x :: x in q2 ==> x in q1;
	}

	lemma bigSubSeq(q1: seq<int>,q2: seq<int>, num: int)
		requires |q1|>0 && |q2|>=0 && q2==q1[1..]
		requires SeqBiggerThanNum(q1,num)
		ensures SeqBiggerThanNum(q2,num)
	{
		assert forall x :: x in q2 ==> x in q1;
	}

	lemma multiSmall(q: seq<int>, oldq: seq<int>, num: int)
		requires |q|>=0 && |q|==|oldq| && multiset(q)==multiset(oldq) && SeqSmallerThanNum(oldq,num)
		ensures SeqSmallerThanNum(q,num)
	{
		assert forall x :: x in q ==> x in multiset(q);
		assert forall x :: x in multiset(q) ==> x in multiset(oldq);
		assert forall x :: x in multiset(oldq) ==> x in oldq;
	}
	lemma multiBig(q: seq<int>, oldq: seq<int>, num: int)
		requires |q|>=0 && |q|==|oldq| && multiset(q)==multiset(oldq) && SeqBiggerThanNum(oldq,num)
		ensures SeqBiggerThanNum(q,num)
	{
		assert forall x :: x in q ==> x in multiset(q);
		assert forall x :: x in multiset(q) ==> x in multiset(oldq);
		assert forall x :: x in multiset(oldq) ==> x in oldq;
	}

	lemma sameMultiRight(q'': seq<int>,q': seq<int>, from: int, r: int)
		requires |q''|>1 && 0<=from<=r<|q''|==|q'| && multiset(q''[from..r])==multiset(q'[from..r]) && q''[r]==q'[r]
		ensures multiset(q''[from..r+1]) == multiset(q'[from..r+1])
	{
		assert q''[from..r]+[q''[r]] ==  q''[from..r+1];
		assert q'[from..r]+[q'[r]] ==  q'[from..r+1];
		assert multiset(q''[from..r]+[q''[r]]) == multiset(q''[from..r+1]); 
		assert multiset(q'[from..r]+[q'[r]]) == multiset(q'[from..r+1]); 	
	}
	lemma sameMultiLeft(q'': seq<int>,q': seq<int>, to: int, r: int)
		requires |q''|>1 && 0<=r<to<=|q''|==|q'| && multiset(q''[r+1..to])==multiset(q'[r+1..to]) && q''[r]==q'[r]
		ensures multiset(q''[r..to]) == multiset(q'[r..to])
	{
		assert [q''[r]]+q''[r+1..to] ==  q''[r..to];
		assert [q'[r]]+q'[r+1..to] ==  q'[r..to];
		assert multiset([q''[r]] + q''[r+1..to]) == multiset(q''[r..to]); 
		assert multiset([q'[r]]  + q'[r+1..to]) == multiset(q'[r..to]); 	
	}

	predicate bigSwapPres(q: seq<int>, oldq: seq<int>, to: int, r: int)
	{
		|oldq|==|q|>1 && 0<r<to<=|q|
		&& Swapped(q,oldq,r-1,r) && SeqBiggerThanNum(oldq[r..to],oldq[r]) 
		&& oldq[r-1]>=oldq[r] && multiset(q[r-1..])==multiset(oldq[r-1..])
	}
	lemma bigSwap(q: seq<int>, oldq: seq<int>, to: int, r: int) 
		requires bigSwapPres(q,oldq,to,r)
		ensures SeqBiggerThanNum(q[r-1..to],q[r-1]) 
	{
		assert oldq[r-1..r] + oldq[r..to] == oldq[r-1..to]; 
		assert SeqBiggerThanNum(oldq[r-1..to],oldq[r]);
		multiBig(q[r-1..to],oldq[r-1..to],oldq[r]);
		assert SeqBiggerThanNum(q[r-1..to],oldq[r]);	
	}

	predicate SubMultisets(q: seq<int>, oldq: seq<int>, from: int, to: int) 
		requires |oldq|==|q|>1 && 0<=from<=to<=|q| && multiset(q) == multiset(oldq)
	{
		q==oldq[..from]+q[from..to]+oldq[to..] && q[..from]==oldq[..from] && multiset(q[from..to])==multiset(oldq[from..to]) && q[to..]==oldq[to..]
	}
	lemma subMultiset(q: seq<int>, oldq: seq<int>, from: int, to: int)
		requires |q|>1 && 0<=from<=to<=|q|==|oldq| && multiset(q)==multiset(oldq) && q==oldq[..from]+q[from..to]+oldq[to..] 
		ensures SubMultisets(q,oldq,from,to)
		ensures to<|q|==|oldq| ==> (q[to]==oldq[to] && q[to+1..]==oldq[to+1..])
		ensures from>0 ==> (q[from-1]==oldq[from-1] && q[..from-1]==oldq[..from-1])
		
	{
		assert multiset(q)-multiset(oldq[..from])-multiset(oldq[to..]) == multiset(q[from..to]);
		assert oldq==(oldq[..from]+oldq[from..to]+oldq[to..]);
		assert multiset(oldq)-multiset(oldq[..from])-multiset(oldq[to..]) == multiset(oldq[from..to]);
		assert  multiset(q) == multiset(oldq[..from])+multiset(oldq[from..to])+multiset(oldq[to..]);
		assert q[..from] == oldq[..from];
		assert q[to..] == oldq[to..];
	}

	predicate Prove1Pres(q'': seq<int>, q': seq<int>, q: seq<int>, from: int, to: int, r: int)
	{
		1<|q''|==|q'|==|q| && 0<=from<=r<to<=|q|
		&& multiset(q'')==multiset(q')==multiset(q)
		&& Partitioned(q',q,from,to,r) && SubMultisets(q'',q', from,r)
		&& Sorted(q''[from..r])
	}
	predicate Prove1Posts(q'': seq<int>, q': seq<int>, q: seq<int>, from: int, to: int, r: int)
	{
		Prove1Pres(q'',q',q, from,to,r) && q''[r]==q'[r] && Partitioned(q'',q,from,to,r)
	}
	lemma prove1 (q'': seq<int>, q': seq<int>,q: seq<int>, from: int, to: int, r: int)
		requires Prove1Pres(q'',q',q, from,to,r)
		ensures Prove1Posts(q'',q',q, from,to,r)
	{
		sameMultiRight(q'',q',from,r);
		multiSmall(q''[from..r+1], q'[from..r+1], q''[r]);
		assert q''[r..to] == q'[r..to];
		subMultiset(q'',q', from,to); 
	}

	predicate Prove2Pres(q''': seq<int>, q'': seq<int>, q': seq<int>, q: seq<int>, from: int, to: int, r: int)
	{
		1<|q''|==|q'|==|q|==|q'''| && 0<=from<=r< to <= |q|
		&& multiset(q''')==multiset(q'')==multiset(q')==multiset(q)
		&& Partitioned(q'',q,from,to,r) && SubMultisets(q''',q'',r+1,to)
		&& Sorted(q'''[r+1..to]) && Sorted(q''[from..r])
		&& q''[r]==q'[r]
	}
	predicate Prove2Posts(q''': seq<int>, q'': seq<int>, q': seq<int>, q: seq<int>, from: int, to: int, r: int)
	{
		Prove2Pres(q''',q'',q',q, from,to,r) && q'''[r]==q''[r]==q'[r] && Partitioned(q''',q,from,to,r) && Sorted(q'''[from..r])
	}
	lemma prove2 (q''': seq<int>,q'': seq<int>, q': seq<int>,q: seq<int>, from: int, to: int, r: int)
		requires Prove2Pres(q''',q'',q',q, from,to,r)
		ensures Prove2Posts(q''',q'',q',q, from,to,r)
	{
		sameMultiLeft(q''',q'',to,r);
		multiBig(q'''[r..to], q''[r..to], q'''[r]);
		subMultiset(q''',q'', from,to); 
		assert q'''[from..r]==q''[from..r];
	}

	lemma subSorted(q: seq<int>, from: int, to: int, r:int)
		requires |q|>1 && 0 <= from <= r < to <= |q|
		requires Sorted(q[from..r]) && Sorted(q[r+1..to]) && SeqSmallerThanNum(q[from..r+1],q[r]) && SeqBiggerThanNum(q[r..to],q[r])
		ensures Sorted(q[from..to])
	{
		assert r>from ==> (q[r-1] in q[from..r+1] && q[r] >= q[r-1]);
		assert to>r+1 ==> (q[r+1] in q[r..to] && q[r+1] >= q[r]);
		assert forall i,j :: ((from <= i <= j <= r ==> q[i] <= q[j]) && (r <= i <= j < to ==> q[i] <= q[j]));
	}

	lemma qtime(n: nat, n1: nat, n2: nat)
		requires n>=1 && n1+n2 == n-1
		ensures 3*APSum(n1)+ 3*APSum(n2) <= 3*APSum(n-1)
	{
		calc {
			APSum(n-1);
			=={Gauss(n-1);}
			((n-1)*n)/2;
			==
			((n-1)*(n-1)+(n-1))/2;
			=={Gauss(n1);Gauss(n2);}	
			((n1+n2)*(n1+n2)+(n1+n2))/2;
			==
			((n1*n1 + 2*n1*n2 + n2*n2)+(n1+n2))/2;
			>=	
			((n1*n1 + n2*n2)+(n1+n2))/2;
			>=
			(n1*(n1+1))/2 + (n2*(n2+1)/2);
			>={Gauss(n1); Gauss(n2);}
			APSum(n1)+ APSum(n2);
		}
		assert APSum(n1)+ APSum(n2) <= APSum(n-1);
		assert 3*APSum(n1)+ 3*APSum(n2) <= 3*APSum(n-1);
	}

	method partition(a: array<int>, from: int, to: int) returns (r: int, ghost t: nat)
		modifies a
		requires a.Length>1 && 0 <= from < to <= a.Length
		ensures Partitioned(a[..],old(a[..]),from,to,r) 
		ensures t <= 3*(to-from) 
	{
		var le := from;
		r := to-1;
		var piv := a[r];
		t := 1;
		while le<r 
			invariant PartitionLoop(a[..],old(a[..]),from,to,r,le,piv) 
			invariant t <= 1 + (2*((to-from)-(r-le)))
			decreases r-le
		{
			if a[le]<=piv
			{
				le := le+1;
				t := t+1;
			}
			else
			{
				ghost var t1 := swap(a,le,r-1);
				ghost var q' := a[..];
				ghost var t2 := swap(a,r-1,r);
				bigSwap(a[..],q',to,r);
				r := r-1;
				t := t+t1+t2;
			}
		}
	}
	predicate QuickSortRecPosts(q: seq<int>, oldq: seq<int>, from: int, to: int)
	{
		|q|==|oldq|>1 && 0<=from<=to<=|q| && multiset(q)==multiset(oldq) && SubMultisets(q,oldq,from,to) && Sorted(q[from..to])
	}

	method quickSortRec(a: array<int>, from: int, to: int) returns(ghost t: nat)
		modifies a
		requires a.Length>1 && 0 <= from <= to <= a.Length
		ensures QuickSortRecPosts(a[..],old(a[..]),from,to)
		ensures t <= 3*APSum(to-from)
		decreases to - from
	{
		ghost var q := a[..];
		t := 0;
		if from<to
		{
			ghost var n := to-from;
			var r;
			ghost var t';
			r, t' := partition(a,from,to);
			ghost var n1 := r-from;
			ghost var n2 := to-(r+1);
			ghost var q' := a[..];
			ghost var t1 := quickSortRec(a,from,r);
			prove1 (a[..],q',q,from,to,r);
			ghost var q'' := a[..];
			ghost var t2 := quickSortRec(a,r+1,to);
			prove2 (a[..],q'', q',q,from,to,r);
			subSorted(a[..], from, to, r);
			t := t' + t1 + t2;
			qtime(n,n1,n2);
			Gauss(n);
		}
	}

	method quickSort(a: array<int>) returns(ghost t: nat) 
	{
		t := 1;
		if a.Length > 1
		{
			ghost var t1 := quickSortRec(a,0,a.Length);
			t := t+t1;
			Gauss(a.Length);
		}
		On2Proof(a.Length,t);
	}
}	