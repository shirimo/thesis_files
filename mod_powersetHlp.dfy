module PowerSetHelpers
{
	predicate IsPowerSet<T>(s: set<T>, powers: set<set<T>>) 
	{
		PowerSetFunc(s)== powers
	}
	lemma onlyOne<T>(emp :set<T>)
		requires emp=={} && emp in PowerSetFunc(emp) && !exists elem :: NotEmp(elem) && elem<=emp
		ensures PowerSetFunc(emp) == {{}};
	{
		assert forall elem :: NotEmp(elem) ==> elem !in PowerSetFunc(emp);
	}
	predicate NotEmp<T>(x: set<T>) 
	{
		x!={}
	}
	function method PowerSetFunc<T>(s: set<T>) : set<set<T>>
		ensures forall subs: set<T> :: subs in PowerSetFunc(s) ==> subs<=s
		ensures forall subs: set<T> :: subs<=s ==> subs in PowerSetFunc(s)
	{
		idLemma(s);
		set subset: set<T> | subset <= s && subset==Id(subset)
	}
	lemma idLemma<T>(s: set<T>)
		ensures forall subs: set<T> :: subs <= s ==> subs==Id(subs)
	{}
	function method Id<T>(x: T): T
	{ 
		x		
	}
	
	predicate IsUniq<T>(q: seq<T>)
	{
		forall i,j :: (0<=i<|q| && 0<=j<|q| && i!=j) ==> q[i] != q[j]
	}
	predicate setIsSeq<T>(q: seq<T>, s: set<T>)
	{
		IsUniq(q) && (forall x: T :: x in q ==> x in s) && (forall x: T :: x in s ==> x in q)
	}
	
	
	function method SetFunc<T>(q: seq<T>) : set<T>
		requires IsUniq(q)
		ensures setIsSeq(q, SetFunc(q))
	{
		set x: T | x in q && x==Id(x)
	}
	
	lemma uniqCount<T>(q: seq<T>, s: set<T>)
		requires setIsSeq(q,s) 
		ensures |s|==|q|
		decreases |s|, |q|
	{
		if (s=={} && q==[])
		{assert |s|==|q|;}
		else
		{
			notEmpSS(q,s);
			var q' := q[1..];
			//assert q[0] !in q';
			var s' := s - {q[0]};
			//assert |s'| == |s| - 1;
			//assert |q'| == |q| - 1;
			uniqCount(q',s');
		}
	}
	
	lemma notEmpSS<T>(q: seq<T>, s: set<T>)
		requires setIsSeq(q,s) && (s!={} || q!=[])
		ensures s!={} && q!=[]
	{
		if  s!={}
		{
			assert exists x :: x in s && x in q;
		}
		else
		{
			assert q[0] in s;
		}
	}
	
	predicate uniqNewPres(q: seq<set<int>>, ind_in: int, elem: int, j: int)
	{
		0<ind_in<=|q| && 2*ind_in<=|q| && 0<=j<ind_in
		&& (forall k :: ind_in<=k<ind_in+j ==> elem in q[k])
		&& (forall k :: 0<=k<ind_in ==> elem !in q[k])
		&& (forall k :: 0<=k<=j ==> q[ind_in+k]==q[k]+{elem})
		&& IsUniq(q[..ind_in+j])
	}
	
	lemma uniqNew(a: array<set<int>>,ind_in: int ,elem: int ,j: int )
		requires uniqNewPres(a[..],ind_in,elem,j)
		ensures IsUniq(a[..ind_in+j+1])
	{
		assert  a[j]+{elem} == a[ind_in+j];
		forall l | ind_in<=l<ind_in+j  ensures exists k :: 0<=k<j && a[l]==a[k]+{elem}{
			assert exists k :: 0<=k<j && a[l]==a[k]+{elem} by {
				assert a[l]==a[l-ind_in]+{elem};
			}
		}
	}
}
