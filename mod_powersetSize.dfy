include "mod_exp.dfy"
include "mod_powersetHlp.dfy"

abstract module PowerSetSizeInterface refines ExpProofInterface
{
	import opened PowerSetHelpers
	method powersetSize(s: set<int>) returns (powers: set<set<int>>)
		ensures IsPowerSet(s,powers)
		ensures IsOExpn(|s|,|powers|)
}
module PSSize refines PowerSetSizeInterface
{
	function f(n: nat) : nat
	{ 
		Power(2,n)
	}
	lemma expCalcLemma(n: nat) returns(c: nat, n0: nat)
		ensures IsExpoFrom(c, n0, f)
	{
		
		calc <=={
			f(n)<=Power(2,Power(n,c));
		}
		c, n0 := 1,1;
		expLemmaHelper1 (c, n0);
		assert forall k: nat  :: f(k)<=Power(2,k);
	}
	lemma expLemmaHelper1 (c: nat, n0: nat)
		requires c==1 && n0==1
		ensures IsExpoFrom(c,n0,f)
	{}
	
	
	predicate PSOuter<T>(s: set<T>, s_diff: set<T>, s_iter: set<T>, powers: set<set<T>>)
	{
		{}<=s_iter<=s && {}<=s_diff<=s && IsPowerSet(s_diff,powers) && s_diff==s-s_iter
	}
	predicate PSInner<T>(powers: set<set<T>> ,powers_diff: set<set<T>> ,powers_iter: set<set<T>> ,powers_in: set<set<T>> ,s_diff: set<T> ,elem: T)
	{
		{}<=powers_iter<=powers && {}<=powers_diff<=powers && powers_diff==powers-powers_iter 
		&& (forall subset :: subset in powers_diff ==> subset+{elem} in powers_in)
		&& (forall subset :: subset in powers_in ==> !exists el :: el in subset && el !in s_diff+{elem})
		&& (forall subset :: subset in powers_iter ==> subset+{elem} !in powers_in) 
		&& |powers_in|==|powers_diff| && powers!!powers_in
	}
	method powersetSize(s: set<int>) returns (powers: set<set<int>>)
	{
		var s_iter := s;
		powers := {{}};
		ghost var s_diff := {};
		onlyOne(s_diff);
		while (s_iter!={})
			invariant PSOuter(s,s_diff,s_iter,powers)
			invariant |powers| ==  Power(2,|s_diff|)
			decreases s_iter
		{
			var elem :| elem in s_iter;
			var powers_in := {};
			var powers_iter := powers;
			ghost var powers_diff := {};
			while (powers_iter != {})
				invariant PSInner(powers,powers_diff,powers_iter,powers_in,s_diff,elem)
				decreases powers_iter
			{
				var subs :| subs in powers_iter;
				powers_diff := powers_diff + {subs};
				powers_in := powers_in + {subs + {elem}};
				powers_iter := powers_iter - {subs};	
			}
			ghost var s_diff' := s_diff;
			s_diff := s_diff + {elem};
			powers := powers + powers_in;
			psLemma1(s_diff',powers_diff,s_diff,PowerSetFunc(s_diff),powers,elem);
			s_iter := s_iter - {elem};
		}
		OExpnProof(|s|,|powers|);
	}
	predicate psLemma2Pres<T>(xPowers: set<set<T>>, yPowers: set<set<T>>, powers: set<set<T>>, elem: T)
	{
		xPowers<=powers && xPowers<=yPowers 
		&& (forall subs :: (subs in yPowers && elem !in subs) ==> subs in powers)
		&& (forall subs :: (subs in yPowers && elem in subs) ==> (subs-{elem}) in xPowers)
		&& (forall subs :: subs in xPowers ==> (subs in powers && subs+{elem} in powers))
	}
	lemma psLemma2<T>(xPowers: set<set<T>>, yPowers: set<set<T>>, powers: set<set<T>>, elem: T)
		requires psLemma2Pres(xPowers,yPowers,powers,elem)
		ensures yPowers<=powers
	{
		assert forall subs :: (subs in yPowers && elem in subs) ==> ((subs-{elem})+{elem} in powers);
		assert forall subs :: (subs in yPowers && elem in subs) ==> (subs-{elem})+{elem}==subs;
	}
	predicate psLemma1Pres<T>(x: set<T>,  xPowers: set<set<T>>, y: set<T>, yPowers: set<set<T>>, powers: set<set<T>>, elem: T)
	{
		IsPowerSet(x,xPowers) && y==x+{elem} && yPowers==PowerSetFunc(y)
		&& (forall subs :: subs in xPowers ==> (subs in powers && subs+{elem} in powers))
		&& (forall subs :: subs in powers ==> !exists el :: el in subs && el !in y)
	}
	lemma psLemma1<T>(x: set<T>,  xPowers: set<set<T>>, y: set<T>, yPowers: set<set<T>>, powers: set<set<T>>, elem: T)//x=sdiff,xpowers=powersdiff y==powers
		requires psLemma1Pres(x,xPowers,y,yPowers,powers,elem)
		ensures IsPowerSet(y,powers)
	{
		psLemma2(xPowers,yPowers,powers,elem);
	}
}
