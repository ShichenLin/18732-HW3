module Specification {
	function method product (a:seq<real>, i:int, j:int) : real
		requires 0 <= i <= |a|
		requires 0 <= j <= |a|
		decreases j - i;
	{
		// Fill in the correct specification here
		if i >= j then 1.0 else a[i] * product(a, i+1, j)
	}
	lemma product_right (a:seq<real>, i:int, j:int)
		requires 0 <= i <= |a|
		requires 0 <= j <= |a|
		requires i <= j
		ensures i < j ==> product(a, i, j) == product(a, i, j-1) * a[j-1]
		decreases j - i
	{
		if i == j
		{
			//assert(product(a, i, j) == 1.0);
		}
		else
		{
			//assert(i < j);
			product_right(a, i+1, j);
		}
	}
}

module Simple {
	import Specification

	/** [query(a, i, j)] returns the product of elements in [a] between index [i] inclusive and index [j] exclusive */
	method Main(a:array<real>, i:int, j:int) returns (res:real)
		requires 0 <= i <= a.Length
		requires 0 <= j <= a.Length
		ensures res == Specification.product(a[..], i, j)
	{
		// Fill in an implementation that verifies
		if(i < j)
		{
			var index := i;
			res := 1.0;
			while index < j
				invariant i <= index <= j
				invariant res == Specification.product(a[..], i, index)
			{
				res := res * a[index];
				index := index + 1;
				Specification.product_right(a[..], i, index);
			}
		}
		else
		{
		  res := 1.0;
		}
	}
}

module CumulativeArray {
	import Specification

	predicate is_cumulative_array_for(c:seq<real>, a:seq<real>)
	{
		|a| + 1 == |c| &&
		forall i :: 0 <= i < |c| ==> c[i] == Specification.product(a, 0, i)
	}

    /** [construct(a)] returns the the cumulative product array for a. */
	method construct(a:array<real>) returns (c:array<real>)
		ensures is_cumulative_array_for(c[..], a[..]);
	{
		c := new real[a.Length + 1];
		// Fill in an implementation that verifies
		c[0] := 1.0;
		var index := 1;
		while index < c.Length
			invariant 1 <= index <= c.Length
			invariant c[index-1] == Specification.product(a[..], 0, index-1)
			invariant forall k :: 0 <= k < index ==> c[k] == Specification.product(a[..], 0, k)
		{
			c[index] := c[index-1] * a[index-1];
			index := index + 1;
			Specification.product_right(a[..], 0, index-1);
		}
	}

	/** [query2(a, i, j)] returns the product of elements in [a] between index [i] inclusive and index [j] exclusive */
	method query2(c:array<real>, i:int, j:int, ghost a:array<real>) returns (res:real)
		requires 0 <= i < c.Length
		requires 0 <= j < c.Length
		requires a.Length + 1 == c.Length
		requires forall k :: 0 <= k < c.Length ==> c[k] != 0.0
		requires is_cumulative_array_for(c[..], a[..])
		ensures res == Specification.product(a[..],i,j)
	{
		// Fill in an implementation that verifies
		if i < j
		{
			var index;
			index := j;
      
      while index > i
        invariant i <= index <= j
        invariant Specification.product(a[..], 0, index) * Specification.product(a[..], index, j) == Specification.product(a[..], 0, j)
      {
				Specification.product_right(a[..], 0, index);
        index := index - 1;
      }
			
			res := c[j] / c[i];
		}
		else{
			res := 1.0;
		}
	}

	lemma unchanged_product (a:seq<real>, b:seq<real>, i:int)
		requires 0 <= i < |a|
		requires |a| == |b|
		requires forall k :: 0 <= k < i ==> a[k] == b[k];
		ensures Specification.product(a, 0, i) == Specification.product(b, 0, i)
	{
		if i == 0
		{
			
		}
		else
		{
			unchanged_product(a, b, i-1);
			Specification.product_right(a, 0, i);
			Specification.product_right(b, 0, i);
		}
	}

	lemma preserved (a:seq<real>, b:seq<real>, c:seq<real>, i:int)
		requires is_cumulative_array_for(c, a)
		requires 0 <= i < |a|
		requires |a| == |b|
		requires forall k :: 0 <= k < i ==> a[k] == b[k];
		ensures forall k :: 0 <= k <= i ==> c[k] == Specification.product(b, 0, k)
	{
		forall k | 0 <= k <= i
			ensures c[k] == Specification.product(b, 0, k)
		{
			unchanged_product(a, b, k);
		}
	}

	/** [update(c, a, i, v)] updates cell [a[i]] to value [v] 
	 and updates the cumulative array [c] accordingly,
	 while touching a few cells of [c] as possible */
	method update (c:array<real>, a:array<real>, i:int, v:real)
		requires a != c;
		requires 0 <= i < a.Length
		requires a.Length + 1 == c.Length
		requires is_cumulative_array_for(c[..], a[..])
		modifies c, a
		// [a] is updated appropriately
		ensures a[i] == v
		ensures forall k:: 0 <= k < a.Length && k != i ==> a[k] == old(a)[k]
		// [c] is updated appropriately
		ensures is_cumulative_array_for(c[..], a[..])
	{
		// Fill in an implementation that verifies
		assert(forall k :: 0 <= k < i+1 ==> c[k] == Specification.product(a[..], 0, k));
		a[i] := v;
		var index := i + 1;
		assert(forall k ::  0 <= k < i+1 ==> c[k] == old(c)[k]);
		preserved(old(a[..]), a[..], c[..], i);
		assert(forall k :: 0 <= k < i+1 ==> c[k] == Specification.product(a[..], 0, k));
		while index < c.Length
			invariant i+1 <= index <= c.Length
			invariant c[index-1] == Specification.product(a[..], 0, index-1)
			invariant forall k :: i+1 <= k < index ==> c[k] == Specification.product(a[..], 0, k)
			invariant forall k :: 0 <= k < i+1 ==> c[k] == Specification.product(a[..], 0, k)
			invariant a[i] == v
		{
			Specification.product_right(a[..], 0, index);
			c[index] := c[index-1] * a[index-1]; 
			index := index + 1;		
		}
	}
}

