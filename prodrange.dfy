module Specification {

	function method product (a:seq<real>, i:int, j:int) : real
		requires 0 <= i <= |a|
		requires 0 <= j <= |a|
		decreases j - i;
	{
		// Fill in the correct specification here
		if i >= j then 1.0 else a[j-1] * product(a, i, j-1)
	}
	
	lemma product_right (a:seq<real>, i:int, j:int)
		requires 0 <= i <= |a|
		requires 0 <= j <= |a|
		requires i <= j
		ensures if i < j then product(a, i, j) == product(a, i, j-1) * a[j-1] else product(a, i, j) == 1.0
		decreases j - i;
	{
	
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
			invariant is_cumulative_array_for(c[..index], a[..index-1])
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
		res := c[j] / c[i];
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
		a[i] := v;
		var index := i + 1;
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
