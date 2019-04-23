module Merge {
	predicate sorted(s: seq<int>)
	{
		forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
	}  

	// Helper lemma that you will likely need to call.
	// It states that if an element i is in the union of two multisets a and b,
	// Then it is in a or in b
	lemma set_union(a:multiset<int>, b:multiset<int>)
	ensures forall i :: i in a + b <==> i in a || i in b
	{ }

	/** [merge(a, b)] takes two sorted arrays, and returns a new sorted array [c]
	containing all elements of [a] and [b] */
	method merge(a:array<int>, b:array<int>) returns (c:array<int>)
		requires sorted(a[..])
		requires sorted(b[..])
		ensures sorted(c[..])
	// Multiset returns sets of elements, where each element can occur multiple times.
	// It is explained in more details in the online Dafny tutorial (https://rise4fun.com/Dafny/tutorial/Collections)
	// You will very likely need the set_union lemma provided earlier
		ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
	{
		c := new int[a.Length + b.Length];
		assert (a[..(a.Length)] == a[..]);
		assert (b[..(b.Length)] == b[..]);

		// TODO: Complete the implementation here.
		// We recommend you leave the previous two assertions at the beginning of your code,
		// and the last one at the end of your code
		var ai := 0;
		var bi := 0;
		var ci := 0;
   
		while ci < c.Length
			invariant 0 <= ai <= a.Length
			invariant 0 <= bi <= b.Length
			invariant ci == ai + bi
			invariant multiset(c[..ci]) == multiset(a[..ai]) + multiset(b[..bi])
			invariant sorted(a[..ai])
			invariant forall k :: bi < b.Length && 0 <= k < ai ==> a[k] <= b[bi]
			invariant sorted(b[..bi])
			invariant forall k :: ai < a.Length && 0 <= k < bi ==> b[k] <= a[ai]
			invariant forall k :: 0 <= k < ci ==> c[k] in a[..ai] || c[k] in b[..bi]
			invariant sorted(c[..ci])
		{
			if ai == a.Length
			{
				c[ci] := b[bi];
				bi := bi + 1;
			}
			else if bi == b.Length
			{
				c[ci] := a[ai];
				ai := ai + 1;
			}
			else if a[ai] <= b[bi]
			{
				c[ci] := a[ai];
				ai := ai + 1;
			}
			else
			{
				c[ci] := b[bi];
				bi := bi + 1;
			}
			ci := ci + 1;
		}
		assert (c[..(c.Length)] == c[..]);
	}
}
