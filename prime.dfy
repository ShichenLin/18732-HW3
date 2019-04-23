module Prime {
	////////////////////////////////////////////////////////
	// DO NOT CHANGE THE SPECIFICATION
	////////////////////////////////////////////////////////
	predicate method prime(n:int)
	{
		n >= 2 && forall i {:nowarn} :: 2 <= i < n ==> n % i != 0
	}

	method IsPrime(n:nat) returns (res:bool)
		requires n >= 2
		ensures res <==> prime(n)
	{
		// WRITE an implementation here that will satisfy the postcondition
		var i := 2;
		while i < n
		invariant 2 <= i <= n
		invariant forall k :: 2 <= k < i ==> n % k != 0 
		{
		  if n % i == 0 
		  {
			return false;
		  }
		  i := i + 1;
		}
		return true;
	}
}
