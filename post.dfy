// NOTE: Do NOT modify anything other than the lines marked with TODOs

module PostOffice {

	datatype state = State(
		BoxCount: int,
		Time: int,
		CalledAt: int,
		Called: bool
	)

	predicate Valid(s:state)
	{
		// TODO: Write what it means for a state to be valid here
		s.BoxCount >= 0 &&
		0 <= s.Time <= 999 &&
		0 <= s.CalledAt <= 997 &&
		s.CalledAt <= s.Time &&
		((s.BoxCount > 20) ==> s.Called)
	}

	// Write appropriate pre and post conditions for all of the methods below

	method NewDay() returns (s:state)
		// TODO
		ensures Valid(s)
		ensures s.Time == 0
		ensures s.CalledAt == 0
		ensures s.BoxCount == 0
		ensures s.Called == false
	{
		s := State(0, 0, 0, false);
	}

	method DropOff(s:state) returns (s':state)
		// TODO
		requires Valid(s)
		requires 0 <= s.Time <= 996
		ensures Valid(s')
		ensures s'.BoxCount == s.BoxCount + 1
		ensures s.Time == s'.Time
	{
		s' := s.(BoxCount := s.BoxCount + 1);
		if s'.BoxCount > 20 && !s'.Called {
			/* Automatically trigger a call if the dropoff causes the
				 threshold to be crossed, and if the truck wasn't called yet. */
			s' := s'.(Called := true, CalledAt := s'.Time);
		}
	}    

	method PickUp(s:state) returns (s':state)
		// TODO
		requires Valid(s)
		ensures Valid(s')
		ensures s'.BoxCount == 0
		ensures s'.Called == false
		ensures s.Time == s'.Time
		ensures s.CalledAt == s'.CalledAt
	{
		s' := s.(BoxCount := 0, Called := false);
	}

	// Regular part of day, when pickups are allowed
	method TickMidday(drop:bool, pick:bool, s:state) returns (s':state)
		// TODO
		requires Valid(s)
		requires 0 <= s.Time <= 996
		ensures Valid(s')
		ensures s'.Time == s.Time + 1
		ensures pick ==> s'.Called == false
    	ensures pick ==> s'.BoxCount == 0
	{
		s' := s;
		if drop {
			s' := DropOff(s');
		}
		if pick {
			s' := PickUp(s');
		}
		s' := s'.(Time := s'.Time + 1);
	}

	// When finishing up the day
	method TickEoD(pick:bool, s:state) returns (s':state)
		// TODO
		requires Valid(s)
		requires 997 <= s.Time < 999
		ensures Valid(s')
		ensures s'.Time == s.Time + 1
		ensures pick ==> s'.Called == false
    	ensures pick ==> s'.BoxCount == 0
	{
		s' := s;
		if pick {
			s' := PickUp(s');
		}
		s' := s'.(Time := s'.Time + 1);
	}

	method WholeDay(dropoffs:seq<bool>)
		// TODO
		requires |dropoffs| == 997
	{
		var s := NewDay();
		var pickups := [false, false];
		while s.Time < 1000 - 1
			// TODO: Some more invariants are needed here to prove the two asserts below. Write them.
			invariant |pickups| == 2
			invariant s.BoxCount > 0 && s.Time == 1000 - 3 ==> true in pickups
			invariant s.BoxCount > 0 && s.Time == 1000 - 2 ==> true in pickups[..|pickups|-1]
			invariant Valid(s)
		{
			if s.Time < 1000 - 3 {
				s := TickMidday(dropoffs[s.Time], pickups[0], s);
			} else {
				s := TickEoD(pickups[0], s);
			}
			if s.Time == 1000 - 3 {
				if s.BoxCount > 0 && !s.Called {
					s := s.(Called := true, CalledAt := s.Time - 1); // -1 since already incremented by now
				}
			}
			pickups := pickups[1..] + [s.Called && s.CalledAt == s.Time - 1];
		}
		assert (s.Time == 1000 - 1);
		assert (s.BoxCount == 0);
	}
}

