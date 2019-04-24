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
		(s.BoxCount >= 0) 
		&& (0 <= s.Time <= 1000 - 1) 
		&& (0 <= s.CalledAt < 1000 - 3)
		&& s.CalledAt <= s.Time
		&& (s.Called ==> (s.Time - s.CalledAt <= 2))
	}

	// Write appropriate pre and post conditions for all of the methods below

	method NewDay() returns (s:state)
		// TODO
		ensures s.BoxCount == 0
		ensures s.Time == 0
		ensures s.CalledAt == 0
		ensures s.Called == false
		ensures Valid(s)
	{
		s := State(0, 0, 0, false);
	}

	method DropOff(s:state) returns (s':state)
		// TODO
		requires Valid(s)
		requires s.Time < 997

		ensures s'.BoxCount == s.BoxCount + 1
		// ensures s.Called ==> s'.Called
		ensures if (s.BoxCount + 1 > 20 && !s.Called) 
			then s'.Called && s'.CalledAt == s'.Time 
			else s'.Called == s.Called && s'.CalledAt == s.CalledAt
		ensures s'.Time == s.Time
		ensures Valid(s')
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
		requires s.Called == true
		requires s.BoxCount > 0

		ensures s'.BoxCount == 0
		ensures s'.Called == false
		ensures s'.Time == s.Time
		ensures s'.CalledAt == s.CalledAt
		ensures Valid(s')
	{
		s' := s.(BoxCount := 0, Called := false);
	}

	// Regular part of day, when pickups are allowed
	method TickMidday(drop:bool, pick:bool, s:state) returns (s':state)
		// TODO
		requires Valid(s)
		requires s.Time < 1000 - 3
		requires s.Called && s.Time - s.CalledAt == 2 ==> pick
		requires pick ==> s.Called
		requires pick ==> s.BoxCount > 0
		requires pick ==> s.Called && s.BoxCount > 0
		
		ensures s'.CalledAt < s'.Time
		ensures s'.Time <= 1000 - 3
		ensures s'.Time == s.Time + 1
		ensures (s'.Called ==> (s'.Time - s'.CalledAt <= 2))
		// ensures drop && (if (s.BoxCount + 1 > 20 && !s.Called) 
		// 	then s'.Called && s'.CalledAt == s'.Time 
		// 	else s'.Called == s.Called && s'.CalledAt == s.CalledAt)
		ensures Valid(s')
	{
		s' := s;
		if drop {
			s' := DropOff(s');
			assert (s'.Called ==> (s'.Time - s'.CalledAt <= 2));
			// assert(if (s.BoxCount + 1 > 20 && !s.Called) 
			// then s'.Called && s'.CalledAt == s'.Time 
			// else s'.Called == s.Called && s'.CalledAt == s.CalledAt);
		}
		
		if pick {
			s' := PickUp(s');
			assert (s'.Called ==> (s'.Time - s'.CalledAt == 2));
		}
		assert (s'.Called ==> (s'.Time - s'.CalledAt <= 2));
		s' := s'.(Time := s'.Time + 1);
		
	}

	// When finishing up the day
	method TickEoD(pick:bool, s:state) returns (s':state)
		// TODO
		requires Valid(s)
		requires 1000 - 3 <= s.Time < 1000 - 1
		requires s.CalledAt < 1000 - 3
		requires s.Called && s.Time - s.CalledAt == 2 ==> pick
		requires pick ==> s.Called && s.BoxCount > 0

		ensures s'.CalledAt < s'.Time
		ensures 1000 - 3 < s'.Time <= 1000
		ensures s'.Time == s.Time + 1
		ensures Valid(s')
	{
		s' := s;
		if pick {
			assert s'.Called == true;
			s' := PickUp(s');
		}
		s' := s'.(Time := s'.Time + 1);
	}

	method WholeDay(dropoffs:seq<bool>)
		// TODO
		requires |dropoffs| == 1000
	{
		var s := NewDay();
		var pickups := [false, false];
		while s.Time < 1000 - 1
			// TODO: Some more invariants are needed here to prove the two asserts below. Write them.
			decreases  1000 - 1 - s.Time
			invariant Valid(s)
			invariant s.Called ==> (0 < s.Time - s.CalledAt <= 2)

			invariant 0 <= s.Time <= 1000 - 1
			invariant |pickups| == 2
			invariant old(|dropoffs|) == |dropoffs|
			invariant s.BoxCount > 0 && s.Time == 1000 - 3 ==> s.Called
			invariant s.BoxCount > 0 && s.Time == 1000 - 3 ==> true in pickups
			invariant s.BoxCount > 0 && s.Time == 1000 - 2 ==> true in pickups[..(|pickups|-1)]
		{
			var stime_old := s.Time;
			var pickups_old := pickups;
			var calledat_old := s.CalledAt;
			var scalled_old := s.Called;
			assert s.Called && s.CalledAt == stime_old - 2 ==> pickups[0];
			if s.Time < 1000 - 3 {
				s := TickMidday(dropoffs[s.Time], pickups[0], s);
				assume scalled_old && s.CalledAt == calledat_old; // TODO
				assert scalled_old ==> s.CalledAt == calledat_old;
			} else {
				assert s.BoxCount > 0 ==> pickups[0] || pickups[1];
				s := TickEoD(pickups[0], s);
			}
			if s.Time == 1000 - 3 {
				if s.BoxCount > 0 && !s.Called {
					s := s.(Called := true, CalledAt := s.Time - 1); // -1 since already incremented by now
				}
			}
			assume scalled_old ==> !s.Called;
			assert scalled_old ==> s.CalledAt == calledat_old;
			pickups := pickups[1..] + [s.Called && s.CalledAt == s.Time - 1];

			assert s.Called ==> (s.Time - s.CalledAt == 1 || s.Time - s.CalledAt == 2);
			assert (scalled_old && calledat_old == stime_old - 1 ==> pickups_old[1]) ==> scalled_old == s.Called;
			assert scalled_old ==> s.CalledAt == calledat_old;
			assert pickups_old[1] == pickups[0];
			assert stime_old == s.Time - 1;
			assert scalled_old && calledat_old == stime_old - 1 ==> pickups_old[1];
			
			assert s.Called && s.CalledAt == s.Time - 2 ==> pickups[0];
			assert s.Called && s.CalledAt == s.Time - 1 ==> pickups[1];
			assert s.Called ==> true in pickups;
		}
		assert (s.Time == 1000 - 1);
		assert (s.BoxCount == 0);
	}
}
