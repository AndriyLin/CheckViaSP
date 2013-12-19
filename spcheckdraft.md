
**Author**: Xuankang Lin

**What is this**: I am using strongest post-condition to prove that the assertions are not invalidated by the rely/guarantees. This is written in markdown so it's not fully formatted. The (3)s are the labels for the rely/guarantee in the .tex and 

**Rule: sp(H^P, C) => H**

-----

### *t*: cooperate()

// ### is followed by a function name, the following is to prove the assertions in this function. t means mutator thread, C means collector thread.


##### after 1 (tmp, phaseC, phase[t])

// ##### is followed by an assertion's location. In the parenthesis are the variables used in the assertion. (thus only need to check the rely/guarantees that change those variables)

*	(3)

		H&P:	{phaseC = phase[t] = tmp = X}
		C:		phaseC = X + 1
		
		sp = {phaseC = phase[t] + 1 = tmp + 1}
		sp => H, success

*	(4) change phase[t'] (another thread), independent
*	(11)(12)(13)(14) change o.f, independent
*	(15) change GREY, independent
*	(16) change o.color, independent
*	(17) change GREY, independent
*	(19) change phase[t'] (another thread), independent
*	(29) change lastRead[t'] (another thread), independent


##### after 3 (phase[t], phaseC, tmp)

*	(3)
	
		H&P:	{phase[t] (+) 1 = phaseC && phase[t] = phaseC} => false

*	(4)...... all independent, the same as above

all other assertions in cooperate() is Phase_inv[t], thus considered to be true all the time

-----

### *C*: handshake()

##### PRE (∀t·phase[t], phaseC)

*	(6)

		H&P:	{(∃t· phase[t] (+) 1 = phaseC) && (∀t·phase[t] = phaseC} => false

*	(11)(12)(13)(14) change o.f, independent
*	(15) change GREY, independent
*	(19)

		H&P:	{(∃t·phaseC = Async && phase[t] = Sync2) && (∀t·phase[t] = phaseC)} => false

*	(25) change roots, independent
*	(26)(27) change FREELIST, independent
*	(31) change lastWrite[t], independent

	
##### after 1 (∀t·phase[t], phaseC, tmp)

"after 1" is the same as "PRE" except that it adds the relation between tmp and phaseC. Since tmp is a local variable, everything is the same as the proof for "PRE".


##### after 2 (phaseC)

*	(6) change phase[t], independent
*	(11)(12)(13)(14) change o.f, independent
*	(15) change GREY, independent
*	(19) change phase[t], independent
*	(25) change roots, independent
*	(26)(27) change FREELIST, independent
*	(31) change lastWrite[t], independent


##### after 3 (phaseC)

exactly the same as "after 2"


##### after 4 while loop (for some t: phase[t], phaseC)

*	(6)

		H&P:	{phase[t] (+) 1 = phaseC && phase[t] = phaseC} => false

*	(11)(12)(13)(14) change o.f, independent
*	(15) change GREY, independent
*	(19)

		H&P:	{(phaseC = Async && phase[t] = Sync2) && (phase[t] = phaseC)} => false

*	(25) change roots, independent
*	(26)(27) change FREELIST, independent
*	(31) change lastWrite[t], independent


##### after 4 for loop / POST (∀t·phase[t], phaseC)

	similar to "PRE", except that the value of phase[t] and phase is different. The proof is the same as "PRE".

-----

### *t*: update()

##### PRE (x, f, v, roots[t])

*	(3) change phaseC, independent
*	(4) change phase[t'] of another mutator thread, independent
*	(11)
	
		H&P:	{x.f |-> _ && {x, v} ⊆ roots[t] && phase[t] = Async && stageC ∈ {Resting, Clear-or-Marking} && {x, v'} ⊆ reachables(roots[t])}
		C:		x.f |-> v'
			
		sp = {x.f |-> v' && v0 |-> _ && {x, v} ⊆ roots[t] && phase[t] = Async && stageC ∈ {Resting, Clear-or-Marking} && {x, v'} ⊆ reachables(roots[t])}
		// v0 is the original value
		sp => H, success
	
*	(12)
	
		H&P:	{x.f |-> _ && {x, v} ⊆ roots[t] && phase[t] = Sync1 && {x, v'} ⊆ reachables(roots[t]) && v' ∈ GREY}
		C:		x.f |-> v'
			
		sp = {x.f |-> v' && v0 |-> _ && {x, v} ⊆ roots[t] && phase[t] = Sync1 && {x, v'} ⊆ reachables(roots[t]) && v' ∈ GREY}
		// v0 is the original value
		sp => H, success
	
*	(13)(14)
	
	similar to (11) and (12), C only assign a new value to x.f, it won't affect roots[t]. In H, "x.f |-> _" so any assignment won't invalidate it.
		
*	(15) change GREY, independent
*	(16) change o.color, independent
*	(17) change GREY, independent
*	(19) change phase[t], independent
*	(29) change lastRead[t], independent


##### after 3 (phast[t], stageC, x.f, old, w, GREY, BLACK)

	H:	phase[t] = Sync2 || stageC = TRACING
		=>
		x.f |-> old || (∃w·x.f |-> w && w ∈ GREY U BLACK)

*	(3) change phaseC, independent
*	(4) change phase[t'] of another mutator thread, independent
*	(11)

		H&P:	{(phase[t] = Sync2 || stageC = TRACING) && (phase[t] = Async && stageC ∈ {Resting, ClearOrMarking})} == false

*	(12)

		// phase[t] = Sync1 => stageC = ClearOrMarking
		H&P:	(phase[t] = Sync2 || stageC = TRACING) && (phase[t] = Sync1)} == false

*	(13)

		H&P:	phase[t] = Sync2 && {x, v'} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (x.f |-> old && old ∈ GREY U BLACK || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		C:		x.f |-> v'

		sp = ∃y·{x.f |-> v' && phase[t] = Sync2 && {x, v'} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (y |-> old && old ∈ GREY U BLACK || ∃w· y |-> w && w ∈ GREY U BLACK)}

		sp => H? success

*	(14)

		H&P:	stageC = Tracing && {v', x} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (x.f |-> old && old ∈ GREY U BLACK || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		C:		x.f |-> v'

		sp = ∃y·{x.f |-> v' && stageC = Tracing && {v', x} ⊆ reachables(roots[t]) && {v', old} ⊆ GREY U BLACK && (y |-> old && old ∈ GREY U BLACK || ∃w· y |-> w && w ∈ GREY U BLACK)}

		sp => H? success

*	(15) only increase set GREY, those already in GREY are not affected
*	(16) only set an obj to BLACK, those already in GREY U BLACK are not affected
*	(17)

		// the "x.f |-> old" branch is independent with respect to GREY(o), thus only consider the other branch

		H&P:	stageC = Tracing && ∀t·phaseC = phase[t] = Async && w.color = BLACK && GREY(w) = n ≥ 1 && (x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		C:		GREY(w) = n-1
		
		sp = ∃y·{GREY(w) = n-1 && stageC = Tracing && ∀t·phaseC = phase[t] = Async && w.color = BLACK && y = n ≥ 1 && (x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)}
		sp => H? success

*	(19)

		H&P:	phase[t] = Sync2 && phaseC = Async && roots[t] ⊆ GREY && (x.f |-> old || (∃w·x.f |-> w && w ∈ GREY U BLACK))
		C:		phase[t] = Async
		
		sp = ∃y·{phase[t] = Async && y = Sync2 && phaseC = Async && roots[t] ⊆ GREY && (x.f |-> old || (∃w·x.f |-> w && w ∈ GREY U BLACK))}
		sp => H? success

*	(29) change lastRead[t], independent


##### after 4 (phase[t], stageC, x.f, GREY, BLACK)

	H:	phase[t] = Sync2 || stageC = Tracing
			=> (x.f |-> old || (∃w· x.f |-> w && w ∈ GREY U BLACK)) && old ∈ GREY U BLACK
		&&
		phase[t] = Sync1
			=> old ∈ GREY U BLACK

*	(3) change phaseC, independent
*	(4) change phase[t] of another mutator thread, independent
*	(11)

		H&P:	(phase[t] = Sync2 || stageC = Tracing || phase[t] = Sync1) && (phase[t] = Async && stageC ∈ {RESTING, CLEAR_OR_MARKING}) = FALSE
		
*	(12)

		H&P:	phase[t] = Sync1 && {x, v'} ⊆ reachables(roots[t]) && v' ∈ GREY && x.f |-> _ && old ∈ GREY U BLACK
		C:		x.f |-> v'
		
		sp = ∃y·{x.f |-> v' && phase[t] = Sync1 && {x, v'} ⊆ reachables(roots[t]) && v' ∈ GREY && y |-> _ && old ∈ GREY U BLACK}

		sp => H? success
		
*	(13)

		// the same as (13) in "after 3"

		H&P:	phase[t] = Sync2 && {x, v'} ⊆ reachables(roots[t]) && {v', old} ⊆ GREY U BLACK && (x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		C:		x.f |-> v'

		sp = ∃y·{x.f |-> v' && phase[t] = Sync2 && {x, v'} ⊆ reachables(roots[t]) && {v', old} ⊆ GREY U BLACK && (y |-> old || ∃w· y |-> w && w ∈ GREY U BLACK)}

		sp => H? success

*	(14)

		// the same as (14) in "after 3"
		
		H&P:	stageC = Tracing && {v', x} ⊆ reachables(roots[t]) && {v', old} ⊆ GREY U BLACK && (x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		C:		x.f |-> v'

		sp = ∃y·{x.f |-> v' && stageC = Tracing && {v', x} ⊆ reachables(roots[t]) && {v', old} ⊆ GREY U BLACK && (y |-> old || ∃w· y |-> w && w ∈ GREY U BLACK)}

		sp => H? success
		
*	(15) only add object into GREY, those already in GREY are not affected
*	(16) only set obj to BLACK, those already in BLACK are not affected
*	(17)

		// both "old" and "w" can be the object o in (17), thus consider them twice

		H&P_1:	stageC = Tracing && ∀t·phase[t] = phaseC = Async && old.color = BLACK && GREY(old) = n ≥ 1 && old ∈ GREY U BLACK && (x.f |-> old || (∃w· x.f |->w && w ∈ GREY U BLACK))
		C:		GREY(old) = n - 1
		
		sp_1 = ∃y·{GREY(old) = n - 1 && stageC = Tracing && ∀t·phase[t] = phaseC = Async && old.color = BLACK && y = n ≥ 1 && old ∈ GREY U BLACK && (...)}
		sp_1 => H? success


		H&P_2:	stageC = Tracing && ∀t·phase[t] = phaseC = Async && w.color = BLACK && GREY(w) = n ≥ 1 && old ∈ GREY U BLACK && (∃w· x.f |->w && w ∈ GREY U BLACK)
		C:		GREY(w) = n - 1
		
		sp_2 = ∃y·{GREY(w) = n-1 && stageC = Tracing && ∀t·phase[t] = phaseC = Async && w.color = BLACK & y = n ≥ 1 && old ∈ GREY U BLACK && (...)}
		sp_2 => H? success

*	(19)

		H&P:	phase[t] = Sync2 && phaseC = Async && roots[t] ⊆ GREY && old ∈ GREY U BLACK && (x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		C:		phase[t] = Async
		
		sp = ∃y·{phase[t] = Async && y = Sync2 && phaseC = Async && roots[t] ⊆ GREY && old ∈ GREY U BLACK && (x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)}
		sp => H? success

*	(29) change lastRead[t], independent


##### after 5 (phase[t], stageC, x.f, GREY, BLACK)

	H:	phase[t] = Sync2 || stageC = Tracing
			=> (x.f |-> old || (∃w· x.f |-> w && w ∈ GREY U BLACK)) && {old, v} ⊆ GREY U BLACK
		&&
		phase[t] = Sync1
			=> {old, v} ⊆ GREY U BLACK

*	(3) change phaseC, independent
*	(4) change phase[t'] of another mutator thread, independent
*	(11)

		H&P:	phase[t] = Async && stageC ∈ {RESTING, CLEAR_OR_MARKING} && (phase[t] = Sync2 || stageC = Tracing || phase[t] = Sync1) == false
		
*	(12)

		H&P:	phase[t] = Sync1 && {old, v} ⊆ GREY U BLACK && {x, v'} ⊆ reachables(roots[t]) && v' ∈ GREY && x.f |-> _
		C:		x.f |-> v'
		
		sp = ∃y·{x.f |-> v' && phase[t] = Sync1 && {old, v} ⊆ GREY U BLACK && {x, v'} ⊆ reachables(roots[t]) && v' ∈ GREY && y |-> _}
		
		sp => H? success

*	(13)

		H&P:	phase[t] = Sync2 && {x, v'} ⊆ reachables(roots[t]) && {v', old} ⊆ GREY U BLACK && (x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK) && {old, v} ⊆ GREY U BLACK
		C:		x.f |-> v'
		
		sp = ∃y·{x.f |-> v' && phase[t] = Sync2 && {x, v'} ⊆ reachables(roots[t]) && {v', old} ⊆ GREY U BLACK && (y |-> old || ∃w· y |-> w && w ∈ GREY U BLACK) && {old, v} ⊆ GREY U BLACK}
		
		sp => H? success

*	(14)

		H&P:	stageC = Tracing && {v', x} ⊆ reachables(roots[t]) && {v', old} ⊆ GREY U BLACK && (x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK) && {old, v} ⊆ GREY U BLACK
		C:		x.f |-> v'
		
		sp = ∃y·{x.f |-> v' && stageC = Tracing && {v', x} ⊆ reachables(roots[t]) && {v', old} ⊆ GREY U BLACK && (y |-> old || ∃w· y |-> w && w ∈ GREY U BLACK) && {old, v} ⊆ GREY U BLACK}
		
		sp => H? success

*	(15) only add object into GREY, those already in GREY are not affected
*	(16) only set object to BLACK, those already in BLACK are not affected
*	(17)

		// GREY(o) ==> GREY(w)
		H&P_1:	stageC = Tracing && ∀t·phaseC = phase[t] = Async && w.color = BLACK && GREY(w) = n ≥ 1 && (∃w· x.f |-> w && w ∈ GREY U BLACK) && {old, v} ⊆ GREY U BLACK
		C_1:	GREY(w) = n - 1
		
		sp_1 = ∃y·{GREY(w) = n-1 && stageC = Tracing && ∀t·phaseC = phase[t] = Async && w.color = BLACK && y = n ≥ 1 && (...) && {old, v} ⊆ GREY U BLACK}

		sp_1 => H? success


		// GREY(o) ==> GREY(old)
		H&P_2:	stageC = Tracing && ∀t·phaseC = phase[t] = Async && old.color = BLACK && GREY(old) = n ≥ 1 && (.. || ..) && {old, v} ⊆ GREY U BLACK
		C_2:	GREY(old) = n - 1
		
		sp_2 = ∃y·{GREY(old) = n-1 && stageC = Tracing && ∀t·phaseC = phase[t] = Async && old.color = BLACK && y = n ≥ 1 && (.. || ..) && {old, v} ⊆ GREY U BLACK}
		
		sp_2 => H? success
		
		// GREY(o) ==> GREY(v)
		H&P_3:	stageC = Tracing && ∀t·phaseC = phase[t] = Async && v.color = BLACK && GREY(v) = n ≥ 1 && (.. || ..) && {old, v} ⊆ GREY U BLACK
		C_3:	GREY(v) = n - 1
		
		sp_3 = ∃y·{GREY(v) = n-1 && stageC = Tracing && ∀t·phaseC = phase[t] = Async && v.color = BLACK && y = n ≥ 1 && (.. || ..) && {old, v} ⊆ GREY U BLACK}
		
		sp_3 => H? success

*	(19)

		H&P:	phaseC = Async && roots[t] ⊆ GREY && phase[t] = Sync2 && (.. || ..) && {old, v} ⊆ GREY U BLACK
		C:		phase[t] = Async
		
		sp = ∃y·{phase[t] = Async && phaseC = Async && roots[t] ⊆ GREY && y = Sync2 && (.. || ..) && {old, v} ⊆ GREY U BLACK}
		
		sp => H? success

*	(29) only change lastRead[t], independent


##### after 6

the same as "after 5"


##### after 7 (phase[t], stageC, x.f, GREY, BLACK)

	H:	phase[t] = Sync2 || stageC = Tracing
			=>	(x.f |-> v || (∃w· x.f |-> w && w ∈ GREY U BLACK)) && {old, v} ⊆ GREY U BLACK
		&&
		phase[t] = Sync1
			=> {old, v} ⊆ GREY U BLACK

*	(3) change phaseC, independent
*	(4) change phase[t'] of another mutator thread, independent
*	(11)

		H&P:	phase[t] = Async && stageC ∈ {RESTING, CLEAR_OR_MARKING} && (phase[t] = Sync2 || stageC = Tracing || phase[t] = Sync1) == false

*	(12)

		H&P:	phase[t] = Sync1 && {x, v'} ⊆ reachables(roots[t]) && v' ∈ GREY && x.f |-> _ && {old, v} ⊆ GREY U BLACK
		C:		x.f |-> v'
		
		sp = ∃y·{x.f |-> v' && phase[t] = Sync1 && {x, v'} ⊆ reachables(roots[t]) && v' ∈ GREY && y |-> _ && {old, v} ⊆ GREY U BLACK}

		sp => H? success

*	(13)

		H&P:	phase[t] = Sync2 && {x, v'} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (x.f |-> v || ∃w· x.f |-> w && w ∈ GREY U BLACK) && {old, v} ⊆ GREY U BLACK
		C:		x.f |-> v'
		
		sp = ∃y·{x.f |-> v' && phase[t] = Sync2 && {x, v'} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (y |-> v || ∃w· y |-> w && w ∈ GREY U BLACK) && {old, v} ⊆ GREY U BLACK}
		
		sp => H? success

*	(14)

		H&P:	stageC = Tracing && {v', x} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (x.f |-> v || ∃w· x.f |-> w && w ∈ GREY U BLACK) && {old, v} ⊆ GREY U BLACK
		C:		x.f |-> v'
		
		sp = ∃y·{x.f |-> v' && stageC = Tracing && {v', x} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (y |-> v || ∃w· y |-> w && w ∈ GREY U BLACK)} && {old, v} ⊆ GREY U BLACK
		
		sp => H? success

*	(15) only add object into GREY, those already in GREY are not affected
*	(16) only set object to BLACK, those already in BLACK are not affected
*	(17)

		// GREY(o) ==> GREY(w)
		H&P_1:	stageC = Tracing && ∀t·phaseC = phase[t] = Async && w.color = BLACK && GREY(w) = n ≥ 1 && (∃w· x.f |-> w && w ∈ GREY U BLACK) && {old, v} ⊆ GREY U BLACK
		C_1:	GREY(w) = n - 1
		
		sp_1 = ∃y·{GREY(w) = n-1 && stageC = Tracing && ∀t·phaseC = phase[t] = Async && w.color = BLACK && y = n ≥ 1 && (...) && {old, v} ⊆ GREY U BLACK}

		sp_1 => H? success


		// GREY(o) ==> GREY(old)
		H&P_2:	stageC = Tracing && ∀t·phaseC = phase[t] = Async && old.color = BLACK && GREY(old) = n ≥ 1 && (.. || ..) && {old, v} ⊆ GREY U BLACK
		C_2:	GREY(old) = n - 1
		
		sp_2 = ∃y·{GREY(old) = n-1 && stageC = Tracing && ∀t·phaseC = phase[t] = Async && old.color = BLACK && y = n ≥ 1 && (.. || ..) && {old, v} ⊆ GREY U BLACK}
		
		sp_2 => H? success
		
		// GREY(o) ==> GREY(v)
		H&P_3:	stageC = Tracing && ∀t·phaseC = phase[t] = Async && v.color = BLACK && GREY(v) = n ≥ 1 && (.. || ..) && {old, v} ⊆ GREY U BLACK
		C_3:	GREY(v) = n - 1
		
		sp_3 = ∃y·{GREY(v) = n-1 && stageC = Tracing && ∀t·phaseC = phase[t] = Async && v.color = BLACK && y = n ≥ 1 && (.. || ..) && {old, v} ⊆ GREY U BLACK}
		
		sp_3 => H? success

*	(19)

		H&P:	phase[t] = Sync2 && phaseC = Async && roots[t] ⊆ GREY && (.. || ..) && {old, v} ⊆ GREY U BLACK
		C:		phase[t] = Async
		
		sp = ∃y·{phase[t] = Async && y = Sync2 && phaseC = Async && roots[t] ⊆ GREY && (.. || ..) && {old, v} ⊆ GREY U BLACK}
		
		sp => H? success

*	(29) only change lastRead[t], independent

-----

### *C*: EmptyCollectorStack()

##### S (phase[t], phaseC, stageC)

	H: (∀t· phase[t] = phaseC = Async) && stageC = Tracing

*	(6)

		H&P:	{∃t· phase[t] (+) 1 = phaseC && ∀t· phase[t] = phaseC} == false

*	(11)..(14) change x.f, independent
*	(15) change GREY, independent
*	(19)

		H&P:	{phase[t] = Sync2 && ∀t· phase[t] = phaseC = Async} == false

*	(25) change a register & roots[t], independent
*	(26)(27) change freelist & obj's color, independent
*	(31) change bucket[t], independent

	So now S is proved to be true with respect to all relies, from now on, S can be used without checking again.


##### before 7 (bucket[C], reachables(), GREY)

	H:	S && bucket[C] = X && reachables(X) = Y && X ⊆ GREY

*	(6) change phase[t], independent
*	(11)..(14) change x.f, independent
*	(15) only add object to GREY, those already in GREY are not affected
*	(19) change phase[t], independent
*	(25) change a register & roots[t], reachables(X) starts from X, thus independent
*	(26)(27) change freelist & obj's color, independent
*	(31) change bucket[t], independent


##### after 7 (bucket[C])

	H:	S && bucket[C] ≠ ∅

*	(6) change phase[t], independent
*	(11)..(14) change x.f, independent
*	(15) change GREY, independent
*	(19) change phase[t], independent
*	(25) change register & roots[t], independent
*	(26)(27) change freelist & obj's color, independent
*	(31) change bucket[t], independent


##### after 8 (bucket[C], GREY)

	H: S && ob ∈ bucket[C] && ob ∈ GREY

The variables that may be changed are subset of "before 7". So it's the same, all independent


##### after 10 (ob.color, bucket[C], GREY)

	H:	S && ob.color = WHITE && ob ∈ bucket[C] && ob ∈ GREY

*	(6) change phase[t], independent
*	(11)..(14) change x.f, independent
*	(15) only add object into GREY, those already in GREY are not affected
*	(19) change phase[t], independent
*	(25) change a register & roots[t], independent
*	(26)(27)

		H&P:	{ob.color = WHITE && ob.color = BLUE && ...} == false

*	(31) change bucket[t], independent


##### after 11

	H:	S && ob.color = WHITE && ob ∈ bucket[C] && ob ∈ GREY  △= Q

the same as "after 10"

So now Q is proved to be true with respect to all relies, from now on, Q can be used without checking again.


##### after 12 (ob.f, GREY, BLACK)

Q is not taken into consideration, since it's proved to be correct under all relies

	H:	Q && ob.f |-> o'' || (o'' ∈ GREY U BLACK && (∃v· ob.f |-> v && v ∈ GREY U BLACK))

*	(6) change phase[t], independent
*	(11)

		H&P:	{stageC ∈ {RESTING, CLEAR_OR_MARKING} && stageC = Tracing} == false

*	(12)

		H&P:	{phase[t] = Sync1 && ∀t· phase[t] = phaseC = Async} == false

*	(13)

		H&P:	{phase[t] = Sync2 && ∀t· phase[t] = phaseC = Async} == false

*	(14)

		H&P:	{ob, v'} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (ob.f |-> o'' || ∃v· ob.f |-> v && v ∈ GREY U BLACK) && o'' ∈ GREY U BLACK
		C:		ob.f |-> v'
		
		sp = ∃y·{ob.f |-> v' && {ob, v'} ⊆ reachables(roots[t]) && {v', o''} ⊆ GREY U BLACK && (y |-> o'' || ∃v· y |-> v && v ∈ GREY U BLACK)}
		
	sp => H? success

*	(15) only add object into GREY, those already in GREY are not affected
*	(19) change phase[t], independent
*	(25) change register & roots[t], independent
*	(26)

		H&P:	{(phase[t] ≠ Async || stageC = CLEAR_OR_MARKING) && (∀t·phase[t] = Async && stageC = Tracing)} == false

*	(27) set obj's color to BLACK, those already in BLACK are not affected
*	(31) change bucket[t], independent


##### after 13 (ob.j, GREY, BLACK, o''.color)

	H:	Q && (ob.f |-> o'' || o'' ∈ GREY && (∃v· ob.f |-> v && v ∈ GREY U BLACK)) && o''.color = WHITE

*	(6) change phase[t], independent
*	(11)

		H&P:	{stageC ∈ {RESTING, CLEAR_OR_MARKING} && stageC = Tracing} == false

*	(12)

		H&P:	{phase[t] = Sync1 && ∀t· phase[t] = phaseC = Async} == false

*	(13)

		H&P:	{phase[t] = Sync2 && ∀t· phase[t] = phaseC = Async} == false

*	(14)

		H&P:	{ob, v'} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (ob.f |-> o'' && o'' ∈ GREY U BLACK || o'' ∈ GREY && (∃v· ob.f |-> v && v ∈ GREY U BLACK)) && o''.color = WHITE
		C:		ob.f |-> v'
		
		sp = ∃y·{ob.f |-> v' && {ob, v'} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (y |-> o'' && o'' ∈ GREY U BLACK || o'' ∈ GREY && (∃v· y |-> v && v ∈ GREY U BLACK)) && o''.color = WHITE}

	sp => H? success

*	(15) only add object into GREY, those already in GREY are not affected
*	(19) change phase[t], independent
*	(25) change register & roots[t], independent
*	(26)(27)

		H&P:	{o''.color = WHITE && o''.color == BLUE && ..} == false

*	(31) change bucket[t], independent


##### after 14 (ob.f, GREY, BLACK, o''.color)

	H:	Q && (ob.f |-> o'' || (∃v· ob.f |-> v && v ∈ GREY U BLACK)) && o''.color = WHITE && o'' ∈ GREY

*	(6) change phase[t], independent
*	(11)

		H&P:	{stageC ∈ {RESTING, CLEAR_OR_MARKING} && stageC = Tracing} == false

*	(12)

		H&P:	{phase[t] = Sync1 && ∀t· phase[t] = phaseC = Async} == false

*	(13)

		H&P:	{phase[t] = Sync2 && ∀t· phase[t] = phaseC = Async} == false

*	(14)

		H&P:	{ob, v'} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (ob.f |-> o'' || (∃v· ob.f |-> v && v ∈ GREY U BLACK)) && o''.color = WHITE && o'' ∈ GREY
		C:		ob.f |-> v'
		
		sp = ∃y·{ob.f |-> v' && {ob, v'} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (y |-> o'' || (∃v· y |-> v && v ∈ GREY U BLACK)) && o''.color = WHITE && o'' ∈ GREY}

	sp => H? success

*	(15) only add object into GREY, those already in GREY are not affected
*	(19) change phase[t], independent
*	(25) change register & roots[t], independent
*	(26)(27)

		H&P:	{o''.color = WHITE && o''.color = BLUE && ..} == false

*	(31) change bucket[t], independent


##### after 15 (ob.f, GREY, BLACK)

	H:	S && (∀ v ∈ Obj, f ∈ fields(ob)· ob.f |-> v => v ∈ BLACK U GREY) △= R

*	(6) change phase[t], independent
*	(11)

		H&P:	{stageC ∈ {RESTING, CLEAR_OR_MARKING} && stageC = Tracing} == false

*	(12)

		H&P:	{phase[t] = Sync1 && ∀t· phase[t] = phaseC = Async} == false

*	(13)

		H&P:	{phase[t] = Sync2 && ∀t· phase[t] = phaseC = Async} == false

*	(14)

		H&P:	{ob, v'} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (∀ v ∈ Obj, f ∈ fields(ob)· ob.f |-> v => v ∈ BLACK U GREY)
		C:		ob.f |-> v'
		
		sp = ∃y·{ob.f |-> v' && {ob, v'} ⊆ reachables(roots[t]) && {v'} ⊆ GREY U BLACK && (∀ v ∈ Obj, f ∈ fields(ob)· y |-> v => v ∈ BLACK U GREY)}

	sp => H? success

*	(15) only add object into GREY, those already in GREY are not affected
*	(19) change phase[t], independent
*	(25) change register & roots[t], independent
*	(26)

		H&P:	{(phase[t] ≠ Async || stageC = CLEAR_OR_MARKING) && (∀t·phase[t] = Async && stageC = Tracing)} == false

*	(27) set obj's color to BLACK, those already in BLACK are not affected
*	(31) change bucket[t], independent

Therefore R is proved with respect to all relies, from now on, R can be used without checking again.


##### after 16 (ob.color)

	H:	R && ob.color = BLACK

*	(6) change phase[t], independent
*	(11)..(14) change ob.f, independent
*	(15) change GREY, independent
*	(19) change phase[t], independent
*	(25) change register & roots[t], independent
*	(26)(27)

		H&P:	{ob.color = BLACK && ob.color = BLUE} == false

*	(31) change bucket[t], independent


##### after 18 (BLACK, reachables(), GREY, bucket[C])

	H:	S && X ⊆ BLACK && reachables(Y) ⊆ reachables(GREY) U BLACK && bucket[C] ≠ ∅

*	(6) change phase[t], independent
*	(11)..(14) here X and Y are local variables, setting ob.f won't change them, thus independent
*	(15) only add object into GREY, those already in GREY are not affected
*	(19) change phase[t], independent
*	(25) change register & roots[t], independent
*	(26)

		H&P:	{(phase[t] ≠ Async || stageC = CLEAR_OR_MARKING) && (∀t·phase[t] = Async && stageC = Tracing)} == false

*	(27) set obj's color to BLACK, those already in BLACK are not affected
*	(31) change bucket[t], independent

-----

### *C*: Trace

##### after 3 (bucket[t], GREY)

	H:	{bucket[t] ≠ ∅ && GREY ≠ ∅} △= Q

**TODO**
