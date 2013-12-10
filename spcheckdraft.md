
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

*	(3) change phaseC, independent
*	(4) change phase[t'] of another mutator thread, independent
*	(11)

		H&P:	{(phase[t] = Sync2 || stageC = TRACING) && (phase[t] = Async && stageC ∈ {Resting, ClearOrMarking})} => false

*	(12)

		// phase[t] = Sync1 => stageC = ClearOrMarking
		H&P:	{(phase[t] = Sync2 || stageC = TRACING) && (phase[t] = Sync1)} => false

*	(13)

		H&P:	{phase[t] = Sync2 && (x.f |-> old || (∃w· x.f|->w && w ∈ GREY U BLACK)) && .... TODO}
		C:		x.f |-> v

