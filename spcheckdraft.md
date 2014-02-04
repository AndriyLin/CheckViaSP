
**Author**: Xuankang Lin

**What is this**: I am using strongest post-condition to prove that the assertions are not invalidated by the rely/guarantees. This is written in markdown and can be converted to HTML for viewing. So please forgive the poor format.

**Rule**: sp(H & P, C) =?> H, here H is some assertion, P is the precondition of some rely, C is the command of that rely. If sp(H & P, C) => H, H is stable with respect to that rely.

**Notations**: Since this is a draft, I only use the notations that are easy to enter. && for logical and, || for logical or.

**Structure**:

*	First list all the relies for mutator thread and for collector thread.
*	Then prove all the invariants are stable.
*	Then prove the assertions of each functions mentioned in the .tex file.

**Notes**:

When I started proving, I commented out all the text in the .tex file and used that number order for each invariant/rely/guarantee. However, it seems that the number order is a little different with text on..

Only those assertions written in the .tex file are proved.

-----

### Relies

in the form of Precondition & Command

##### relies for mutator thread

-----
// for copying

*	Phase_rely_t
*	Phase_rely_t'
*	UpdateResting
*	UpdateS1
*	UpdateS2
*	UpdateTracing
*	MarkGrey
*	MarkBlack
*	RemoveGrey
*	PhaseS2
*	LoadWhite
*	LoadBlack
*	NewWhite
*	NewBlack
*	Bucket_rely_t
*	Bucket_rely_t'

-----

**TODO** rewrite the text numbers

*	**Phase_rely_t**, on collector thread, NO.(three) in .tex

		{∀t· phase[t] = phaseC =X}
			phaseC = X (+) 1

*	**Phase_rely_t'**, on another mutator thread, NO.(four) in .tex

		{∃t'· t' ≠ t && phase[t'] (+) 1 = phaseC = X}
			phase[t'] = X

*	**UpdateResting**, on another mutator thread, NO.(twelve) in .tex

		{phase[t] = Async && stageC ∈ {RESTING, CLEAR_OR_MARKING} && {o, v} ⊆ reachables(roots[t]) && o.f |-> _}
			o.f |-> v

*	**UpdateS1**, on another mutator thread, NO.(thriteen), former (12)

		{phase[t] = Sync1 && {o, v} ⊆ reachables(roots[t]) && v ∈ GREY && o.f |-> _}
			o.f |-> v

*	**UpdateS2**, on another mutator thread, NO.(fourteen), former (13)

		{phase[t] = Sync2 && {o, v} ⊆ reachables(roots[t]) && {v, o'} ⊆ GREY U BLACK && o.f |-> o'}
			o.f |-> v

*	**UpdateTracing**, on another mutator thread, NO.(fifteen), former (14)

		{phase[t] = Async && stageC ∈ {TRACING, SWEEPING} && {v, o} ⊆ reachables(roots[t]) && {v, o'} ⊆ GREY U BLACK && o.f |-> o'}
			o.f |-> v

*	**MarkGrey**, on collector thread or another mutator thread, NO.(sixteen), former (15)

		{(phase[t] ≠ Async || stageC ≠ RESTING) && o ∈ reachables(roots[t]) && GREY = R}
			GREY = R (+) {o}

*	**MarkBlack**, on collector thread, NO.(seventeen), former (16)

		{stageC = TRACING && (∀t ∈ T · phaseC = phase[t] = Async) && (∀f ∈ fields(o), o' ∈ Obj · o.f |-> o' => o' ∈ GREY U BLACK) && o.color = WHITE && GREY(o) = n ≥ 1}
			o.color = BLACK

*	**RemoveGrey**, on collector thread, NO.(eighteen), former (17)

		{stageC = TRACING && (∀t ∈ T · phaseC = phase[t] = Async) && o.color = BLACK && GREY(o) = n ≥ 1}
			GREY(o) = n - 1


	**TODO** remove following if it doesn't hurt
*	**PhaseS2**, on another mutator thread, NO.(twenty), former (19)

		{phaseC = Async && roots[t] ⊆ GREY && phase[t] = Sync2}
			phase[t] = Async

*	**LoadWhite**, on another mutator thread, NO.(twentysix), no former

		{r0 = o && r1 = o' && f ∈ fields(o) && [o' + f] |-> o'' && {o, o'} ⊆ roots[t] = R && o''.color = WHITE && (phase[t] = Async => o'' ∈ reachables(GREY))}
			r0 = o'' && roots[t] = R (-) {o} (+) {o''}

*	**LoadBlack**, on another mutator thread, NO.(twentyseven), no former

		{r0 = o && r1 = o' && f ∈ fields(o) && [o' + f] |-> o'' && {o, o'} ⊆ roots[t] = R && o''.color = BLACK}
			r0 = o'' && roots[t] = R (-) {o} (+) {o''}

*	**NewWhite**, on another mutator thread, NO.(twentyeight), no former

		{freelist |-> FREELIST && o ∈ FREELIST && o.color = BLUE && (phase[t] ≠ Async || stageC = CLEAR_OR_MARKING)}
			freelist |-> FREELIST / {o} && o.color = WHITE

*	**NewBlack**, on another mutator thread, NO.(twentynine), no former

		{freelist |-> FREELIST && o ∈ FREELIST && o.color = BLUE && (phase[t] = Async && stageC ≠ CLEAR_OR_MARKING)}
			freelist |-> FREELIST / {o} && o.color = BLACK

*	**Bucket_rely_t**, on collector thread, NO.(thirtyone), former (29)

		{lastRead[t] = v && lastWrite[t] = v' && v + n ≤ v'}
			lastRead[t] = v + n

*	**Bucket_rely_t'**, on another mutator thread, NO.(thirtytwo), no former

		{lastRead[t'] = v && lastWrite[t'] = v' && v + n ≤ v'}
			lastRead[t'] = v + n




##### relies for collector thread (duplication are not written again)

All the relies for collector thread happened on one mutator thread t.

*	**Phase_rely_C**, NO.(six), former (6), same as **Phase_rely_t'**.

*	**UpdateResting**, NO.(twelve)
*	**UpdateS1**, NO.(thirteen), former (12)
*	**UpdateS2**, NO.(fourteen), former (13)
*	**UpdateTracing**, NO.(fifteen), former (14)
*	**MarkGrey**, NO.(sixteen), former (15)
*	**PhaseS2**, NO.(twenty), former (19)
*	**LoadWhite**, NO.(twentysix), no former
*	**LoadBlack**, NO.(twentyseven), no former
*	**NewWhite**, NO.(twentyeight), former (26)
*	**NewBlack**, NO.(twentynine), former (27)

*	**Bucket_rely_C**, NO.(thirtythree), same as **Bucket_rely_t'**.

-----
// for copying

*	Phase_rely_C
*	UpdateResting
*	UpdateS1
*	UpdateS2
*	UpdateTracing
*	MarkGrey
*	PhaseS2
*	LoadWhite
*	LoadBlack
*	NewWhite
*	NewBlack
*	Bucket_rely_C

-----

-----

<!-- Above are the resources, the followings are the proofs -->

### All Invariants

Each invariant has to check against all the relies, that is,

*	Phase_rely_t
*	Phase_rely_t', Phase_rely_C
*	UpdateResting
*	UpdateS1
*	UpdateS2
*	UpdateTracing
*	MarkGrey
*	MarkBlack
*	RemoveGrey
*	PhaseS2
*	LoadWhite
*	LoadBlack
*	NewWhite
*	NewBlack
*	Bucket_rely_t
*	Bucket_rely_t', Bucket_rely_C

##### Invariant (1) Phase_inv' (phase[t], phaseC, in_handshake)

	Phase_inv':	not in handshake => ∀t· phase[t] = phaseC

Note: According to Gustavo, in_handshake is not used so far, this invariant can be ignored.


##### Invariant (2) Phase_inv (phase[t], phaseC)

	Phase_inv:	∀t· phase[t] ≤ phaseC ≤ phase[t] (+) 1

*	Phase_rely_t:

		H&P:	∀t· phase[t] = phaseC = X
		C:		phaseC = X + 1
		
		sp = ∃y·{phaseC = X + 1 && ∀t· phase[t] = y = X}

	sp => H? success

*	Phase_rely_t', Phase_rely_C:

		H&P:	∃t· phase[t'] (+) 1 = phaseC = X
		C:		phase[t'] = phaseC = X
		
		sp = ∃y·{phase[t'] = X && y (+) 1 = phaseC = X}

	sp => H? success

*	UpdateResting, UpdateS1, UpdateS2, UpdateTracing: change o.f, independent
*	MarkGrey: change GREY, independent
*	MarkBlack: change o.color, independent
*	RemoveGrey: change GREY, independent

*	PhaseS2:

		H&P:	phaseC = Async && roots[t] ⊆ GREY && phase[t] = Sync2
		C:		phase[t] = Async
		
		sp = ∃y·{phase[t] = Async && phaseC = Async && roots[t] ⊆ GREY && y = Sync2}

	sp => H? success

*	LoadWhite, LoadBlack: change register & roots[t], independent
*	NewWhite, NewBlack: change freelist and o.color, independent
*	Bucket_rely_t: change lastRead[t], independent
*	Bucket_rely_t', Bucket_rely_C: change lastWrite[t], independent


##### Invariant Stage_inv1, Stage_inv2, Stage_inv3 (stageC, phaseC, in_handshake)

	Stage_inv1:	stageC ∈ {SWEEPING, RESTING} => phaseC = Async && not_in_handshake

	Stage_inv2:	stageC = CLEAR_OR_MARKING => phaseC ∈ {Async, Sync1, Sync2}

	Stage_inv3:	stageC = Tracing => phaseC ∈ {Sync2, Async}

These three can only modified in collector thread, therefore there is indeed no need to check via rely-guarantee!!


##### Invariant MAsynch_inv (phase[t], stageC, reachables(), roots[t], BLACK, GREY)

	MAsynch_inv:	phase[t] = Async && stageC ≠ CLEAR_OR_MARKING => reachables(roots[t]) ⊆ BLACK U reachables(GREY)

*	Phase_rely_t: change phaseC, independent

*	Phase_rely_t', Phase_rely_C:

		H&P:	phase[t] = Async && phaseC= Sync1 && ..
		C:		phase[t] = Sync1
		
		sp = ∃y·{phase[t] = Sync1 && y = Async && phaseC = Sync1 && ..}

	sp => H? success

*	UpdateResting:

		H&P:	phase[t] = Async
			&&	stageC = RESTING
			&&	{o, v} ⊆ reachables(roots[t])
			&&	reachables(roots[t]) ⊆ BLACK U reachables(GREY)
		C:		o.f |-> v

		sp = ∃y·{
			o.f |-> v
		&&	phase[t] = Async
		&&	stageC = RESTING
		&&	{o, v} ⊆ reachables(roots[t])
		&&	reachables(roots[t]) ⊆ BLACK U reachables(GREY)
		}

	sp => H? success

*	UpdateS1:

		H&P:	{phase[t] = Sync1 && phase[t] = Async && ..} == false

*	UpdateS2:

		H&P:	{phase[t] = Sync2 && phase[t] = Async && ..} == false

*	UpdateTracing:

		H&P:	phase[t] = Async
			&&	stageC ∈ {Tracing, Sweeping}
			&&	{v, o} ⊆ reachables(roots[t])
			&&	{v, o'} ⊆ GREY U BLACK
			&&	o.f |-> o'
			&&	reachables(roots[t]) ⊆ BLACK U reachables(GREY)
		C:		o.f |-> v

		sp = ∃y·{
			o.f |-> v
		&&	phase[t] = Async
		&&	stageC ∈ {Tracing, Sweeping}
		&&	{v, o} ⊆ reachables(roots[t])
		&&	{v, o'} ⊆ GREY U BLACK
		&&	y |-> o'
		&&	reachables(roots[t]) ⊆ BLACK U reachables(GREY)
		}

	sp => H? success

*	MarkGrey: only add object into GREY, those already in GREY are not affected
*	MarkBlack: only set o.color to BLACK, those already in BLACK are not affected

*	RemoveGrey:

		H&P:	stageC = Tracing
			&&	∀t· phase[t] = phaseC = Async
			&&	o.color = BLACK
			&&	GREY(o) = n ≥ 1
			&&	o ∈ reachables(roots[t])
			&&	reachables(roots[t]) ⊆ BLACK U reachables(GREY)
		C:		GREY(o) = n - 1

		sp = ∃y·{
			GREY(o) = n-1
		&&	stageC = Tracing
		&&	∀t· phase[t] = phaseC = Async
		&&	o.color = BLACK
		&&	y = n ≥ 1
		&&	o ∈ reachables(roots[t])
		&&	reachables(roots[t]) ⊆ BLACK U reachables(GREY)}

	sp => H? success

*	PhaseS2

		H&P:	{phase[t] = Sync2 && phase[t] = Async && ..} == false

*	LoadWhite

		H&P:	phase[t] = Async
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	r0 = o
			&&	r1 = o'
			&&	f ∈ fields(o)
			&&	[o' + f] |-> o''
			&&	{o, o'} ⊆ roots[t] = R
			&&	o''.color = WHITE
			&&	o'' ∈ reachables(GREY)
			&&	reachables(roots[t]) ⊆ BLACK U reachables(GREY))

		C:		roots[t] = R (-) {o} (+) {o''}	// assignment to r0 is omitted here

		sp = ∃y·{
			roots[t] = R (-) {o} (+) {o''}
		&&	phase[t] = Async
		&&	stageC ≠ CLEAR_OR_MARKING
		&&	r0 = o
		&&	r1 = o'
		&&	f ∈ fields(o)
		&&	[o' + f] |-> o''
		&&	{o, o'} ⊆ y = R
		&&	o''.color = WHITE
		&&	o'' ∈ reachables(GREY)
		&&	reachables(y) ⊆ BLACK U reachables(GREY))
		}

	sp => H? success
	
*	LoadBlack

		H&P:	phase[t] = Async
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	r0 = o
			&&	r1 = o'
			&&	f ∈ fields(o)
			&&	[o' + f] |-> o''
			&&	{o, o'} ⊆ roots[t] = R
			&&	o''.color = BLACK
			&&	reachables(roots[t]) ⊆ BLACK U reachables(GREY))

		C:		roots[t] = R (-) {o} (+) {o''}	// assignment to r0 is omitted here

		sp = ∃y·{
			roots[t] = R (-) {o} (+) {o''}
		&&	phase[t] = Async
		&&	stageC ≠ CLEAR_OR_MARKING
		&&	r0 = o
		&&	r1 = o'
		&&	f ∈ fields(o)
		&&	[o' + f] |-> o''
		&&	{o, o'} ⊆ y = R
		&&	o''.color = BLACK
		&&	reachables(y) ⊆ BLACK U reachables(GREY))
		}

	sp => H? success

*	NewWhite, NewBlack: change freelist & o.color, independent
*	Bucket_rely_t: change lastRead[t], independent
*	Bucket_rely_t', Bucket_rely_C: change lastWrite[t], independent


##### Invariant MAsynchObj_inv (reachables(), roots[t], o.color, GREY, phase[t], stageC, BLACK)

	MAsynchOjb_inv:
		∀ o ∈ Obj, t ∈ 	T ·
			o ∈ reachables(roots[t])
		&&	o.color = WHITE
		&&	o ∉ GREY
			=>
			phase[t] ≠ Async 
		||	stageC = CLEAR_OR_MARKING
		||	(∃o' ∈ GREY/BLACK· o ∈ reachables(o'))

Note that the invariant is only meaningful when "stageC ≠ CLEAR_OR_MARKING" && "phase[t] = Async"!

*	Phase_rely_t: change phaseC, independent

*	Phase_rely_t', Phase_rely_C:

	Only changing "phase[t] ≠ Async" from "true" to "not true" is meaningful. Otherwise it won't change anything.	So:

		H&P:	phase[t] (+) 1 = phaseC = Async
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	∀ o ∈ Obj · o ∈ reachables(roots[t]) && o.color = WHITE && o ∉ GREY
				=>	phase[t] ≠ Async || (∃o' ∈ GREY/BLACK · o ∈ reachables(o'))

		C:		phase[t] = Async

		sp = ∃y·{
				phase[t] = Async
			&&	y (+) 1 = phaseC = Async
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	∀ o ∈ Obj · o ∈ reachables(roots[t]) && o.color = WHITE && o ∉ GREY
				=>	y ≠ Async || (∃o' ∈ GREY/BLACK · o ∈ reachables(o'))			}

	sp => H? success

*	UpdateResting, UpdateS1, UpdateS2, UpdateTracing: change o.f, independent
*	MarkGrey: only add object into GREY, since there is a constraint "o ∉ GREY", independent

*	MarkBlack: independent for o.color, but not for o'.color

		H&P:	stageC = TRACING
			&&	∀ t · phase[t] = phaseC = Async
			&&	∀ f ∈ fields(o'), o'' ∈ Obj · o'.f |-> o'' => o'' ∈ GREY U BLACK
			&&	o'.color = WHITE
			&&	GREY(o') = n ≥ 1
			&&	∀ o ∈ Obj, t ∈ T ·
					o ∈ reachables(roots[t])
				&&	o.color = WHITE
				&&	o ∉ GREY
					=>
					∃o' ∈ GREY · o'.color ≠ BLACK && o ∈ reachables(o')

		C:	o'.color = BLACK
		
		sp = ∃y·{
				... // just replace o'.color
		}

	sp => H? success. Using the invariant itself, there must be a GREY object between a BLACK and a WHITE one.
	
	Note: Here the invariant itself can be used in the proof, because this is not to prove the invariant is true, but to prove that invariant won't be invalidated by some rely. (with the assumption that it's already true)

*	RemoveGrey: only o' may be removed

		H&P:	{o' ∈ GREY && o'.color ≠ BLACK && o'.color = BLACK} == false

*	PhaseS2: same as proof of Phase_rely_t', Phase_rely_C

*	LoadWhite:

		// r0 = load(r1, f)
		H&P:	r0 = o
			&&	r1 = o1
			&&	f ∈ fields(o)
			&&	[o1 + f] |-> o2
			&&	{o, o1} ⊆ roots[t] = R
			&&	phase[t] = Async
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	o2.color = WHITE
			&&	o2 ∈ reachables(GREY)
			&&	∀ o ∈ Obj, t ∈ T ·
					o ∈ reachables(roots[t])
				&&	o.color = WHITE
				&&	o ∉ GREY
					=>
					∃ o' ∈ GREY · o'.color ≠ BLACK && o ∈ reachables(o')

		C:		roots[t] = R (-) {o} (+) {o2}	// ignore r0 = o''
		
		sp = ∃y·{
			roots[t] = R (-) {o} (+) {o2}
		&&	r0 = o
		&&	r1 = o1
		&&	f ∈ fields(o)
		&&	[o1 + f] |-> o2
		&&	{o, o1} ⊆ y = R
		&&	phase[t] = Async
		&&	stageC ≠ CLEAR_OR_MARKING
		&&	o2.color = WHITE
		&&	o2 ∈ reachables(GREY)
		&&	∀ o ∈ Obj, t ∈ T ·
				o ∈ reachables(y)
			&&	o.color = WHITE
			&&	o ∉ GREY
				=>
				∃ o' ∈ GREY · o'.color ≠ BLACK && o ∈ reachables(o')
		}

	sp => H? success.

*	LoadBlack: The loaded object is BLACK while the invariant requires the object to be WHITE, thus independent

*	NewWhite, NewBlack:

		H&P:	{o.color = BLUE && ..} == false

*	Bucket_rely_t: change lastRead[t], independent
*	Bucket_rely_t', Bucket_rely_C: change lastWrite[t], independent


##### Invariant MAsynch_inv' (phase[t], stageC, reachables, roots[t], BLACK, GREY)

	MAsynch_inv':
		∀t ∈ T ·
			phase[t] = Async && stageC ≠ CLEAR_OR_MARKING
		=>
		reachables(U roots[t]) ⊆ BLACK U reachables(GREY)

*	Phase_rely_t: change phaseC, independent

*	Phase_rely_t', Phase_rely_C: only "change to Async" is meaningful

		H&P:	phase[t'] (+) 1 = phaseC = Async
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	reachables(U roots[t]) ⊆ BLACK U reachables(GREY) // ∀ t · t ≠ t'
		
		C:		phase[t'] = Async
		
		sp = ∃y · {
			phase[t'] = Async
		&&	y (+) 1 = phaseC = Async
		&&	stageC ≠ CLEAR_OR_MARKING
		&&	reachables(U roots[t]) ⊆ BLACK U reachables(GREY)
		}

	sp => H? success. According to invariant MAsynch_inv.

*	UpdateResting, UpdateS1, UpdateS2, UpdateTracing: change o.f, independent
*	MarkGrey: only add object into GREY, independent
*	MarkBlack only add object to BLACK, independent

*	RemoveGrey:

		H&P:	stageC = TRACING
			&&	∀t · phaseC = phase[t] = Async
			&&	o.color = BLACK
			&&	GREY(o) = n ≥ 1
			&&	reachables(U roots[t]) ⊆ BLACK U reachables(GREY)
		
		C:		GREY(o) = n - 1
		
		sp = ∃y · {
				GREY(o) = n - 1
			&&	stageC = TRACING
			&&	∀t · phaseC = phase[t] = Async
			&&	o.color = BLACK
			&&	y = n ≥ 1
			&&	reachables(U roots[t]) ⊆ BLACK U reachables(GREY)
		}

	sp => H? success

*	PhaseS2: same as Phase_rely_t', Phase_rely_C

*	LoadWhite

		// r0 = load(r1, f)
		H&P:	r0 = o
			&&	r1 = o'
			&&	f ∈ fields(o)
			&&	[o' + f] |-> o''
			&&	{o, o'} ⊆ roots[t] = R
			&&	∀t· phase[t] = Async
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	o''.color = WHITE
			&&	o'' ∈ reachables(GREY)
			&&	reachables(U roots[t]) ⊆ BLACK U reachables(GREY)

		C:		roots[t] = R (-) {o} (+) {o''}	// ignore r0 = o''
		
		sp = ∃y · {
				roots[t] = R (-) {o} (+) {o''}
			&&	r0 = o
			&&	r1 = o'
			&&	f ∈ fields(o)
			&&	[o' + f] |-> o''
			&&	{o, o'} ⊆ roots[t] = R
			&&	∀t· phase[t] = Async
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	o''.color = WHITE
			&&	o'' ∈ reachables(GREY)
			&&	reachables(U roots[t'] U y) ⊆ BLACK U reachables(GREY) // t' ≠ t
		}

	sp => H? success

*	LoadBlack

		// r0 = load(r1, f)
		H&P:	r0 = o
			&&	r1 = o'
			&&	f ∈ fields(o)
			&&	[o' + f] |-> o''
			&&	{o, o'} ⊆ roots[t] = R
			&&	∀t· phase[t] = Async
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	o''.color = BLACK
			&&	reachables(U roots[t]) ⊆ BLACK U reachables(GREY)

		C:		roots[t] = R (-) {o} (+) {o''}	// ignore r0 = o''
		
		sp = ∃y · {
				roots[t] = R (-) {o} (+) {o''}
			&&	r0 = o
			&&	r1 = o'
			&&	f ∈ fields(o)
			&&	[o' + f] |-> o''
			&&	{o, o'} ⊆ roots[t] = R
			&&	∀t· phase[t] = Async
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	o''.color = BLACK
			&&	reachables(U roots[t'] U y) ⊆ BLACK U reachables(GREY) // t' ≠ t
		}

	sp => H? success

*	NewWhite, NewBlack:

		H&P:	{o.color = BLUE && ..} == false

*	Bucket_rely_t: change lastRead, independent
*	Bucket_rely_t', Bucket_rely_C: change lastWrite, independent


##### Invariant MRoot_inv (phaseC, stageC, roots[t], reachables() GREY, BLACK, rootToMark)

	MRoot_inv:
		∀t ∈ T ·
			phaseC = Async && stageC ≠ CLEAR_OR_MARKING
			=>
			roots[t] ⊆ reachables(GREY U rootToMark) U BLACK

*	Phase_rely_t:

		H&P:	∀t· phase[t] = phaseC = Async && ..
		C:		phaseC = Sync1
		
		sp = ∃y·{phaseC = Sync1 && ∀t· phase[t] = Async && ..}

	sp => H? success

*	Phase_rely_t', Phase_rely_C: change phase[t], independent
*	UpdateResting, UpdateS1, UpdateS2, UpdateTracing: change o.f, independent
*	MarkGrey: only add object into GREY, those already in GREY are not affected
*	MarkBlack: only set o.color to BLACK, those already in BLACK are not affected

*	RemoveGrey

		H&P:	phaseC = Async
			&&	stageC = Tracing
			&&	o ∈ roots[t]
			&&	o.color = BLACK
			&&	GREY(o) = n ≥ 1
			&&	roots[t] ⊆ reachables(GREY U rootToMark) U BLACK
		C:		GREY(o) = n - 1
		
		sp = ∃y·{
			GREY(o) = n-1
		&&	phaseC = Async
		&&	stageC = Tracing
		&&	o ∈ roots[t]
		&&	o.color = BLACK
		&&	y = n ≥ 1
		&&	roots[t] ⊆ reachables(GREY U rootToMark) U BLACK}

	sp => H? success

*	PhaseS2 change phase[t], independent


*	LoadWhite

		H&P:	r0 = o
			&&	r1 = o'
			&&	f ∈ fields(o)
			&&	[o' + f] |-> o''
			&&	{o, o'} ⊆ roots[t] = R
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	o''.color = WHITE
			&&	phase[t] = Async
			&&	o'' ∈ reachables(GREY)
			&&	roots[t] ⊆ reachables(GREY U rootToMark) U BLACK

		C:		roots[t] = R (-) {o} (+) {o''}	// assignment of r0 is omitted

		sp = ∃y · {
				roots[t] = R (-) {o} (+) {o''}
			&&	r0 = o
			&&	r1 = o'
			&&	f ∈ fields(o)
			&&	[o' + f] |-> o''
			&&	{o, o'} ⊆ y = R
			&&	∀t · phase[t] = Async
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	o''.color = WHITE
			&&	o'' ∈ reachables(GREY)
			&&	y ⊆ reachables(GREY U rootToMark) U BLACK
		}

	sp => H? success

*	LoadBlack

		H&P:	r0 = o
			&&	r1 = o'
			&&	f ∈ fields(o)
			&&	[o' + f] |-> o''
			&&	{o, o'} ⊆ roots[t] = R
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	o''.color = BLACK
			&&	phase[t] = Async
			&&	roots[t] ⊆ reachables(GREY U rootToMark) U BLACK

		C:		roots[t] = R (-) {o} (+) {o''}	// assignment of r0 is omitted

		sp = ∃y · {
				roots[t] = R (-) {o} (+) {o''}
			&&	r0 = o
			&&	r1 = o'
			&&	f ∈ fields(o)
			&&	[o' + f] |-> o''
			&&	{o, o'} ⊆ y = R
			&&	∀t · phase[t] = Async
			&&	stageC ≠ CLEAR_OR_MARKING
			&&	o''.color = BLACK
			&&	y ⊆ reachables(GREY U rootToMark) U BLACK
		}

	sp => H? success

*	NewWhite, NewBlack:

		H&P:	{o ∈ roots[t] && o.color = BLUE} == false

	Some invariant is implicit that BLUE objects can only be used in allocation.


*	Bucket_rely_t: change lastRead[t], independent
*	Bucket_rely_t', Bucket_rely_C: change lastWrite[t], independent


##### Invariant Resting_inv (stageC, o.color)

	Resting_inv:	stageC = RESTING => (∀ o ∈ Obj· o.color ∈ {BLUE, BLACK})

*	Phase_rely_t: change phaseC, independent
*	Phase_rely_t': change phase[t], independent
*	UpdateResting, UpdateS1, UpdateS2, UpdateTracing: change o.f, independent
*	MarkGrey: change GREY, independent
*	MarkBlack: set o.color to BLACK, those already in BLACK are not affected
*	RemoveGrey change GREY, independent
*	PhaseS2 change phase[t], independent
*	LoadWhite, LoadBlack: change register & roots[t], independent

*	NewWhite, NewBlack:

		H&P:	{o.color ∈ {BLUE, BLACK} && o.color = BLUE && ..} == false

*	Bucket_rely_t: change lastRead[t], independent
*	Bucket_rely_C: change lastWrite[t], independent


##### Invariant Resting_inv' (stageC, reachables(), roots[t], o.color)

	Resting_inv':
		stageC = RESTING => (∀ o ∈ Obj · (o ∈ U_t∈T reachables(roots[t]) => o.color = BLACK))

*	Phase_rely_t: change phaseC, independent
*	Phase_rely_t', Phase_rely_C: change phase[t], independent

*	UpdateResting, UpdateS1, UpdateS2, UpdateTracing:

		H&P:	stageC = RESTING
			&&	{o, v} ⊆ reachables(roots[t])
			&&	(∀ o ∈ Obj· (o ∈ U_t∈T reachables(roots[t]) => o.color = BLACK))
		C:		o.f |-> v

		sp = ∃y·{
			o.f |-> v
		&&	stageC = RESTING
		&&	{o, v} ⊆ reachables(roots[t])
		&&	v.color = BLACK
		&&	..
		}

	sp => H? success

*	MarkGrey: change GREY, independent
*	MarkBlack only set color to BLACK, those already in BLACK are not affected
*	RemoveGrey: change GREY, independent
*	PhaseS2: change phase[t], independent

*	LoadWhite:

		H&P:	r0 = o
			&&	r1 = o'
			&&	f ∈ fields(o)
			&&	[o' + f] |-> o''
			&&	{o, o'} ⊆ roots[t] = R
			&&	o''.color = WHITE
			&&	(phase[t] = Async => o'' ∈ reachables(GREY))
			&&	stageC = RESTING
			&&	∀ob ∈ Obj· (ob ∈ U_t∈T reachables(roots[t]) => ob.color = BLACK)

		H&P == false // o''.color = WHITE & BLACK

*	LoadBlack:

		H&P:	r0 = o
			&&	r1 = o'
			&&	f ∈ fields(o)
			&&	[o' + f] |-> o''
			&&	{o, o'} ⊆ roots[t] = R
			&&	o''.color = BLACK
			&&	stageC = RESTING
			&&	∀ob ∈ Obj· (ob ∈ U_t∈T reachables(roots[t]) => ob.color = BLACK)

		C:		roots[t] = R (-) {o} (+) {o''}	// assignment of r0 is omitted
		
		sp = ∃y·{
			roots[t] = R (-) {o} (+) {o''}
		&&	r0 = o
		&&	r1 = o'
		&&	f ∈ fields(o)
		&&	[o' + f] |-> o''
		&&	{o, o'} ⊆ y = R
		&&	o''.color = BLACK
		&&	stageC = RESTING
		&&	∀ob ∈ Obj· (ob ∈ U_t∈T reachables(y) => ob.color = BLACK)}

	sp => H? success (key: o'' previously ∈ reachables(roots[t])? yes)

*	NewWhite:

		H&P:	{stageC = CLEAR_OR_MARKING && stageC = RESTING && ..} == false

*	NewBlack:

		H&P:	phase[t] = Async
			&&	stageC = RESTING
			&&	freelist |-> FREELIST
			&&	o ∈ FREELIST
			&&	o.color = BLUE
			&&	∀ o ∈ Obj · (o ∈ U_t∈T reachables(roots[t]) => o.color = BLACK)
		C:		o.color = BLACK	// change of freelist is omitted

		sp = ∃y·{
			o.color = BLACK
		&&	phase[t] = Async
		&&	stageC = RESTING
		&&	freelist |-> FREELIST
		&&	o ∈ FREELIST
		&&	y = BLUE
		&&	∀ o ∈ Obj · (ob ∈ U_t∈T reachables(roots[t]) => ob.color = BLACK)
		}

	sp => H? success

*	Bucket_rely_t: change lastRead[t], independent
*	Bucket_rely_t', Bucket_rely_C: change lastWrite[t], independent


##### Invariant Bucket_inv (lastRead[t], lastWrite[t])

	H:	lastRead[t] ≤ lastWrite[t]

*	Phase_rely_t: change phaseC, independent
*	Phase_rely_t': change phase[t], independent
*	UpdateResting, UpdateS1, UpdateS2, UpdateTracing: change o.f, independent
*	MarkGrey: change GREY, independent
*	MarkBlack change o.color, independent
*	RemoveGrey: change GREY, independent
*	PhaseS2: change phase[t], independent
*	LoadWhite, LoadBlack: change register & roots[t], independent
*	NewWhite, NewBlack: change freelist & o.color, independent

*	Bucket_rely_t:

		H&P:	lastRead[t] = v
			&&	lastWrite[t] = v'
			&&	v + n ≤ v'
		C:		lastRead[t] = v + n
		
		sp = ∃y·{
			lastRead[t] = v + n
		&&	y = v
		&&	lastWrite[t] = v'
		&&	v + n ≤ v'
		}

	sp => H? success


*	Bucket_rely_t', Bucket_rely_C:

		H&P:	lastWrite[t] = v
			&&	v + n ≤ BUCKET_SIZE
			&&	lastRead[t] ≤ lastWrite[t]
		C:		lastWrite[t] = v + n
		
		sp = ∃y·{
			lastWrite[t] = v + n
		&&	y = v
		&&	v + n ≤ BUCKET_SIZE
		&&	lastRead[t] ≤ y
		}

	sp => H? success


-----

### *t*: cooperate()

"###" is followed by a function name, the following is to prove the assertions in this function. t means mutator thread, C means collector thread.

While invariants check against all relies, functions on mutator thread only check agains the relies of mutator thread. Similar for collector thread.

"after 1" is to locate the assertion. 1 is the line number written in .tex file.

In parenthesis are the variables used in the assertion. (therefore only need to check the rely/guarantees that change those variables)


##### after 1 (tmp, phaseC, phase[t])

	H:	Phase_inv[t] && {(tmp ≤ phaseC ≤ tmp (+) 1) && phase[t] ≤ tmp}
	// Phase_inv[t] is invariant and has been proved above.

*	Phase_rely_t:

		H&P:	phaseC = phase[t] = tmp = X
		C:		phaseC = X + 1
		
		sp = {phaseC = phase[t] + 1 = tmp + 1}
	
	sp => H? success

*	Phase_rely_t': change phase[t'] (another thread), independent
*	UpdateResting, UpdateS1, UpdateS2, UpdateTracing: change o.f, independent
*	MarkGrey: change GREY, independent
*	MarkBlack: change o.color, independent
*	RemoveGrey: change GREY, independent
*	PhaseS2: change phase[t'] (another thread), independent
*	LoadWhite, LoadBlack: change register & roots[t], independent
*	NewWhite, NewBlack: change freelist & o.color, independent
*	Bucket_rely_t: change lastRead[t], independent
*	Bucket_rely_t': change lastWrite[t] of another thread, independent


##### after 3 (phase[t], phaseC, tmp)

	H:	Phase_inv[t] && {phase[t] (+) 1 = phaseC && tmp = phaseC}

*	Phase_rely_t:
	
		H&P:	{phase[t] (+) 1 = phaseC && phase[t] = phaseC} == false

*	Phase_rely_t': change phase[t'] (another thread), independent
*	UpdateResting, UpdateS1, UpdateS2, UpdateTracing: change o.f, independent
*	MarkGrey: change GREY, independent
*	MarkBlack: change o.color, independent
*	RemoveGrey: change GREY, independent
*	PhaseS2: change phase[t'] (another thread), independent
*	LoadWhite, LoadBlack: change register & roots[t], independent
*	NewWhite, NewBlack: change freelist & o.color, independent
*	Bucket_rely_t: change lastRead[t], independent
*	Bucket_rely_t': change lastWrite[t] of another thread, independent


all other assertions in cooperate() is Phase_inv[t], thus considered to be true all the time


-----

### *C*: handshake()

##### PRE (∀t·phase[t], phaseC)

	H:	Phase_inv && {∀t · phase[t] = phaseC = X}

*	Phase_rely_C:

		H&P:	{(∃t· phase[t] (+) 1 = phaseC) && (∀t·phase[t] = phaseC} == false

*	UpdateResting, UpdateS1, UpdateS2, UpdateTracing: change o.f, independent
*	MarkGrey: change GREY, independent
*	PhaseS2:

		H&P:	{(∃t·phaseC = Async && phase[t] = Sync2) && (∀t·phase[t] = phaseC)} == false

*	LoadWhite, LoadBlack: change register & roots, independent
*	NewWhite, NewBlack: change FREELIST, independent
*	Bucket_rely_C: change lastWrite[t], independent

	
##### after 1 (∀t·phase[t], phaseC, tmp)

	H:	Phase_inv && {(∀t · phase[t] = phaseC) && tmp = phaseC = X}

"after 1" is the same as "PRE" except that it adds the relation between tmp and phaseC. Since tmp is a local variable, everything is the same as the proof for "PRE".


##### after 2 (phaseC)

	H:	Phase_inv && {phaseC = X (+) 1}

*	Phase_rely_C: change phase[t], independent
*	UpdateResting, UpdateS1, UpdateS2, UpdateTracing: change o.f, independent
*	MarkGrey: change GREY, independent
*	PhaseS2: change phase[t], independent
*	LoadWhite, LoadBlack: change register & roots, independent
*	NewWhite, NewBLack: change FREELIST, independent
*	Bucket_rely_C: change lastWrite[t], independent


##### after 3 (phaseC)

	H:	Phase_inv && {phaseC = X (+) 1}

exactly the same as "after 2"


##### after 4 while loop (for some t: phase[t], phaseC)

	H:	Phase_inv && {phase[t] = phaseC = X (+) 1}

*	Phase_rely_C:

		H&P:	{phase[t] (+) 1 = phaseC && phase[t] = phaseC} == false

*	UpdateResting, UpdateS1, UpdateS2, UpdateTracing: change o.f, independent
*	MarkGrey: change GREY, independent
*	PhaseS2:

		H&P:	{(phaseC = Async && phase[t] = Sync2) && (phase[t] = phaseC)} == false

*	LoadWhite, LoadBlack: change register & roots, independent
*	NewWhite, NewBlack: change FREELIST, independent
*	Bucket_rely_C: change lastWrite[t], independent


##### after 4 for loop / POST (∀t·phase[t], phaseC)

	H:	Phase_inv && {∀t · phase[t] = phaseC = X (+) 1}

similar to "PRE", except that the value of phase[t] and phase is different. The proof is the same as "PRE".

-----

### *t*: update()

##### PRE (x, f, v, roots[t])

*	Phase_rely_t: change phaseC, independent
*	Phase_rely_t': change phase[t'] of another mutator thread, independent
*	UpdateResting:
	
		H&P:	x.f |-> _
			&&	{x, v} ⊆ roots[t]
			&&	phase[t] = Async
			&&	stageC ∈ {Resting, Clear-or-Marking}
			&&	{x, v'} ⊆ reachables(roots[t])
		C:		x.f |-> v'
			
		sp = {
			x.f |-> v'
		&&	v0 |-> _
		&&	{x, v} ⊆ roots[t]
		&&	phase[t] = Async
		&&	stageC ∈ {Resting, Clear-or-Marking}
		&&	{x, v'} ⊆ reachables(roots[t])
		}
		// v0 is the original value

	sp => H? success
	
*	(12)
	
		H&P:	x.f |-> _
			&&	{x, v} ⊆ roots[t]
			&&	phase[t] = Sync1
			&&	{x, v'} ⊆ reachables(roots[t])
			&&	v' ∈ GREY
		C:		x.f |-> v'
			
		sp = {
			x.f |-> v'
		&&	v0 |-> _
		&&	{x, v} ⊆ roots[t]
		&&	phase[t] = Sync1
		&&	{x, v'} ⊆ reachables(roots[t])
		&&	v' ∈ GREY
		}
		// v0 is the original value
	
	sp => H? success
	
*	(13)(14)
	
	similar to UpdateResting: and (12), C only assign a new value to x.f, it won't affect roots[t]. In H, "x.f |-> _" so any assignment won't invalidate it.
		
*	(15) change GREY, independent
*	(16) change o.color, independent
*	(17) change GREY, independent
*	(19) change phase[t], independent
*	(29) change lastRead[t], independent


##### after 3 (phast[t], stageC, x.f, old, w, GREY, BLACK)

	H:	phase[t] = Sync2 || stageC = TRACING
		=>
		x.f |-> old || (∃w·x.f |-> w && w ∈ GREY U BLACK)

*	Phase_rely_t: change phaseC, independent
*	Phase_rely_t': change phase[t'] of another mutator thread, independent
*	UpdateResting:

		H&P:	{(phase[t] = Sync2 || stageC = TRACING) && (phase[t] = Async && stageC ∈ {Resting, ClearOrMarking})} == false

*	(12)

		// phase[t] = Sync1 => stageC = ClearOrMarking
		H&P:	(phase[t] = Sync2 || stageC = TRACING) && (phase[t] = Sync1)} == false

*	(13)

		H&P:	phase[t] = Sync2
			&&	{x, v'} ⊆ reachables(roots[t])
			&&	{v'} ⊆ GREY U BLACK
			&&	(x.f |-> old && old ∈ GREY U BLACK || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		C:		x.f |-> v'

		sp = ∃y·{
			x.f |-> v'
		&&	phase[t] = Sync2
		&&	{x, v'} ⊆ reachables(roots[t])
		&&	{v'} ⊆ GREY U BLACK
		&&	(y |-> old && old ∈ GREY U BLACK || ∃w· y |-> w && w ∈ GREY U BLACK)
		}

	sp => H? success

*	(14)

		H&P:	stageC = Tracing
			&&	{v', x} ⊆ reachables(roots[t])
			&&	{v'} ⊆ GREY U BLACK
			&&	(x.f |-> old && old ∈ GREY U BLACK || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		C:		x.f |-> v'

		sp = ∃y·{
			x.f |-> v'
		&&	stageC = Tracing
		&&	{v', x} ⊆ reachables(roots[t])
		&&	{v', old} ⊆ GREY U BLACK
		&&	(y |-> old && old ∈ GREY U BLACK || ∃w· y |-> w && w ∈ GREY U BLACK)
		}

	sp => H? success

*	(15) only increase set GREY, those already in GREY are not affected
*	(16) only set an obj to BLACK, those already in GREY U BLACK are not affected
*	(17)

		// the "x.f |-> old" branch is independent with respect to GREY(o), thus only consider the other branch

		H&P:	stageC = Tracing
			&&	∀t·phaseC = phase[t] = Async
			&&	w.color = BLACK
			&&	GREY(w) = n ≥ 1
			&& (x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		C:		GREY(w) = n-1
		
		sp = ∃y·{
			GREY(w) = n-1
		&&	stageC = Tracing
		&&	∀t·phaseC = phase[t] = Async
		&&	w.color = BLACK
		&&	y = n ≥ 1
		&&	(x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		}

	sp => H? success

*	(19)

		H&P:	phase[t] = Sync2
			&&	phaseC = Async
			&&	roots[t] ⊆ GREY
			&&	(x.f |-> old || (∃w·x.f |-> w && w ∈ GREY U BLACK))
		C:		phase[t] = Async
		
		sp = ∃y·{
			phase[t] = Async
		&&	y = Sync2
		&&	phaseC = Async
		&&	roots[t] ⊆ GREY
		&&	(x.f |-> old || (∃w·x.f |-> w && w ∈ GREY U BLACK))
		}

	sp => H? success

*	(29) change lastRead[t], independent


##### after 4 (phase[t], stageC, x.f, GREY, BLACK)

	H:	phase[t] = Sync2 || stageC = Tracing
			=> (x.f |-> old || (∃w· x.f |-> w && w ∈ GREY U BLACK)) && old ∈ GREY U BLACK
		&&
		phase[t] = Sync1
			=> old ∈ GREY U BLACK

*	Phase_rely_t: change phaseC, independent
*	Phase_rely_t': change phase[t] of another mutator thread, independent
*	UpdateResting:

		H&P:	(phase[t] = Sync2 || stageC = Tracing || phase[t] = Sync1) && (phase[t] = Async && stageC ∈ {RESTING, CLEAR_OR_MARKING}) == FALSE
		
*	(12)

		H&P:	phase[t] = Sync1
			&&	{x, v'} ⊆ reachables(roots[t])
			&&	v' ∈ GREY
			&&	x.f |-> _
			&&	old ∈ GREY U BLACK
		C:		x.f |-> v'
		
		sp = ∃y·{
			x.f |-> v'
		&&	phase[t] = Sync1
		&&	{x, v'} ⊆ reachables(roots[t])
		&&	v' ∈ GREY
		&&	y |-> _
		&&	old ∈ GREY U BLACK
		}

	sp => H? success
		
*	(13)

		// the same as (13) in "after 3"

		H&P:	phase[t] = Sync2
			&&	{x, v'} ⊆ reachables(roots[t])
			&&	{v', old} ⊆ GREY U BLACK
			&&	(x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		C:		x.f |-> v'

		sp = ∃y·{
			x.f |-> v'
		&&	phase[t] = Sync2
		&&	{x, v'} ⊆ reachables(roots[t])
		&&	{v', old} ⊆ GREY U BLACK
		&&	(y |-> old || ∃w· y |-> w && w ∈ GREY U BLACK)
		}

	sp => H? success

*	(14)

		// the same as (14) in "after 3"
		
		H&P:	stageC = Tracing
			&&	{v', x} ⊆ reachables(roots[t])
			&&	{v', old} ⊆ GREY U BLACK
			&&	(x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		C:		x.f |-> v'

		sp = ∃y·{
			x.f |-> v'
		&&	stageC = Tracing
		&&	{v', x} ⊆ reachables(roots[t])
		&&	{v', old} ⊆ GREY U BLACK
		&&	(y |-> old || ∃w· y |-> w && w ∈ GREY U BLACK)
		}

	sp => H? success
		
*	(15) only add object into GREY, those already in GREY are not affected
*	(16) only set obj to BLACK, those already in BLACK are not affected
*	(17)

		// both "old" and "w" can be the object o in (17), thus consider them twice

		H&P_1:	stageC = Tracing
			&&	∀t·phase[t] = phaseC = Async
			&&	old.color = BLACK
			&&	GREY(old) = n ≥ 1
			&&	old ∈ GREY U BLACK
			&&	(x.f |-> old || (∃w· x.f |->w && w ∈ GREY U BLACK))
		C:		GREY(old) = n - 1
		
		sp_1 = ∃y·{
			GREY(old) = n - 1
		&&	stageC = Tracing
		&&	∀t·phase[t] = phaseC = Async
		&&	old.color = BLACK
		&&	y = n ≥ 1
		&&	old ∈ GREY U BLACK
		&&	(...)
		}

	sp_1 => H? success


		H&P_2:	stageC = Tracing
			&&	∀t·phase[t] = phaseC = Async
			&&	w.color = BLACK
			&&	GREY(w) = n ≥ 1
			&&	old ∈ GREY U BLACK
			&&	(∃w· x.f |->w && w ∈ GREY U BLACK)
		C:		GREY(w) = n - 1
		
		sp_2 = ∃y·{
			GREY(w) = n-1
		&&	stageC = Tracing
		&&	∀t·phase[t] = phaseC = Async
		&&	w.color = BLACK
		&&	y = n ≥ 1
		&&	old ∈ GREY U BLACK
		&&	(...)
		}

	sp_2 => H? success

*	(19)

		H&P:	phase[t] = Sync2
			&&	phaseC = Async
			&&	roots[t] ⊆ GREY
			&&	old ∈ GREY U BLACK
			&&	(x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		C:		phase[t] = Async
		
		sp = ∃y·{
			phase[t] = Async
		&&	y = Sync2
		&&	phaseC = Async
		&&	roots[t] ⊆ GREY
		&&	old ∈ GREY U BLACK
		&& (x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)
		}

	sp => H? success

*	(29) change lastRead[t], independent


##### after 5 (phase[t], stageC, x.f, GREY, BLACK)

	H:	phase[t] = Sync2 || stageC = Tracing
			=> (x.f |-> old || (∃w· x.f |-> w && w ∈ GREY U BLACK)) && {old, v} ⊆ GREY U BLACK
		&&
		phase[t] = Sync1
			=> {old, v} ⊆ GREY U BLACK

*	Phase_rely_t: change phaseC, independent
*	Phase_rely_t': change phase[t'] of another mutator thread, independent
*	UpdateResting:

		H&P:	phase[t] = Async
			&&	stageC ∈ {RESTING, CLEAR_OR_MARKING}
			&&	(phase[t] = Sync2 || stageC = Tracing || phase[t] = Sync1) == false
		
*	(12)

		H&P:	phase[t] = Sync1
			&&	{old, v} ⊆ GREY U BLACK
			&&	{x, v'} ⊆ reachables(roots[t])
			&&	v' ∈ GREY
			&&	x.f |-> _
		C:		x.f |-> v'
		
		sp = ∃y·{
			x.f |-> v'
		&&	phase[t] = Sync1
		&&	{old, v} ⊆ GREY U BLACK
		&&	{x, v'} ⊆ reachables(roots[t])
		&&	v' ∈ GREY
		&&	y |-> _
		}
		
	sp => H? success

*	(13)

		H&P:	phase[t] = Sync2
			&&	{x, v'} ⊆ reachables(roots[t])
			&&	{v', old} ⊆ GREY U BLACK
			&&	(x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)
			&&	{old, v} ⊆ GREY U BLACK
		C:		x.f |-> v'
		
		sp = ∃y·{
			x.f |-> v'
		&&	phase[t] = Sync2
		&&	{x, v'} ⊆ reachables(roots[t])
		&&	{v', old} ⊆ GREY U BLACK
		&&	(y |-> old || ∃w· y |-> w && w ∈ GREY U BLACK)
		&&	{old, v} ⊆ GREY U BLACK
		}
		
	sp => H? success

*	(14)

		H&P:	stageC = Tracing
			&&	{v', x} ⊆ reachables(roots[t])
			&&	{v', old} ⊆ GREY U BLACK
			&&	(x.f |-> old || ∃w· x.f |-> w && w ∈ GREY U BLACK)
			&&	{old, v} ⊆ GREY U BLACK
		C:		x.f |-> v'
		
		sp = ∃y·{
			x.f |-> v'
		&&	stageC = Tracing
		&&	{v', x} ⊆ reachables(roots[t])
		&&	{v', old} ⊆ GREY U BLACK
		&&	(y |-> old || ∃w· y |-> w && w ∈ GREY U BLACK)
		&&	{old, v} ⊆ GREY U BLACK
		}
		
	sp => H? success

*	(15) only add object into GREY, those already in GREY are not affected
*	(16) only set object to BLACK, those already in BLACK are not affected
*	(17)

		// GREY(o) ==> GREY(w)
		H&P_1:	stageC = Tracing
			&&	∀t·phaseC = phase[t] = Async
			&&	w.color = BLACK
			&&	GREY(w) = n ≥ 1
			&&	(∃w· x.f |-> w && w ∈ GREY U BLACK)
			&&	{old, v} ⊆ GREY U BLACK
		C_1:	GREY(w) = n - 1
		
		sp_1 = ∃y·{
			GREY(w) = n-1
		&&	stageC = Tracing
		&&	∀t·phaseC = phase[t] = Async
		&&	w.color = BLACK
		&&	y = n ≥ 1
		&&	(...)
		&&	{old, v} ⊆ GREY U BLACK
		}

	sp_1 => H? success


		// GREY(o) ==> GREY(old)
		H&P_2:	stageC = Tracing
			&&	∀t·phaseC = phase[t] = Async
			&&	old.color = BLACK
			&&	GREY(old) = n ≥ 1
			&&	(.. || ..)
			&&	{old, v} ⊆ GREY U BLACK
		C_2:	GREY(old) = n - 1
		
		sp_2 = ∃y·{
			GREY(old) = n-1
		&&	stageC = Tracing
		&&	∀t·phaseC = phase[t] = Async
		&&	old.color = BLACK
		&&	y = n ≥ 1
		&&	(.. || ..)
		&&	{old, v} ⊆ GREY U BLACK
		}
		
	sp_2 => H? success
		
		// GREY(o) ==> GREY(v)
		H&P_3:	stageC = Tracing
			&&	∀t·phaseC = phase[t] = Async
			&&	v.color = BLACK
			&&	GREY(v) = n ≥ 1
			&&	(.. || ..)
			&&	{old, v} ⊆ GREY U BLACK
		C_3:	GREY(v) = n - 1
		
		sp_3 = ∃y·{
			GREY(v) = n-1
		&&	stageC = Tracing
		&&	∀t·phaseC = phase[t] = Async
		&&	v.color = BLACK
		&&	y = n ≥ 1
		&&	(.. || ..)
		&&	{old, v} ⊆ GREY U BLACK
		}
		
	sp_3 => H? success

*	(19)

		H&P:	phaseC = Async
			&&	roots[t] ⊆ GREY
			&&	phase[t] = Sync2
			&&	(.. || ..)
			&&	{old, v} ⊆ GREY U BLACK
		C:		phase[t] = Async
		
		sp = ∃y·{
			phase[t] = Async
		&&	phaseC = Async
		&&	roots[t] ⊆ GREY
		&&	y = Sync2
		&&	(.. || ..)
		&&	{old, v} ⊆ GREY U BLACK
		}
		
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

*	Phase_rely_t: change phaseC, independent
*	Phase_rely_t': change phase[t'] of another mutator thread, independent
*	UpdateResting:

		H&P:	phase[t] = Async
			&&	stageC ∈ {RESTING, CLEAR_OR_MARKING}
			&&	(phase[t] = Sync2 || stageC = Tracing || phase[t] = Sync1) == false

*	(12)

		H&P:	phase[t] = Sync1
			&&	{x, v'} ⊆ reachables(roots[t])
			&&	v' ∈ GREY
			&&	x.f |-> _
			&&	{old, v} ⊆ GREY U BLACK
		C:		x.f |-> v'
		
		sp = ∃y·{
			x.f |-> v'
		&&	phase[t] = Sync1
		&&	{x, v'} ⊆ reachables(roots[t])
		&&	v' ∈ GREY
		&&	y |-> _
		&&	{old, v} ⊆ GREY U BLACK
		}

	sp => H? success

*	(13)

		H&P:	phase[t] = Sync2
			&&	{x, v'} ⊆ reachables(roots[t])
			&&	{v'} ⊆ GREY U BLACK
			&&	(x.f |-> v || ∃w· x.f |-> w && w ∈ GREY U BLACK)
			&&	{old, v} ⊆ GREY U BLACK
		C:		x.f |-> v'
		
		sp = ∃y·{
			x.f |-> v'
		&&	phase[t] = Sync2
		&&	{x, v'} ⊆ reachables(roots[t])
		&&	{v'} ⊆ GREY U BLACK
		&&	(y |-> v || ∃w· y |-> w && w ∈ GREY U BLACK)
		&&	{old, v} ⊆ GREY U BLACK
		}

	sp => H? success

*	(14)

		H&P:	stageC = Tracing
			&&	{v', x} ⊆ reachables(roots[t])
			&&	{v'} ⊆ GREY U BLACK
			&&	(x.f |-> v || ∃w· x.f |-> w && w ∈ GREY U BLACK)
			&&	{old, v} ⊆ GREY U BLACK
		C:		x.f |-> v'
		
		sp = ∃y·{
			x.f |-> v'
		&&	stageC = Tracing
		&&	{v', x} ⊆ reachables(roots[t])
		&&	{v'} ⊆ GREY U BLACK
		&&	(y |-> v || ∃w· y |-> w && w ∈ GREY U BLACK)}
		&&	{old, v} ⊆ GREY U BLACK
		
	sp => H? success

*	(15) only add object into GREY, those already in GREY are not affected
*	(16) only set object to BLACK, those already in BLACK are not affected
*	(17)

		// GREY(o) ==> GREY(w)
		H&P_1:	stageC = Tracing
			&&	∀t·phaseC = phase[t] = Async
			&&	w.color = BLACK
			&&	GREY(w) = n ≥ 1
			&&	(∃w· x.f |-> w && w ∈ GREY U BLACK)
			&&	{old, v} ⊆ GREY U BLACK
		C_1:	GREY(w) = n - 1
		
		sp_1 = ∃y·{
			GREY(w) = n-1
		&&	stageC = Tracing
		&&	∀t·phaseC = phase[t] = Async
		&&	w.color = BLACK
		&&	y = n ≥ 1
		&&	(...)
		&&	{old, v} ⊆ GREY U BLACK
		}

	sp_1 => H? success


		// GREY(o) ==> GREY(old)
		H&P_2:	stageC = Tracing
			&&	∀t·phaseC = phase[t] = Async
			&&	old.color = BLACK
			&&	GREY(old) = n ≥ 1
			&&	(.. || ..)
			&&	{old, v} ⊆ GREY U BLACK
		C_2:	GREY(old) = n - 1
		
		sp_2 = ∃y·{
			GREY(old) = n-1
		&&	stageC = Tracing
		&&	∀t·phaseC = phase[t] = Async
		&&	old.color = BLACK
		&&	y = n ≥ 1
		&&	(.. || ..)
		&&	{old, v} ⊆ GREY U BLACK
		}

	sp_2 => H? success
		
		// GREY(o) ==> GREY(v)
		H&P_3:	stageC = Tracing
			&&	∀t·phaseC = phase[t] = Async
			&&	v.color = BLACK
			&&	GREY(v) = n ≥ 1
			&&	(.. || ..)
			&&	{old, v} ⊆ GREY U BLACK
		C_3:	GREY(v) = n - 1
		
		sp_3 = ∃y·{
			GREY(v) = n-1
		&&	stageC = Tracing
		&&	∀t·phaseC = phase[t] = Async
		&&	v.color = BLACK
		&&	y = n ≥ 1
		&&	(.. || ..)
		&&	{old, v} ⊆ GREY U BLACK
		}
		
	sp_3 => H? success

*	(19)

		H&P:	phase[t] = Sync2
			&&	phaseC = Async
			&&	roots[t] ⊆ GREY
			&&	(.. || ..)
			&&	{old, v} ⊆ GREY U BLACK
		C:		phase[t] = Async
		
		sp = ∃y·{
			phase[t] = Async
		&&	y = Sync2
		&&	phaseC = Async
		&&	roots[t] ⊆ GREY
		&&	(.. || ..)
		&&	{old, v} ⊆ GREY U BLACK
		}

	sp => H? success

*	(29) only change lastRead[t], independent

-----

### *C*: EmptyCollectorStack()

##### S (phase[t], phaseC, stageC)

	H: (∀t· phase[t] = phaseC = Async) && stageC = Tracing

*	(6)

		H&P:	{∃t· phase[t] (+) 1 = phaseC && ∀t· phase[t] = phaseC} == false

*	UpdateResting:..(14) change x.f, independent
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
*	UpdateResting:..(14) change x.f, independent
*	(15) only add object to GREY, those already in GREY are not affected
*	(19) change phase[t], independent
*	(25) change a register & roots[t], reachables(X) starts from X, thus independent
*	(26)(27) change freelist & obj's color, independent
*	(31) change bucket[t], independent


##### after 7 (bucket[C])

	H:	S && bucket[C] ≠ ∅

*	(6) change phase[t], independent
*	UpdateResting:..(14) change x.f, independent
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
*	UpdateResting:..(14) change x.f, independent
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
*	UpdateResting:

		H&P:	{stageC ∈ {RESTING, CLEAR_OR_MARKING} && stageC = Tracing} == false

*	(12)

		H&P:	{phase[t] = Sync1 && ∀t· phase[t] = phaseC = Async} == false

*	(13)

		H&P:	{phase[t] = Sync2 && ∀t· phase[t] = phaseC = Async} == false

*	(14)

		H&P:	{ob, v'} ⊆ reachables(roots[t])
			&&	{v'} ⊆ GREY U BLACK
			&&	(ob.f |-> o'' || ∃v· ob.f |-> v && v ∈ GREY U BLACK)
			&&	o'' ∈ GREY U BLACK
		C:		ob.f |-> v'
		
		sp = ∃y·{
			ob.f |-> v'
		&&	{ob, v'} ⊆ reachables(roots[t])
		&&	{v', o''} ⊆ GREY U BLACK
		&&	(y |-> o'' || ∃v· y |-> v && v ∈ GREY U BLACK)
		}
		
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
*	UpdateResting:

		H&P:	{stageC ∈ {RESTING, CLEAR_OR_MARKING} && stageC = Tracing} == false

*	(12)

		H&P:	{phase[t] = Sync1 && ∀t· phase[t] = phaseC = Async} == false

*	(13)

		H&P:	{phase[t] = Sync2 && ∀t· phase[t] = phaseC = Async} == false

*	(14)

		H&P:	{ob, v'} ⊆ reachables(roots[t])
			&&	{v'} ⊆ GREY U BLACK
			&&	(ob.f |-> o'' && o'' ∈ GREY U BLACK || o'' ∈ GREY && (∃v· ob.f |-> v && v ∈ GREY U BLACK))
			&&	o''.color = WHITE
		C:		ob.f |-> v'
		
		sp = ∃y·{
			ob.f |-> v'
		&&	{ob, v'} ⊆ reachables(roots[t])
		&&	{v'} ⊆ GREY U BLACK
		&&	(y |-> o'' && o'' ∈ GREY U BLACK || o'' ∈ GREY && (∃v· y |-> v && v ∈ GREY U BLACK))
		&&	o''.color = WHITE
		}

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
*	UpdateResting:

		H&P:	{stageC ∈ {RESTING, CLEAR_OR_MARKING} && stageC = Tracing} == false

*	(12)

		H&P:	{phase[t] = Sync1 && ∀t· phase[t] = phaseC = Async} == false

*	(13)

		H&P:	{phase[t] = Sync2 && ∀t· phase[t] = phaseC = Async} == false

*	(14)

		H&P:	{ob, v'} ⊆ reachables(roots[t])
			&&	{v'} ⊆ GREY U BLACK
			&&	(ob.f |-> o'' || (∃v· ob.f |-> v && v ∈ GREY U BLACK))
			&&	o''.color = WHITE
			&&	o'' ∈ GREY
		C:		ob.f |-> v'
		
		sp = ∃y·{
			ob.f |-> v'
		&&	{ob, v'} ⊆ reachables(roots[t])
		&&	{v'} ⊆ GREY U BLACK
		&&	(y |-> o'' || (∃v· y |-> v && v ∈ GREY U BLACK))
		&&	o''.color = WHITE
		&& o'' ∈ GREY
		}

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
*	UpdateResting:

		H&P:	{stageC ∈ {RESTING, CLEAR_OR_MARKING} && stageC = Tracing} == false

*	(12)

		H&P:	{phase[t] = Sync1 && ∀t· phase[t] = phaseC = Async} == false

*	(13)

		H&P:	{phase[t] = Sync2 && ∀t· phase[t] = phaseC = Async} == false

*	(14)

		H&P:	{ob, v'} ⊆ reachables(roots[t])
			&&	{v'} ⊆ GREY U BLACK
			&&	(∀ v ∈ Obj, f ∈ fields(ob)· ob.f |-> v => v ∈ BLACK U GREY)
		C:		ob.f |-> v'
		
		sp = ∃y·{
			ob.f |-> v'
		&&	{ob, v'} ⊆ reachables(roots[t])
		&&	{v'} ⊆ GREY U BLACK
		&&	(∀ v ∈ Obj, f ∈ fields(ob)· y |-> v => v ∈ BLACK U GREY)
		}

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
*	UpdateResting:..(14) change ob.f, independent
*	(15) change GREY, independent
*	(19) change phase[t], independent
*	(25) change register & roots[t], independent
*	(26)(27)

		H&P:	{ob.color = BLACK && ob.color = BLUE} == false

*	(31) change bucket[t], independent


##### after 18 (BLACK, reachables(), GREY, bucket[C])

	H:	S && X ⊆ BLACK && reachables(Y) ⊆ reachables(GREY) U BLACK && bucket[C] ≠ ∅

*	(6) change phase[t], independent
*	UpdateResting:..(14) here X and Y are local variables, setting ob.f won't change them, thus independent
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

*	(6) change phase[t], independent
*	UpdateResting:..(14) change ob.f, independent
*	(15)

		H&P:	o ∈ reachables(roots[t])
			&&	GREY = R
			&&	GREY ≠ ∅
			&&	bucket[t] ≠ ∅
		C:		GREY = R (+) {o}
		
		sp = ∃y·{
			GREY = y (+) {o}
		&&	o ∈ reachables(roots[t])
		&&	y = R
		&&	y ≠ ∅
		&&	bucket[t] ≠ ∅
		}

	sp => H? success

*	(19) change phase[t], independent
*	(25) change register & roots[t], independent
*	(26)(27) change ob.color, independent
*	(31)

		H&P:	lastWrite[t] = v
			&&	v + n ≤ BUCKET_SIZE
			&&	bucket[t] ≠ ∅
			&&	GREY ≠ ∅
		C:		lastWrite[t] = v + n
		
		sp = ∃y·{
			lastWrite[t] = v + n
		&&	y = v
		&&	v + n ≤ BUCKET_SIZE
		&&	bucket[t] ≠ ∅
		&&	GREY ≠ ∅
		}

	sp => H? success

So Q is proved correct with respect to all relies, from now on, Q can be used without checking again.


##### after 4 (GREY, bucket[t])

	H:	Q && o ∈ GREY && o ∈ bucket[t]

*	(6) change phase[t], independent
*	UpdateResting:..(14) change ob.f, independent
*	(15) only add object into GREY, those already in GREY are not affected
*	(19) change phase[t], independent
*	(25) change register & roots[t], independent
*	(26)(27) change ob.color, independent
*	(31)

		H&P:	lastWrite[t] = v
			&&	v + n ≤ BUCKET_SIZE
			&&	o ∈ GREY
			&&	o ∈ bucket[t]
		C:		lastWrite[t] = v + n
		
		sp = ∃y·{
			lastWrite[t] = v + n
		&&	y = v
		&&	v + n ≤ BUCKET_SIZE
		&&	o ∈ GREY
		&& o ∈ bucket[t]
		}

	sp => H? success


##### after 5 (o.color, GREY, bucket[t])

	H:	Q && o.color = WHITE && o ∈ GREY && o ∈ bucket[t]

*	(6) change phase[t], independent
*	UpdateResting:..(14) change ob.f, independent
*	(15) only add object into GREY, those already in GREY are not affected
*	(19) change phase[t], independent
*	(25) change register & roots[t], independent
*	(26)(27)

		H&P:	{o.color = WHITE && o.color = BLUE && ..} == false

*	(31)

		H&P:	lastWrite[t] = v
			&&	v + n ≤ BUCKET_SIZE
			&&	o ∈ GREY
			&&	o ∈ bucket[t]
			&&	o.color = WHITE
		C:		lastWrite[t] = v + n
		
		sp = ∃y·{
			lastWrite[t] = v + n
		&&	y = v
		&&	v + n ≤ BUCKET_SIZE
		&&	o ∈ GREY
		&&	o ∈ bucket[t]
		&&	o.color = WHITE
		}

	sp => H? success


##### after 6 (o.color, GREY, bucket[t], bucket[C])

	H:	Q && o.color = WHITE && o ∈ GREY && o ∈ bucket[t] o ∈ bucket[C]

*	(6) change phase[t], independent
*	UpdateResting:..(14) change o.f, independent
*	(15) only add object into GREY, those already in GREY are not affected
*	(19) change phase[t], independent
*	(25) change register & roots[t], independent
*	(26)(27)

		H&P:	{o.color = WHITE && o.color = BLUE && ..} == false

*	(31)

		H&P:	lastWrite[t] = v
			&&	v + n ≤ BUCKET_SIZE
			&&	o.color = WHITE
			&&	o ∈ GREY
			&&	o ∈ bucket[t]
			&&	o ∈ bucket[C]
		C:		lastWrite[t] = v + n
		
		sp = ∃y·{
			lastWrite[t] = v + n
		&&	y = v
		&&	v + n ≤ BUCKET_SIZE
		&&	o.color = WHITE
		&&	o ∈ GREY
		&&	o ∈ bucket[t]
		&&	o ∈ bucket[C]
		}

	sp => H? success

