# Predicate Transformer

	{ P0: PRE }
	  c1
	{ P1 }
	  c2
	{ P2 }
	  ..
	{ P_n-1 }
	  cn
	{ Pn: POST }

Followed by my understanding:

### Generating Overall Assertion A

If only one assertion is given, we can use wlp/sp to generate all the assertions. So assume that we have all the assertions in place. P0 = PRE, P1 = "after c1", .. Pn = POST.

Then we get all the assertions together and combine the similar terms. Only by combining similar terms is this meaningful, otherwise it's the same as previous approach.


Definition combine (a1 a2 : assertion) : assertion := ...

	Ai = { Pn (POST), i = n\\
	     { combine (Pi+1, Ai+1), 0 ≤ i ≤ n-1
	A = A0

The direction of combining should not make any difference. Forward & Backward should have the same result.

	Ai =	{ P0 (PRE), i = 0
			{ combine (Pi-1, Ai-1), 1 ≤ i ≤ n
	A = An

"The same result" may depend on the implementation of combine(). Also it may not be literally the same. (functional_extensionality).


After combine(), we get a "overall assertion" A. It should have the following property:

	forall Pi, Pi ->> A|Pi
		where A|Pi are those subparts in A that are corresponding to Pi
		e.g. A = {x > 10 /\ y < 100}, Pi = {x = 11}, ∴ A|Pi = {x > 10}


Rules in combine(a1, a2), i.e. the transformer

*	if a1 a2 don't have any variable in common, then just a1 /\ a2
*	treat { a1 ->> a2 } as { a1 /\ a2 \/ ~a1}
*	**TODO** what if combine { x <= 10 } { x > 5 \/ y < 10}
*	**TODO** other rules?

// any papers about this?

assertion types used in the proof draft

assertion ::=

	|	∀ var · assertion
	|	∃ var · assertion
	|	assertion /\ assertion
	|	assertion \/ assertion
	|	assertion ->> assertion
	|	aexp = aexp
	|	aexp ≠ aexp
	|	aexp <= aexp
	|	aexp >= aexp
	|	aexp |-> aexp
	|	{ .. } ⊆ { .. }
	|	aexp ∈ { .. }


### Use Overall Assertion A

##### A is stable wrt. rely

Theorem BASIS:

	forall P c Pi A,
		A = combine all Pi together ->
		A is stable wrt. rely(P, c) ->
		forall i, Pi is stable to rely(P, c)

Is this provable? I think so.


As stated in theorem BASIS, if A is stable wrt. a rely. All the assertions are stable wrt. it. So this piece of code is proved.


##### A is not stable wrt. rely

It depends on the implementation of combine()

*	If combine() do not relax/generalize any Pi, e.g.

		P0 = { x = 0 }, P1 = { x = 10 }
		A = combine(P0, P1) = { x ∈ {0, 10} }

	Then: if A is not stable wrt. some rely, some Pi must fail the stability check.
	
	Theorem rely_fail:
	
		forall P c Pi A,
			A = combine all Pi together ->
			A is not stable wrt. rely(P, c) ->
			∃ i, Pi is not stable wrt. rely(P, c)


*	If combine() does relax/generalize) some Pi, e.g.

		P0 = { x = 0 }, P1 = { x = 10 }
		A = combine(P0, P1) = { 0 <= x <= 10 }

	Then: even if A is not stable wrt. some rely, it could still be the case that all Pi are stable wrt. that rely. E.g.
	
		Pi: { x = 11 }, { x = 12 } ... { x = 14 }, { x = 16 }, ... { x = 20 }
		A = combine (..) = { 11 <= x <= 20 } // including 15
		Rely: { x = 15 }
				x = 100
		Therefore, A fails the rely
		but each Pi is in fact stable wrt. the rely.


I think, the coarser combine() is implemented, the more likely that A fails but all Pi passes the check.


##### What to do after the stability failure

*	"naive" approach

	binary search, check if the overall assertion out of half of Pi succeeds the stability check. Recursively do this.

*	"smart" approach

	See which subparts in A make it unstable. e.g.

		A = o /\ o /\ o .. o /\ A' /\ o .. /\ o

		if A' is the assertion that makes A unstable wrt. rely(P, c)
		then those Pi that can ->> A' will be unstable wrt. rely(P, c)

