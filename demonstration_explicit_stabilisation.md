##### What for:

This is just for demonstration of applying the idea in paper *Explicit Stabilisation for Modular Rely-Guarantee Reasoning* to the proof of on-the-fly gc algorithm.


##### Original Code & Assertions

The *cooperate* method on mutator thread is picked for demonstration. (More specifically, just the two assertions before & after line 1..)

It's code and assertions are copied from the proof draft:

		Pre = Phase_inv[t]
		t: cooperate() {
			{ Phase_inv[t] }
	1:		tmp = phaseC;
			{ Phase_inv[t] /\ { tmp ≤ phaseC ≤ tmp (+) 1 /\ phase[t] ≤ tmp } }
	2:		if phase[t] < tmp
	3:		then
				{ Phase_inv[t] /\ { tmp ≤ phaseC ≤ tmp (+) 1 /\ phase[t] < tmp } }
				==>
				{ Phase_inv[t] /\ { phase[t] (+) 1 = phaseC /\ tmp = phaseC } }
	4:			phase[t] = tmp
				{ Phase_inv[t] }
		}
		Post = Phase_inv[t]


##### Idea in the paper

Rule BASIC-S: (see Fig.3 in the paper)

	|- {p} c {q}	pbar ∩ c ⊆ G
	---------------------------
	  R,G |- {[p」R} c {「q]R}

Due to the inefficiency of writing math symbol here, I use

*	「P]R to represent the strongest assertion that is weaker than P under R
*	[P」R to represent the weakest assertion that is stronger than P under R


##### Using the idea of *Explicit Stabilisation*

Invariants are omitted.

Checking if the command satisfies the Guarantee of current thread is also omitted.

Original:

	P: { True }
		tmp = phaseC;
	Q: { tmp ≤ phaseC ≤ tmp (+) 1 /\ phase[t] ≤ tmp }

↓

With *Explicit Stabilisation*:

The only Rely that may influence here is:

	R: ￼{ ∀t · phase[t] = phaseC = X }
		phaseC = X (+) 1

Calculation of [P」R: (the weakest precondition of R* given postcondition P)
	
	{??} R { True }

	∴ [P」R = True
	]
Calculation of 「Q]R: (the strongest postcondition of R* given precondition Q)

	{ tmp ≤ phaseC ≤ tmp (+) 1 /\ phase[t] ≤ tmp } R { ?? }
		
Here R is only one rely, there are two possibilities, either R get executed or not. If there are n relies, we need to check each rely separately (n iterations).
	
1.	Executed:

		{ tmp ≤ phaseC ≤ tmp (+) 1 /\ phase[t] ≤ tmp } /\ { ∀t · phase[t] = phaseC = X }
		==>
		{ ∀t · phase[t] = phaseC = X = tmp }
		phaseC = X (+) 1
		{ ?? }

		∴ ?? = ∃y · { ∀t · phase[t] = y = X = tmp } /\ phaseC = X (+) 1
			 = { ∀t · phase[t] = X = tmp } /\ phaseC = X (+) 1

2.	Not Executed:

		{ tmp ≤ phaseC ≤ tmp (+) 1 /\ phase[t] ≤ tmp }
		skip
		{ tmp ≤ phaseC ≤ tmp (+) 1 /\ phase[t] ≤ tmp }

So combine (by operator \/) these two cases:

	∴「Q]R = { tmp ≤ phaseC ≤ tmp (+) 1 /\ phase[t] ≤ tmp }

Now check if they are sequentially valid? Yes. (Also need to write down the invariant here)
	
	[P」R /\ Inv: { Phase_inv[t] /\ True }
					tmp = phaseC;
	「Q]R /\ Inv: { Phase_inv[t] /\ tmp ≤ phaseC ≤ tmp (+) 1 /\ phase[t] ≤ tmp }

Thus proved the stability of original code & assertions under all Rely.

##### Others examples

*	Line 2-3

	Original:

		P: { tmp ≤ phaseC ≤ tmp (+) 1 /\ phase[t] ≤ tmp }
			if phase[t] < tmp
			then
		Q: { phase[t] (+) 1 = phaseC /\ tmp = phaseC }
	
	↓
	
	With *Explicit Stabilisation*:

	......

*	Line 4

	Original:

		P: { phase[t] (+) 1 = phaseC /\ tmp = phaseC }
			phase[t] = tmp
		Q: { True }
	
	↓
	
	With *Explicit Stabilisation*:

	......

The two triples above can also be proved using the new idea from that paper with similar steps:

1.	Find the relevant relies
2.	Calculate [P」R
3.	Calculate 「Q]R
4.	Check that {[P」R} c {「Q]R} is a valid Hoare triple


##### Notes

*	Most assertions need to be calculated twice w.r.t. some relies R*. First in [P」R, then in 「Q]R.

	e.g. for {P} c1 {Q} c2 {R}, we have to check {P} c1 {Q} and {Q} c2 {R} separately. So Q is calculated twice. While in standard R/G, P Q R are checked only once.

*	Is it correct to calculate [P」R and「Q]R as I do?

	Currently I am using wlp and sp predicate transformers and view R as the command in the Hoare triple. Because it says so in the paper:

		P613: (page 4)
		[P」R is the weakest precondition of R* given postcondition P, while「Q]R is the strongest postcondition of R* given precondition P.


*	My opinion is that the "Explicit Stabilisation" doesn't reduce the work, on the contrary, it may demand more work due to the overhead in the 1st bullet.
