##### What for:

This is just for demonstration of applying the idea in paper *Explicit Stabilisation for Modular Rely-Guarantee Reasoning* to the proof of on-the-fly gc algorithm.

This is the second try of applying that idea. This time, I will try the forward-thinking way, I will specify the sequential assertions first and generate the final assertions as they do. At the end, I will check the difference between the specified assertions and the generated assertions.


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

Here the Phase_inv[t] is:

	∀t · phase[t] ≤ phaseC ≤ phase[t] (+) 1


##### Idea in the paper

Rule BASIC-S: (see Fig.3 in the paper)

	|- {p} c {q}	pbar ∩ c ⊆ G
	---------------------------
	  R,G |- {|p」R} c {「q| R}

Due to the inefficiency of writing math symbol here, I use

*	「P|R to represent the strongest assertion that is weaker than P under R
*	|P」R to represent the weakest assertion that is stronger than P under R


##### Using the idea of *Explicit Stabilisation*

First, I will specify the assertions according to sequential requirements.

Below is the initial framework of the code & assertions: (Phase_inv[t] is already known)

		Pre = Phase_inv[t]
		t: cooperate() {
			{ Phase_inv[t] } ->>
			{ ?? }
	1:		tmp = phaseC;
			{ ?? }
	2:		if phase[t] < tmp
	3:		then
				{ ?? /\ phase[t] < tmp }
				==>
				{ ?? }
	4:			phase[t] = tmp
				{ ?? }
	5:		else
				{ ?? /\ phase[t] ≥ tmp}
				==>
				{ ?? }
	6:			skip
				{ ?? }
			{ ?? }
			==>
			{ Phase_inv[t] }
		}
		Post = Phase_inv[t]

So I filled the assertions:

	Let Inv_t' := ∀t' · (t' ≠ t /\ phase[t'] ≤ phaseC ≤ phase[t'] (+) 1
	// Inv_t' is part of Phase_inv[t]

		Pre = Phase_inv[t]
		t: cooperate() {
			{ Phase_inv[t] }
			==>
			{ phase[t] ≤ phaseC /\ Inv_t' }
	1:		tmp = phaseC;
			{ phase[t] ≤ phaseC /\ Inv_t' /\ tmp = phaseC }
	2:		if phase[t] < tmp
	3:		then
				{ phase[t] ≤ phaseC /\ Inv_t' /\ tmp = phaseC
				/\ phase[t] < tmp }
				==>
				{ Inv_t' /\ tmp = phaseC }
	4:			phase[t] = tmp
				{ phase[t] = phaseC /\ Inv_t' /\ tmp = phaseC }
	5:		else
				{ phase[t] ≤ phaseC /\ Inv_t' /\ tmp = phaseC
				/\ phase[t] ≥ tmp }
				==>
				{ phase[t] = phaseC /\ Inv_t' /\ tmp = phaseC }
	6:			skip
				{ phase[t] = phaseC /\ Inv_t' /\ tmp = phaseC }

			{ phase[t] = phaseC /\ Inv_t' /\ tmp = phaseC }
			==>
			{ Phase_inv[t] }
		}
		Post = Phase_inv[t]

<br/>

Then I picked the assertions before & after line 1 to demonstrate the idea of "Explicit Stabilisation":

		P: { phase[t] ≤ phaseC /\ Inv_t' }
	1:		tmp = phaseC;
		Q: { phase[t] ≤ phaseC /\ Inv_t' /\ tmp = phaseC }

The only Rely that may influence here is:

	R: ￼{ ∀t · phase[t] = phaseC = X }
		phaseC = X (+) 1

Here R is the only one rely. If there are n relies, we need to check each rely separately (n iterations).

Calculation of |P」R: (the weakest precondition of R* given postcondition P)

	{ ?? } R { phase[t] ≤ phaseC /\ Inv_t' }

1.	R is executed:

		Let R = (PRE, CMD)
		So PRE = { ∀t · phase[t] = phaseC = X }
		   CMD = "phaseC = X (+) 1"

		?? = wlp(CMD, phase[t] ≤ phaseC /\ Inv_t') /\ PRE
		   = ∀t · phase[t] = phaseC = X

2.	R is not executed:

		?? = { phase[t] ≤ phaseC /\ Inv_t' }
		  skip
		{ phase[t] ≤ phaseC /\ Inv_t' }

3.	Combine these two together (**intuitively** OR), we get:

		∴ |P」R = { phase[t] ≤ phaseC /\ Inv_t' }


Calculation of 「Q|R: (the strongest postcondition of R* given precondition Q)

	{ phase[t] ≤ phaseC /\ Inv_t' /\ tmp = phaseC } R { ?? }

1.	R is executed:

		Let R = (PRE, CMD)
		So PRE = { ∀t · phase[t] = phaseC = X }
		   CMD = "phaseC = X (+) 1"

		{ phase[t] ≤ phaseC /\ Inv_t' /\ tmp = phaseC
		/\ ∀t · phase[t] = phaseC = X }
		  phaseC = X (+) 1
		{ ?? }

		?? = sp(CMD, ...)
		   = sp(phaseC = X (+) 1, ∀t · phase[t] = phaseC = tmp = X)
		   = ∃y· phaseC = X (+) 1 /\ (∀t · phase[t] = y = tmp = X)
		   = phaseC = X (+) 1 /\ (∀t · phase[t] = tmp = X)

2.	R is not executed:

		{ phase[t] ≤ phaseC /\ Inv_t' /\ tmp = phaseC }
		  R
		{ phase[t] ≤ phaseC /\ Inv_t' /\ tmp = phaseC }

3.	Combine these two together (**intuitively** OR), we get:

	*	phase[t] & phaseC: (forall t)
	
			phase[t] ≤ phaseC /\ Inv_t'

	*	phase[t] & tmp: (tmp is local)
	
			phase[t] ≤ tmp
	
	*	phaseC & tmp:

			tmp ≤ phaseC ≤ tmp (+) 1

	*	Final result:

			∴ 「Q|R = phase[t] ≤ phaseC /\ Inv_t'
					/\ phase[t] ≤ tmp
					/\ tmp ≤ phaseC ≤ tmp (+) 1

So the final assertions for the code in line 1 is:

	{ phase[t] ≤ phaseC /\ Inv_t' }
	  tmp = phaseC;
	{ phase[t] ≤ phaseC /\ Inv_t' /\ phase[t] ≤ tmp /\ tmp ≤ phaseC ≤ tmp (+) 1 }

For comparison, the original code & assertions are:

		{ Phase_inv[t] }
	1:    tmp = phaseC;
        { Phase_inv[t] /\ tmp ≤ phaseC ≤ tmp (+) 1 /\ phase[t] ≤ tmp }

ALMOST THE SAME!!
