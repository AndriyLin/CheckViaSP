(*
 * Trying to formalize the strongest postcondition
 * Andriy LIN
 *
 * Start with formalizing a tiny toy language here.
 * Then formalize the assertions.
 * Then the Strongest Postcondition.
 *)

(* The following dependencies are copied from SFLib.v *)
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)


Definition admit {T: Type} : T.  Admitted.


Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' => match m with
                | O => false
                | S m' => ble_nat n' m'
              end
  end.


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* TODOs:
 * 1. var can only bind an arithmatic expression for now. Extend to bexp, then to all exp.
 * 2. I want aexp & bexp to inherit from one exp, how?
 * 3. Add fold_constants and optimize_0plus for aexp/bexp??
 * 4. Add the index for array into var??
 * 5. return option nat brings extra troubles.
 *)

Inductive var : Type :=
  Var: nat -> var.

Definition X : var := Var 0.
Definition Y : var := Var 1.
Definition Z : var := Var 2.

(* state: the current memory map. Given one variable name, return its value or not found
option monad
maybe monad in coq
 *)
Definition state := var -> option nat.
Definition empty_state : state :=
  fun _ => None.

(* TODO make val a option nat?? *)
Definition state_update (st : state) (v : var) (val : nat) : state :=
  fun x => match x, v with
             | Var xid, Var vid => if beq_nat xid vid
                                   then Some val
                                   else st x
           end.

(* arithmatic expression *)
Inductive aexp : Type :=
  ANum: nat -> aexp
| APlus: aexp -> aexp -> aexp
| AMinus: aexp -> aexp -> aexp
| AMult: aexp -> aexp -> aexp
| AVar: var -> aexp.

Fixpoint aeval (st : state) (ae : aexp) : option nat :=
  match ae with
    | ANum n => Some n
    | APlus a1 a2 => match aeval st a1, aeval st a2 with
                       | Some r1, Some r2 => Some (r1 + r2)
                       | _, _ => None
                     end
    | AMinus a1 a2 => match aeval st a1, aeval st a2 with
                       | Some r1, Some r2 => Some (r1 - r2)
                       | _, _ => None
                     end
    | AMult a1 a2 => match aeval st a1, aeval st a2 with
                       | Some r1, Some r2 => Some (r1 * r2)
                       | _, _ => None
                     end
    | AVar id => st id
  end.

(* boolean expression *)
Inductive bexp : Type :=
  BTrue: bexp
| BFalse: bexp
| BNot: bexp -> bexp
| BAnd: bexp -> bexp -> bexp
| BOr: bexp -> bexp -> bexp
| BEq: aexp -> aexp -> bexp
| BLe: aexp -> aexp -> bexp.

Fixpoint beval (st : state) (be : bexp) : option bool :=
  match be with
    | BTrue => Some true
    | BFalse => Some false
    | BNot b => match beval st b with
                  | None => None
                  | Some r => Some (negb r)
                end
    | BAnd b1 b2 => match beval st b1, beval st b2 with
                      | Some r1, Some r2 => Some (andb r1 r2)
                      | _, _ => None
                    end
    | BOr b1 b2 => match beval st b1, beval st b2 with
                     | Some r1, Some r2 => Some (orb r1 r2)
                     | _, _ => None
                   end
    | BEq a1 a2 => match aeval st a1, aeval st a2 with
                     | Some r1, Some r2 => Some (beq_nat r1 r2)
                     | _, _ => None
                   end
    | BLe a1 a2 => match aeval st a1, aeval st a2 with
                     | Some r1, Some r2 => Some (ble_nat r1 r2)
                     | _, _ => None
                   end
  end.

(* command *)
Inductive cmd : Type :=
  CSkip: cmd
| CAssi: var -> aexp -> cmd
| CSeq: cmd -> cmd -> cmd
| CIf: bexp -> cmd -> cmd -> cmd
| CWhile: bexp -> cmd -> cmd.

Notation "'SKIP'" := CSkip.
Notation "a '::=' e" := (CAssi a e) (at level 60).
Notation "c1 ';;' c2" := (CSeq c1 c2) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2" := (CIf b c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := (CWhile b c) (at level 80, right associativity).

Example test1 : cmd :=
  IFB (BEq (AVar X) (AVar Y))
  THEN Z ::= (ANum 1)
  ELSE Z ::= (ANum 0).

Example test2 : cmd :=
  Z ::= AVar X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AVar Z) (ANum 0)) DO
    Y ::= AMult (AVar Y) (AVar Z);;
    Z ::= AMinus (AVar Z) (ANum 1)
  END.


Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : cmd -> state -> state -> Prop :=
| ESkip: forall st,
           SKIP / st || st
| EAssi: forall st a e n,
           aeval st e = Some n ->
           (a ::= e) / st || (state_update st a n)
| ESeq: forall st st1 st2 c1 c2,
          c1 / st || st1 ->
          c2 / st1 || st2 ->
          (c1 ;; c2) / st || st2
| EIfTrue: forall st b c1 c2 st1,
             beval st b = Some true ->
             c1 / st || st1 ->
             (IFB b THEN c1 ELSE c2) / st || st1
| EIfFalse: forall st b c1 c2 st2,
              beval st b = Some false ->
              c2 / st || st2 ->
              (IFB b THEN c1 ELSE c2) / st || st2
| EWhileEnd: forall st b c,
               beval st b = Some false ->
               (WHILE b DO c END) / st || st
| EWhileLoop: forall st b c st1 st2,
                beval st b = Some true ->
                c / st || st1 ->
                (WHILE b DO c END) / st1 || st2 ->
                (WHILE b DO c END) / st || st2

where "c1 '/' st '||' st'" := (ceval c1 st st').


Definition assertion := state -> Prop.

(* TODO now that state gives back an "option nat", it becomes incovenient? *)
Definition as1 : assertion := fun st => st X < 1 /\ st Y < 2.

Definition assertion_imply (P Q : assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assertion_imply P Q) (at level 80).
Notation "P <<->> Q" := (P ->> Q /\ Q ->> P) (at level 80).


Definition hoare_triple (P : assertion) (c : cmd) (Q : assertion) : Prop :=
  forall st st',
    c / st || st' ->
    P st ->
    Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level).


(* Followed by the hoare rules *)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.


Definition assertion_sub X a P : assertion :=
  fun (st : state) =>
    P (state_update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.


Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st'). 
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP. 
  apply Himp.
  apply (Hhoare st st'). 
  assumption. assumption. Qed.


Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.


Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst. 
  Case "b is true".
    apply (HTrue st st'). 
      assumption. 
      split. assumption. 
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st'). 
      assumption. 
      split. assumption.
             apply bexp_eval_false. assumption. Qed.


Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction 
     on He, because, in the "keep looping" case, its hypotheses 
     talk about the whole loop instead of just c *)
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  ceval_cases (induction He) Case;
    try (inversion Heqwcom); subst; clear Heqwcom.

  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false. assumption.

  Case "E_WhileLoop".
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(* TODO start from here *)



(* For strongest postcondition, resume later *)

Inductive relyprod : Type :=
  (* precondition & command *)
  rely : assertion -> code -> relyprod.


Fixpoint sp_gen (a : assertion) (c : cmd) : assertion :=
  admit.

Definition sp_check (a : assertion)(r : relyprod) : bool :=
  match r with
    | rely pre com => implies (sp_gen (as_and a pre) com) a
  end.


Fixpoint sp_all (a : assertion) (rs : list relyprod) : assertion :=
  match rs with
    | nil => a
    | cons hd tl => match hd with
                      | rely pre com => sp_all (sp_gen (as_and a pre) com) tl
                    end
  end.

