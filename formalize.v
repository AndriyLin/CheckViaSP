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
 *)

Inductive var : Type :=
  Var: nat -> var.

Definition X : var := Var 0.
Definition Y : var := Var 1.
Definition Z : var := Var 2.

(* state: the current memory map. Given one variable name, return its value or not found *)
Definition state := var -> option nat.
Definition empty_state : state :=
  fun _ => None.

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


(* TODO start from here *)

(* like ASYNCH, BLACK, TRACING and such such *)
Definition value := nat.

(* e.g. {BLACK, GREY} *)
Definition collection := list value.


Inductive assertion : Set :=
  as_and: assertion -> assertion -> assertion
| as_or: assertion -> assertion -> assertion
| as_imply: assertion -> assertion -> assertion
| as_equal: var -> value -> assertion
| as_uneq: var -> value -> assertion
| as_in: var -> collection -> assertion
| as_subset: collection -> collection -> assertion
| as_exists: var -> assertion -> assertion
| as_forall: var -> assertion -> assertion.


Inductive relyprod : Type :=
  (* precondition & command *)
  rely : assertion -> code -> relyprod.


Fixpoint sp_gen (a : assertion) (c : code) : assertion :=
  admit.

Fixpoint implies (a1 a2 : assertion) : bool :=
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

