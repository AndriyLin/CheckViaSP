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


Inductive var : Type :=
(* TODO bind a string in the future *)
  Var: nat -> var.

Definition X : var := Var 0.
Definition Y : var := Var 1.
Definition Z : var := Var 2.


(* context is the current memory, given one variable name, return its value or not found *)
Definition ctx := var -> option nat.
Definition ctx_null : ctx :=
  fun n => None.

Definition ctx_update (c : ctx) (v : var) (val : nat) : ctx :=
  fun x => match x, v with
             | Var xid, Var vid => if beq_nat xid vid
                                   then Some val
                                   else c x
           end.

Inductive aexp : Type :=
  ANum: nat -> aexp
| APlus: aexp -> aexp -> aexp
(* I can't have ANeg because nat is always >= 0 *)
| AMinus: aexp -> aexp -> aexp
| AMult: aexp -> aexp -> aexp
(* Now var can only refer to arithmatic exp *)
| AVar: var -> aexp.

Fixpoint aeval (c : ctx) (ae : aexp) : option nat :=
  match ae with
    | ANum n => Some n
    | APlus a1 a2 => let r1 := (aeval c a1) in
                     match r1 with
                       | None => None
                       | Some r1' => let r2 := (aeval c a2) in
                                     match r2 with
                                       | None => None
                                       | Some r2' => Some (r1' + r2')
                                     end
                     end
    | AMinus a1 a2 => let r1 := (aeval c a1) in
                      match r1 with
                        | None => None
                        | Some r1' => let r2 := (aeval c a2) in
                                      match r2 with
                                        | None => None
                                        | Some r2' => Some (r1' - r2')
                                      end
                      end
    | AMult a1 a2 => let r1 := (aeval c a1) in
                     match r1 with
                       | None => None
                       | Some r1' => let r2 := (aeval c a2) in
                                     match r2 with
                                       | None => None
                                       | Some r2' => Some (r1' * r2')
                                     end
                     end
    | AVar id => c id
  end.

(* TODO I want to make aexp and bexp inherit the same "exp", how? *)

Inductive bexp : Type :=
  BTrue: bexp (* TODO why do I need these two, cannot directly use true & false?? *)
| BFalse: bexp
| BNot: bexp -> bexp
| BAnd: bexp -> bexp -> bexp
| BOr: bexp -> bexp -> bexp
| BEq: aexp -> aexp -> bexp
| BLe: aexp -> aexp -> bexp.

Fixpoint beval (c : ctx) (be : bexp) : option bool :=
  match be with
    | BTrue => Some true
    | BFalse => Some false
    | BNot b => let r := beval c b in
                match r with
                  | None => None
                  | Some r' => Some (negb r')
                end
    | BAnd b1 b2 => let r1 := beval c b1 in
                    match r1 with
                      | None => None
                      | Some r1' => let r2 := beval c b2 in
                                    match r2 with
                                      | None => None
                                      | Some r2' => Some (andb r1' r2')
                                    end
                    end
    | BOr b1 b2 => let r1 := beval c b1 in
                   match r1 with
                     | None => None
                     | Some r1' => let r2 := beval c b2 in
                                   match r2 with
                                     | None => None
                                     | Some r2' => Some (orb r1' r2')
                                   end
                   end
    | BEq a1 a2 => let r1 := aeval c a1 in
                   match r1 with
                     | None => None
                     | Some r1' => let r2 := aeval c a2 in
                                   match r2 with
                                     | None => None
                                     | Some r2' => Some (beq_nat r1' r2')
                                   end
                   end
    | BLe a1 a2 => let r1 := aeval c a1 in
                   match r1 with
                     | None => None
                     | Some r1' => let r2 := aeval c a2 in
                                   match r2 with
                                     | None => None
                                     | Some r2' => Some (ble_nat r1' r2')
                                   end
                   end
  end.


Inductive cmd : Type :=
  CSkip: cmd
| CAssi: var -> aexp -> cmd (* I want it to be natexp or boolexp or strexp, how? *)
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

Inductive ceval : cmd -> ctx -> ctx -> Prop :=
| ESkip: forall st,
           SKIP / st || st
| EAssi: forall st a e n,
           aeval st e = Some n ->
           (a ::= e) / st || (ctx_update st a n)
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


(* temporary, just to have a type named string, because I don't know to represent string here. *)
Definition string := nat.


Inductive var : Set :=
  var_name : string -> var (* e.g. phaseC *)
| var_index : var -> var -> var. (* e.g. phase[t] *)


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

Definition code : Set := string.

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

