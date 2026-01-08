(** Classical proof of the Infinite Pigeonhole Principle with corecursion *)
(** For a given stream of Boolean values, this implementation classically
    returns either a stream of all "true" or a stream of all "false";
    that is, observationally, it returns as long as needed approximations
    of the corresponding infinite outputs (possibly backtracking on the way) *)

Require Import List.
Require Import Bool.
Import ListNotations.
Import EqNotations.

(** Axiomatization of control *)
Definition cont A := A -> Empty_set.
Parameter callcc : forall {A}, (cont A -> A) -> A.
Parameter throw : forall {A B}, cont A -> A -> B.

(** Relevant and non-relevant forms of sigma-types *)
Notation "( x ; .. ; y ; z )" := (existT _ x .. (existT _ y z) ..) (at level 0, format "'[' ( x ;  '/ ' .. ;  '/ ' y ;  '/ ' z ) ']'").
Notation "( x ; | y | )" := (exist _ x y) (at level 0, format "'[' ( x ;  '/  ' | y | ) ']'").
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").
Notation "x ..1" := (proj1_sig x) (at level 1, left associativity, format "x ..1").
Notation "x ..2" := (proj2_sig x) (at level 1, left associativity, format "x ..2").

Record sigP (A : Prop) (P : A -> Type) : Type :=
    existP { proj1P : A; proj2P : P proj1P }.
Notation "{ x &P P }" := (sigP _ (fun x => P)) (at level 0, x at level 99) : type_scope.
Notation "{ x : A &P P }" := (sigP A (fun x : A => P)) (at level 0, x at level 99) : type_scope.
Notation "( | x | ; y )" := (existP _ _ x y) (at level 0, format "'[' ( | x | ;  '/  ' y ) ']'").

(** General streams *)
CoInductive stream A := { head : A; tail : stream A }.

Arguments head {A}.
Arguments tail {A}.

Fixpoint nth_tail {A} (n : nat) (s : stream A) {struct n} : stream A :=
  match n with
  | 0 => s
  | S m => tail (nth_tail m s)
  end.

Definition index {A} (n : nat) (s : stream A) := head (nth_tail n s).

(** Propositional truncation *)
Inductive trunc (A : Type) : Prop := Trunc : A -> trunc A.

Arguments Trunc {A}.

Inductive holds {A} P : trunc A -> Prop :=
  InTrunc x : P x -> holds P (Trunc x).

Arguments InTrunc {A P} _.

Notation "'for' x 'in' [ y ]  'holds' P" := (holds (fun y => P) x) (at level 200, P at level 70).

(** Satisfaction on option types *)
Inductive if_some (P : nat -> Prop) : option nat -> Prop :=
  | IfSome n : P n -> if_some P (Some n)
  | IfNone : if_some P None.

Arguments IfSome {P} _.
Arguments IfNone {P}.

Notation "'if' n 'is' 'some' n' 'then' P" := (if_some (fun n' => P) n) (at level 200, P at level 70).

(** Specification of the infinite pigeon hole *)
Definition ok (bs : trunc (stream bool)) n depth :=
  for bs in [bs] holds for n in [n] holds if n is some n then (index depth bs = index n bs /\ n < depth).

CoInductive ipp_stream bs n : Type :=
  { depth : nat;
    rest  : unit -> ipp_stream bs (Trunc (Some depth)); (* delay explicitly, since extraction does not do it *)
    hyp   : ok bs n depth }.

Arguments depth {bs n} _.
Arguments rest {bs n}.

Definition coiter bs n X (base : forall n, X n -> { depth : nat | ok bs n depth })
  (next : forall n, forall s : X n, X (Trunc (Some (base n s)..1))) :=
  (cofix f n (s : X n) : ipp_stream bs n :=
  {| depth := (base n s)..1;
     rest  := fun _ => f _ (next n s);
     hyp   := (base n s)..2
 |}) n.

Definition corecM bs n X (base : forall n, X n -> { depth : nat | ok bs n depth })
  (next : forall n, forall s : X n, (ipp_stream bs (Trunc (Some (base n s)..1)) + X (Trunc (Some (base n s)..1)))%type) :=
  (cofix f n (s : X n) : ipp_stream bs n :=
  {| depth := (base n s)..1;
     rest  := fun _ => match next n s with inl s0 => s0 | inr x => f _ x end;
     hyp   := (base n s)..2;
  |}) n.

Definition corecC bs n X (base : forall n, X n -> { depth : nat | ok bs n depth })
  (next : forall n, forall s : X n, cont (ipp_stream bs (Trunc (Some (base n s)..1))) -> X (Trunc (Some (base n s)..1))) :=
  corecM bs n X base (fun n0 s =>
     callcc (fun disjret => inr (next n0 s (fun ret => disjret (inl ret))))).

(** Linking the last integer in a stream to the previous integer *)
Definition prev_spec (bs : stream bool) b n' depth :=
  if n' is some n' then (index n' bs = b /\ n' < depth).

(** Properties of the current tail and position *)
Definition untruncated_spec bs rest (b : bool) n n' depth :=
  (nth_tail (S depth) bs = rest /\ index depth bs = b)
  /\ prev_spec bs b n depth
  /\ prev_spec bs (negb b) n' depth.

Definition spec bs rest (b : bool) n n' depth :=
  for n in [n] holds for n' in [n'] holds untruncated_spec bs rest (b : bool) n n' depth.

(** The data for dealing with boolean b *)
Definition state0 bs b n :=
  { sp : { depth & stream bool } & { n' &P { k : cont (ipp_stream (Trunc bs) n') | spec bs sp.2 b n n' sp.1 } } }.

(** The data for dealing with boolean "neg b" *)
Definition state1 bs b n' n :=
  { sp : { depth & stream bool } | spec bs sp.2 (negb b) n n' sp.1 }.


Definition bool_dec' b b' : { b = b' } + { b = negb b' } :=
  match b, b' with
  | true, true  | false, false => left eq_refl
  | true, false | false, true  => right eq_refl
  end.

(** Extract the current depth and its properties *)
Definition spec_ok {bs rest b n n' depth} : spec bs rest b n n' depth -> ok (Trunc bs) n depth.
destruct 1. destruct H. constructor. constructor. destruct H as ((_,<-),([n (H,Hle)|],_)).
Proof.
- constructor; now split.
- constructor.
Qed.

(** Initial link between (no) last integer found and current depth *)
Definition prev_spec_init {bs} : prev_spec bs (negb (head bs)) None 0 := IfNone.

(** Link between last integer found and current depth when switching *)
Definition prev_spec_reinit {bs b depth} (e_depth : index depth bs = b)
  : prev_spec bs b (Some depth) (S depth).
Proof.
constructor. apply (conj e_depth (le_n (S depth))).
Qed.

(** Initial property of the state *)
Definition untruncated_spec_init bs : untruncated_spec bs (tail bs) (head bs) None None 0.
Proof.
apply (conj (conj eq_refl eq_refl) (conj IfNone IfNone)).
Qed.

Definition spec_init bs : spec bs (tail bs) (head bs) (Trunc None) (Trunc None) 0.
Proof.
constructor. constructor. apply untruncated_spec_init.
Qed.

(** Lift the link between last integer found and depth to the new depth *)
Definition prev_spec_step {bs b n' depth} (H : prev_spec bs b n' depth) : prev_spec bs b n' (S depth) :=
  match H with
  | IfNone  => IfNone
  | IfSome n (conj e_n le) => IfSome n (conj e_n (le_S (S n) _ le))
  end.

(** Lifting property of the state to the next position for fixed boolean *)
Definition untruncated_spec_step {bs rest b n n' depth} (e_b : head rest = b) (H : untruncated_spec bs rest b n n' depth)
  : untruncated_spec bs (tail rest) b (Some depth) n' (S depth).
Proof.
destruct H as ((e_tail,e_depth),(_,H)).
constructor; constructor.
- apply (f_equal (@tail bool) e_tail).
- apply (eq_trans (f_equal (@head bool) e_tail) e_b).
- apply (prev_spec_reinit e_depth).
- apply (prev_spec_step H).
Qed.

Definition spec_step {bs rest b n n' depth} (e_b : head rest = b) (H : spec bs rest b n n' depth)
  : spec bs (tail rest) b (Trunc (Some depth)) n' (S depth).
Proof.
destruct H, H.
constructor. constructor.
apply (untruncated_spec_step e_b H).
Qed.

(** Lifting property of the state to the next position when boolean swaps *)
Definition untruncated_spec_swap_neg {bs rest b n n' depth} (e_b : head rest = b) (H : untruncated_spec bs rest (negb b) n n' depth)
  : untruncated_spec bs (tail rest) b n' (Some depth) (S depth).
Proof.
destruct H as ((e_tail,e_depth),(H1,H2)).
constructor; constructor.
- apply (f_equal (@tail bool) e_tail).
- apply (eq_trans (f_equal (@head bool) e_tail) e_b).
- rewrite <- (negb_involutive b). apply (prev_spec_step H2).
- apply (prev_spec_reinit e_depth).
Qed.

Definition spec_swap_neg {bs rest b n' n depth} (e_b : head rest = b) (H : spec bs rest (negb b) n n' depth)
  : spec bs (tail rest) b n' (Trunc (Some depth)) (S depth).
Proof.
destruct H, H.
constructor. constructor.
apply (untruncated_spec_swap_neg e_b H).
Qed.

Definition spec_swap {bs rest b n n' depth} (e_b : head rest = negb b) (H : spec bs rest b n n' depth)
  : spec bs (tail rest) (negb b) n' (Trunc (Some depth)) (S depth).
Proof.
eapply (spec_swap_neg e_b).
rewrite negb_involutive. apply H.
Qed.

(* Core of the proof *)
Definition infinite_bool (bs: stream bool) : ipp_stream (Trunc bs) (Trunc None) :=
  let b0 := head bs in
  callcc (fun start : cont (ipp_stream (Trunc bs) (Trunc None)) =>
    coiter (Trunc bs) (Trunc None) (fun n' => state0 bs b0 n')
      (fun n '((depth;rest);(|_|;(_;|e|))) => (depth;|spec_ok e|))
      (fun n '((depth;rest);(|n'|;(switch;|e|))) =>
        match bool_dec' (head rest ) b0 return state0 bs b0 (Trunc (Some depth)) with
         |left e'' => ((S depth;tail rest);(|n'|;(switch;|spec_step e'' e|)))
         |right e'' =>
           callcc (fun restart : cont (state0 bs b0 (Trunc (Some depth))) =>
             throw switch
               (corecC (Trunc bs) n' (fun n => state1 bs b0 (Trunc (Some depth)) n)
                 (fun n' st => (st..1.1;|spec_ok st..2|))
                 (fun n' '((depth;rest);|e|) ret =>
                     match bool_dec' (head rest ) b0 with
                      |left e'' => throw restart
                        ((S depth;tail rest);(|Trunc (Some depth)|;(ret; |spec_swap_neg e'' e|)))
                      |right e'' => ((S depth;tail rest);|spec_step e'' e|)
                     end)
                 ((S depth;tail rest);|spec_swap e'' e|)))
        end)
      ((0;tail bs);(|Trunc None|;(start;|spec_init bs|)))).

(* Examples *)

Fixpoint ipp_stream_depths
  (bs : stream bool)
  (k : nat)
  (n : option nat)
  (ms : ipp_stream (Trunc bs) (Trunc n))
  : list nat :=
  match k with
  | 0 => []
  | S 0 =>  (depth ms) :: nil
  | S k' =>
      let d := depth ms in
      let ms' := rest ms tt in
      d :: ipp_stream_depths bs k' (Some d) ms'
  end.

Definition take_ipp (bs : stream bool) (ms : ipp_stream (Trunc bs) (Trunc None)) (n : nat) : list nat :=
  ipp_stream_depths bs n None ms.

Notation Cons hd tl := {| head := hd; tail := tl |}.

Axiom wrap : forall {A}, (unit -> A) -> A.
Definition test n bs := wrap (fun _ => take_ipp bs (infinite_bool bs) n).

CoFixpoint always_true: stream bool := Cons true always_true.
CoFixpoint always_false: stream bool := Cons false always_false.

Definition test_stream :=
Cons true (Cons false (Cons true (Cons false (Cons true (Cons true (Cons false (Cons false
(Cons true (Cons true always_false))))))))).
(* x = T F T F T T F F T T F^w *)

Definition test1 := test 1 test_stream.
Definition test2 := test 2 test_stream.
Definition test3 := test 3 test_stream.
Definition test4 := test 4 test_stream.
Definition test5 := test 5 test_stream.
Definition test6 := test 6 test_stream.
Definition test7 := test 7 test_stream.


CoFixpoint prova1: stream bool := Cons true (Cons true (Cons false (Cons false prova1))).
(* x = T T F F x *)

CoFixpoint prova2: stream bool := Cons true (Cons true (Cons false (Cons false (Cons false prova2)))).
(* x = T T F F F x *)

Definition prova3: stream bool := Cons true (Cons true (Cons false (Cons false always_false))).
(* x = T T F F F^w *)

Definition prova4: stream bool := Cons true (Cons true (Cons false (Cons false always_true))).
(* x = T T F F T^w *)


Definition testprova1 := test 2 prova1.
Definition testprova2 := test 2 prova2.
Definition testprova3 := test 2 prova3.
Definition testprova4 := test 2 prova4.


CoFixpoint example_ET :=
Cons true (Cons false (Cons true (Cons false example_ET))).
(* x = T F T F x *)

CoFixpoint example_EF :=
Cons false (Cons true (Cons false (Cons true example_EF))).
(* x = F T F T x *)

Definition example_ET1 :=
Cons true (Cons false (Cons true (Cons false always_true))).
(* x = T F T F T^w *)

Definition example_EF1 :=
Cons false (Cons true (Cons false (Cons true always_false))).
(* x = F T F T F^w *)

Definition example_ET2 :=
Cons true (Cons false (Cons true (Cons false always_false))).
(* x = T F T F F^w *)

Definition example_EF2 :=
Cons false (Cons true (Cons false (Cons true always_true))).
(* x = F T F T T^w *)

Definition example_ET3 :=
Cons true (Cons false (Cons true (Cons false (Cons true (Cons true (Cons true always_true)))))).
(* x = T F T F T T T T^w *)

Definition example_EF3 :=
Cons true (Cons false (Cons true (Cons false (Cons true (Cons true (Cons true always_false)))))).
(* x = T F T F T T T F^w *)

Definition test_ET  := test 2 example_ET.
Definition test_EF  := test 2 example_EF.
Definition test_ET1 := test 2 example_ET1.
Definition test_EF1 := test 2 example_EF1.
Definition test_ET2 := test 4 example_ET2.
Definition test_EF2 := test 4 example_EF2.
Definition test_ET3 := test 6 example_ET3.
Definition test_EF3 := test 6 example_EF3.


Require Import Extraction.
Set Extraction Output Directory ".".

Extraction Language OCaml.
Extract Constant callcc => "fun c -> shift p (fun k -> k (c (fun x -> abort p (k x))))".
Extract Constant throw => "fun (k : 'a cont) x -> match k x with _ -> .".
Extract Constant wrap => "push_prompt p".
Extraction Inline test wrap.
Extraction "IPP_proof.ml" test1 test2 test3 test4 test5 test6 test7 testprova1 testprova2 testprova3 testprova4 
test_ET test_EF test_ET1  test_EF1 test_ET2 test_EF2 test_ET3 test_EF3.

Extraction Language  Scheme.
Extract Constant callcc => "call/cc".
Extract Constant throw => "(lambda (x) x)".
Extract Constant wrap => "(lambda (f) (f '(Tt)))".
Extraction Inline test.
Extraction "IPP_proof.scm" test1 test2 test3 test4 test5 test6 test7.
