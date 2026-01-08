(** Computing the Infinite Pigeonhole Principle with corecursion and control *)
(** For a given stream of Boolean values, this implementation classically
    returns either a stream of all "true" or a stream of all "false";
    that is, observationally, it returns as long as needed approximations
    of the corresponding infinite outputs (possibly backtracking on the way) *)

Require Import List.
Require Import Bool.
Import ListNotations.

(** Axiomatization of control *)
Definition cont A := A -> Empty_set.
Parameter callcc : forall {A}, (cont A -> A) -> A.
Parameter throw : forall {A B}, cont A -> A -> B.

(** Notations for dependent pairs *)
Notation "( x ; y ; .. ; z )" := (existT _ .. (existT _ x y) .. z) (at level 0, format "'[' ( x ;  '/ ' y ;  '/ ' .. ;  '/ ' z ) ']'").
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").

(** General streams *)
CoInductive stream A := { head : A; tail : stream A }.

Arguments head {A}.
Arguments tail {A}.

(* CoInductive definition of streams *)
CoInductive ipp_stream : Type := { depth : nat; rest : unit -> ipp_stream }. (* delay explicitly, since extraction does not do it *)

Definition coiter X (base : X -> nat) (next : X -> X) :=
 cofix f s : ipp_stream := {| depth := base s;
                              rest  := fun _ => f (next s)
                            |}.

Definition corecM X (base : X -> nat) (next : X -> ipp_stream + X) :=
  cofix f s : ipp_stream :=
     {| depth := base s;
        rest  := fun _ => match next s with
                            | inl s => s
                            | inr x => f x
                           end
      |}.

Definition corecC X  (base : X -> nat) (next : X -> cont ipp_stream -> X) :=
  corecM X base (fun s =>
     callcc (fun disjret => inr (next s (fun ret => disjret (inl ret))))).

Definition bool_dec b b' : bool :=
  match b, b' with
  | true, true | false, false => true
  | true, false | false, true => false
  end.

(* Core of the program *)
Definition infinite_bool (bs : stream bool) : ipp_stream :=
 let b0 := head bs in
  callcc (fun start : cont ipp_stream =>
   coiter
   {ns : { n : nat & stream bool } & cont ipp_stream}
   (fun '(depth; _; _) => depth)
   (fun '(depth; rest; switch) =>
         if bool_dec (head rest) b0
          then (S depth; tail rest; switch)
          else callcc (fun restart => throw switch
     (corecC
     {n : nat & stream bool}
     (fun st => st.1)
     (fun '(depth; rest) ret =>
           if bool_dec (head rest) b0
            then throw restart (S depth; tail rest; ret)
            else (S depth; tail rest)
      )
      (S depth; tail rest)))
    )
   (0; tail bs; start)).

(** Examples *)

(* Take first n elements of an ipp_stream as a list *)
Fixpoint take_ipp (s : ipp_stream) (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => (depth s) :: take_ipp (rest s tt) n'
  end.

Notation Cons hd tl := {| head := hd; tail := tl |}.

Axiom wrap : forall {A}, (unit -> A) -> A.
Definition test n s := wrap (fun _ => take_ipp (infinite_bool s) n).

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


Require Import Extraction ExtrOcamlBasic.
Set Extraction Output Directory ".".

Extraction Language OCaml.
Extract Constant callcc => "fun c -> shift p (fun k -> k (c (fun x -> abort p (k x))))".
Extract Constant throw => "fun (k : 'a cont) x -> match k x with _ -> .".
Extract Constant wrap => "push_prompt p".
Extraction Inline test wrap.
Extraction "IPP_program.ml" test1 test2 test3 test4 test5 test6 test7 testprova1 testprova2 testprova3 testprova4 
test_ET test_EF test_ET1  test_EF1 test_ET2 test_EF2 test_ET3 test_EF3.

Extraction Language Scheme.
Extract Constant callcc => "call/cc".
Extract Constant throw => "(lambda (x) x)".
Extract Constant wrap => "(lambda (f) (f '(Tt)))".
Extraction Inline test.
Extraction "IPP_program.scm" test1 test2 test3 test4 test5 test6 test7 testprova1 testprova2 testprova3 testprova4.
