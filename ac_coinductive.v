(** A coinductive proof with control of the axiom of countable choice *)

(** Classical logic, in Prop and Type, relatively to a final toplevel type R *)

Definition cont A := A -> False.
Parameter callccP : forall {A:Prop}, (cont A -> A) -> A.
Parameter callccT : forall {A:Type}, (cont A -> A) -> A.
Parameter throwT : forall {A B:Type}, cont A -> A -> B.

(** Miscellaneous notations *)

Import EqNotations.

Notation "( x ; .. ; y ; z )" := (existT _ x .. (existT _ y z) ..) (at level 0, format "'[' ( x ;  '/ ' .. ;  '/ ' y ;  '/ ' z ) ']'").
Notation "( x 'as' z 'in' T ; y 'in' P )" := (existT (fun z: T => P%type) x y)
  (at level 0, only parsing).
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").

(** Stream representation of countable Pi-types *)

CoInductive stream A n : Type := Cons { hd : A n ; tl : stream A (S n) }.

Arguments hd {A n}.
Arguments tl {A n}.
Arguments Cons {A n}.

Definition coiter {A} (X:nat->Type) (mkhd : forall n, X n -> A n) (mktl : forall n, X n -> X (S n)) :=
  cofix f n (s : X n) : stream A n := {| hd := mkhd n s; tl := f (S n) (mktl n s) |}.

Definition comatch {A n} (mkhd : A n) (mktl : stream A (S n)) :=
  cofix f : stream A n := {| hd := mkhd; tl := mktl |}.

Fixpoint nth {A n} i (s : stream A n) : A (n + i) :=
  match i return A (n + i) with
  | 0 => rew plus_n_O n in s.(hd)
  | S i => rew plus_n_Sm n i in nth i s.(tl)
  end.

Definition stream_of_function {A} (f : forall n, A n) : stream A 0 :=
  (cofix s n : stream A n := {| hd := f n; tl := s (S n) |}) 0.

Definition function_of_stream {A} (s : stream A 0) : forall n, A n :=
   fun n => nth n s.

(** Propositional truncation *)

Inductive trunc A : Prop := Trunc : A -> trunc A.

Arguments Trunc {A}.
Notation "|| A ||" := (trunc A) (at level 11, A at level 10).
Notation "| A |" := (Trunc A) (at level 11, A at level 10).

Definition under {A B} f (p : ||A||) : ||B|| :=
  match p with
  | Trunc x => Trunc (f x)
  end.

(** A variant of DNS: shift of truncation through streams *)

Definition DNS_trunc' A p : stream (fun n => || A n ||) p -> || stream A p || :=
  fun s =>
  callccP (fun k : cont (|| stream A p ||) =>
  let '|a| := s.(hd) in
  |coiter (fun n => (A n * stream (fun n => || A n ||) (S n) * cont (|| stream A n ||))%type)
        (fun n '(a,_,_) => a)
        (fun n '(a,s,k) => callccT (fun ks : cont (A (S n) * _ * _) =>
            throwT k
             ((let '(|a'|) := s.(hd) in throwT ks
                 ((a',s.(tl),fun s => k (let '|s| := s in |comatch a s|))
                  : (A (S n) * _ * _ ) %type))
              : || _ ||)))
        p (a,s.(tl),k)|).

Definition DNS_trunc A := DNS_trunc' A 0.

(** Countable choice from truncation shift *)

Definition ACw A R (H : forall n, || { a : A & R n a } ||) : || { f : nat -> A & forall n, R n (f n) } || :=
  let s := stream_of_function H in
  let '|s| := DNS_trunc (fun i => { a & R i a }) s in
  let H : forall n, { a : A & R n a } := function_of_stream s in
  |(fun i => (H i).1 as f in _;
    fun i => (H i).2 in forall n, R n (f n))|.

(** Tests *)

Definition true := Trunc true.
Definition false := Trunc false.

CoFixpoint always_false n : stream (fun _ => ||bool||) n := Cons false (always_false (S n)).

Definition test_stream :=
Cons true (Cons false (Cons true (Cons false (Cons true (Cons true (Cons false (Cons false
(Cons true (Cons true (always_false 10)))))))))).

Definition test0 := under (nth 0) (DNS_trunc _ test_stream).
Definition test1 := under (nth 1) (DNS_trunc _ test_stream).
Definition test2 := under (nth 2) (DNS_trunc _ test_stream).
Definition test3 := under (nth 3) (DNS_trunc _ test_stream).

