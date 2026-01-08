
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type empty_set = |

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b



type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a


open Delimcc
let p = (new_prompt () : _ prompt)

type 'a cont = 'a -> empty_set

(** val callcc : ('a1 cont -> 'a1) -> 'a1 **)

let callcc = fun c -> shift p (fun k -> k (c (fun x -> abort p (k x))))

(** val throw : 'a1 cont -> 'a1 -> 'a2 **)

let throw = fun (k : 'a cont) x -> match k x with _ -> .

type 'p sigP = 'p
  (* singleton inductive, whose constructor was existP *)

type 'a stream = 'a __stream Lazy.t
and 'a __stream =
| Build_stream of 'a * 'a stream

(** val head : 'a1 stream -> 'a1 **)

let head s =
  let Build_stream (head0, _) = Lazy.force s in head0

(** val tail : 'a1 stream -> 'a1 stream **)

let tail s =
  let Build_stream (_, tail0) = Lazy.force s in tail0

type ipp_stream = __ipp_stream Lazy.t
and __ipp_stream =
| Build_ipp_stream of nat * (unit -> ipp_stream)

(** val depth : ipp_stream -> nat **)

let depth i =
  let Build_ipp_stream (depth0, _) = Lazy.force i in depth0

(** val rest : ipp_stream -> unit -> ipp_stream **)

let rest i =
  let Build_ipp_stream (_, rest0) = Lazy.force i in rest0

(** val coiter :
    (__ -> 'a1 -> nat) -> (__ -> 'a1 -> 'a1) -> 'a1 -> ipp_stream **)

let rec coiter base next s =
  lazy (Build_ipp_stream ((base __ s), (fun _ ->
    coiter base next (next __ s))))

(** val corecM :
    (__ -> 'a1 -> nat) -> (__ -> 'a1 -> (ipp_stream, 'a1) sum) -> 'a1 ->
    ipp_stream **)

let rec corecM base next s =
  lazy (Build_ipp_stream ((base __ s), (fun _ ->
    match next __ s with
    | Inl s0 -> s0
    | Inr x -> corecM base next x)))

(** val corecC :
    (__ -> 'a1 -> nat) -> (__ -> 'a1 -> ipp_stream cont -> 'a1) -> 'a1 ->
    ipp_stream **)

let corecC base next =
  corecM base (fun _ s ->
    callcc (fun disjret -> Inr (next __ s (fun ret -> disjret (Inl ret)))))

(** val bool_dec : bool -> bool -> bool **)

let bool_dec b b' =
  if b then if b' then true else false else if b' then false else true

(** val infinite_bool : bool stream -> ipp_stream **)

let infinite_bool bs =
  let b0 = head bs in
  callcc (fun start ->
    coiter (fun _ pat ->
      let ExistT (x, _) = pat in let ExistT (depth0, _) = x in depth0)
      (fun _ pat ->
      let ExistT (x, s) = pat in
      let ExistT (depth0, rest0) = x in
      if bool_dec (head rest0) b0
      then ExistT ((ExistT ((S depth0), (tail rest0))), s)
      else callcc (fun restart ->
             throw s
               (corecC (fun _ -> projT1) (fun _ pat0 ret ->
                 let ExistT (depth1, rest1) = pat0 in
                 if bool_dec (head rest1) b0
                 then throw restart (ExistT ((ExistT ((S depth1),
                        (tail rest1))), ret))
                 else ExistT ((S depth1), (tail rest1))) (ExistT ((S depth0),
                 (tail rest0)))))) (ExistT ((ExistT (O, (tail bs))), start)))

(** val ipp_stream_depths :
    bool stream -> nat -> nat option -> ipp_stream -> nat list **)

let rec ipp_stream_depths bs k _ ms =
  match k with
  | O -> []
  | S k' ->
    (match k' with
     | O -> (depth ms) :: []
     | S _ ->
       let d = depth ms in
       let ms' = rest ms () in d :: (ipp_stream_depths bs k' (Some d) ms'))

(** val take_ipp : bool stream -> ipp_stream -> nat -> nat list **)

let take_ipp bs ms n =
  ipp_stream_depths bs n None ms

(** val always_true : bool stream **)

let rec always_true =
  lazy (Build_stream (true, always_true))

(** val always_false : bool stream **)

let rec always_false =
  lazy (Build_stream (false, always_false))

(** val test_stream : bool stream **)

let test_stream =
  lazy (Build_stream (true, (lazy (Build_stream (false,
    (lazy (Build_stream (true, (lazy (Build_stream (false,
    (lazy (Build_stream (true, (lazy (Build_stream (true,
    (lazy (Build_stream (false, (lazy (Build_stream (false,
    (lazy (Build_stream (true, (lazy (Build_stream (true,
    always_false)))))))))))))))))))))))))))))

(** val test1 : nat list **)

let test1 =
  push_prompt p (fun _ ->
    take_ipp test_stream (infinite_bool test_stream) (S O))

(** val test2 : nat list **)

let test2 =
  push_prompt p (fun _ ->
    take_ipp test_stream (infinite_bool test_stream) (S (S O)))

(** val test3 : nat list **)

let test3 =
  push_prompt p (fun _ ->
    take_ipp test_stream (infinite_bool test_stream) (S (S (S O))))

(** val test4 : nat list **)

let test4 =
  push_prompt p (fun _ ->
    take_ipp test_stream (infinite_bool test_stream) (S (S (S (S O)))))

(** val test5 : nat list **)

let test5 =
  push_prompt p (fun _ ->
    take_ipp test_stream (infinite_bool test_stream) (S (S (S (S (S O))))))

(** val test6 : nat list **)

let test6 =
  push_prompt p (fun _ ->
    take_ipp test_stream (infinite_bool test_stream) (S (S (S (S (S (S O)))))))

(** val test7 : nat list **)

let test7 =
  push_prompt p (fun _ ->
    take_ipp test_stream (infinite_bool test_stream) (S (S (S (S (S (S (S
      O))))))))

(** val prova1 : bool stream **)

let rec prova1 =
  lazy (Build_stream (true, (lazy (Build_stream (true,
    (lazy (Build_stream (false, (lazy (Build_stream (false, prova1)))))))))))

(** val prova2 : bool stream **)

let rec prova2 =
  lazy (Build_stream (true, (lazy (Build_stream (true,
    (lazy (Build_stream (false, (lazy (Build_stream (false,
    (lazy (Build_stream (false, prova2))))))))))))))

(** val prova3 : bool stream **)

let prova3 =
  lazy (Build_stream (true, (lazy (Build_stream (true,
    (lazy (Build_stream (false, (lazy (Build_stream (false,
    always_false)))))))))))

(** val prova4 : bool stream **)

let prova4 =
  lazy (Build_stream (true, (lazy (Build_stream (true,
    (lazy (Build_stream (false, (lazy (Build_stream (false,
    always_true)))))))))))

(** val testprova1 : nat list **)

let testprova1 =
  push_prompt p (fun _ -> take_ipp prova1 (infinite_bool prova1) (S (S O)))

(** val testprova2 : nat list **)

let testprova2 =
  push_prompt p (fun _ -> take_ipp prova2 (infinite_bool prova2) (S (S O)))

(** val testprova3 : nat list **)

let testprova3 =
  push_prompt p (fun _ -> take_ipp prova3 (infinite_bool prova3) (S (S O)))

(** val testprova4 : nat list **)

let testprova4 =
  push_prompt p (fun _ -> take_ipp prova4 (infinite_bool prova4) (S (S O)))

(** val example_ET : bool stream **)

let rec example_ET =
  lazy (Build_stream (true, (lazy (Build_stream (false,
    (lazy (Build_stream (true, (lazy (Build_stream (false,
    example_ET)))))))))))

(** val example_EF : bool stream **)

let rec example_EF =
  lazy (Build_stream (false, (lazy (Build_stream (true,
    (lazy (Build_stream (false, (lazy (Build_stream (true,
    example_EF)))))))))))

(** val example_ET1 : bool stream **)

let example_ET1 =
  lazy (Build_stream (true, (lazy (Build_stream (false,
    (lazy (Build_stream (true, (lazy (Build_stream (false,
    always_true)))))))))))

(** val example_EF1 : bool stream **)

let example_EF1 =
  lazy (Build_stream (false, (lazy (Build_stream (true,
    (lazy (Build_stream (false, (lazy (Build_stream (true,
    always_false)))))))))))

(** val example_ET2 : bool stream **)

let example_ET2 =
  lazy (Build_stream (true, (lazy (Build_stream (false,
    (lazy (Build_stream (true, (lazy (Build_stream (false,
    always_false)))))))))))

(** val example_EF2 : bool stream **)

let example_EF2 =
  lazy (Build_stream (false, (lazy (Build_stream (true,
    (lazy (Build_stream (false, (lazy (Build_stream (true,
    always_true)))))))))))

(** val example_ET3 : bool stream **)

let example_ET3 =
  lazy (Build_stream (true, (lazy (Build_stream (false,
    (lazy (Build_stream (true, (lazy (Build_stream (false,
    (lazy (Build_stream (true, (lazy (Build_stream (true,
    (lazy (Build_stream (true, always_true))))))))))))))))))))

(** val example_EF3 : bool stream **)

let example_EF3 =
  lazy (Build_stream (true, (lazy (Build_stream (false,
    (lazy (Build_stream (true, (lazy (Build_stream (false,
    (lazy (Build_stream (true, (lazy (Build_stream (true,
    (lazy (Build_stream (true, always_false))))))))))))))))))))

(** val test_ET : nat list **)

let test_ET =
  push_prompt p (fun _ ->
    take_ipp example_ET (infinite_bool example_ET) (S (S O)))

(** val test_EF : nat list **)

let test_EF =
  push_prompt p (fun _ ->
    take_ipp example_EF (infinite_bool example_EF) (S (S O)))

(** val test_ET1 : nat list **)

let test_ET1 =
  push_prompt p (fun _ ->
    take_ipp example_ET1 (infinite_bool example_ET1) (S (S O)))

(** val test_EF1 : nat list **)

let test_EF1 =
  push_prompt p (fun _ ->
    take_ipp example_EF1 (infinite_bool example_EF1) (S (S O)))

(** val test_ET2 : nat list **)

let test_ET2 =
  push_prompt p (fun _ ->
    take_ipp example_ET2 (infinite_bool example_ET2) (S (S (S (S O)))))

(** val test_EF2 : nat list **)

let test_EF2 =
  push_prompt p (fun _ ->
    take_ipp example_EF2 (infinite_bool example_EF2) (S (S (S (S O)))))

(** val test_ET3 : nat list **)

let test_ET3 =
  push_prompt p (fun _ ->
    take_ipp example_ET3 (infinite_bool example_ET3) (S (S (S (S (S (S O)))))))

(** val test_EF3 : nat list **)

let test_EF3 =
  push_prompt p (fun _ ->
    take_ipp example_EF3 (infinite_bool example_EF3) (S (S (S (S (S (S O)))))))
