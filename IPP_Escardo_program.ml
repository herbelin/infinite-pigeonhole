
type empty_set = |

type unit0 =
| Tt

type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

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
| Build_ipp_stream of nat * (unit0 -> ipp_stream)

(** val depth : ipp_stream -> nat **)

let depth i =
  let Build_ipp_stream (depth0, _) = Lazy.force i in depth0

(** val rest : ipp_stream -> unit0 -> ipp_stream **)

let rest i =
  let Build_ipp_stream (_, rest0) = Lazy.force i in rest0

(** val coiter : ('a1 -> nat) -> ('a1 -> 'a1) -> 'a1 -> ipp_stream **)

let rec coiter base next s =
  lazy (Build_ipp_stream ((base s), (fun _ -> coiter base next (next s))))

(** val bool_dec' : bool -> bool -> bool **)

let bool_dec' b b' =
  match b with
  | True -> b'
  | False -> (match b' with
              | True -> False
              | False -> True)

(** val infinite_bool : bool stream -> ipp_stream **)

let infinite_bool bs =
  let b0 = head bs in
  callcc (fun start ->
    coiter (fun pat -> let ExistT (depth0, _) = pat in depth0) (fun pat ->
      let ExistT (depth0, rest0) = pat in
      (match bool_dec' (head rest0) b0 with
       | True -> ExistT ((S depth0), (tail rest0))
       | False ->
         callcc (fun restart ->
           throw start
             (coiter projT1 (fun pat0 ->
               let ExistT (depth1, rest1) = pat0 in
               (match bool_dec' (head rest1) b0 with
                | True -> throw restart (ExistT ((S depth1), (tail rest1)))
                | False -> ExistT ((S depth1), (tail rest1)))) (ExistT ((S
               depth0), (tail rest0))))))) (ExistT (O, (tail bs))))

(** val take_ipp : ipp_stream -> nat -> nat list **)

let rec take_ipp s = function
| O -> Nil
| S n' ->
  (match n' with
   | O -> Cons ((depth s), Nil)
   | S _ -> Cons ((depth s), (take_ipp (rest s Tt) n')))

(** val always_true : bool stream **)

let rec always_true =
  lazy (Build_stream (True, always_true))

(** val always_false : bool stream **)

let rec always_false =
  lazy (Build_stream (False, always_false))

(** val test_stream : bool stream **)

let test_stream =
  lazy (Build_stream (True, (lazy (Build_stream (False,
    (lazy (Build_stream (True, (lazy (Build_stream (False,
    (lazy (Build_stream (True, (lazy (Build_stream (True,
    (lazy (Build_stream (False, (lazy (Build_stream (False,
    (lazy (Build_stream (True, (lazy (Build_stream (True,
    always_false)))))))))))))))))))))))))))))

(** val test1 : nat list **)

let test1 =
  push_prompt p (fun _ -> take_ipp (infinite_bool test_stream) (S O))

(** val test2 : nat list **)

let test2 =
  push_prompt p (fun _ -> take_ipp (infinite_bool test_stream) (S (S O)))

(** val test3 : nat list **)

let test3 =
  push_prompt p (fun _ -> take_ipp (infinite_bool test_stream) (S (S (S O))))

(** val test4 : nat list **)

let test4 =
  push_prompt p (fun _ ->
    take_ipp (infinite_bool test_stream) (S (S (S (S O)))))

(** val test5 : nat list **)

let test5 =
  push_prompt p (fun _ ->
    take_ipp (infinite_bool test_stream) (S (S (S (S (S O))))))

(** val test6 : nat list **)

let test6 =
  push_prompt p (fun _ ->
    take_ipp (infinite_bool test_stream) (S (S (S (S (S (S O)))))))

(** val test7 : nat list **)

let test7 =
  push_prompt p (fun _ ->
    take_ipp (infinite_bool test_stream) (S (S (S (S (S (S (S O))))))))

(** val prova1 : bool stream **)

let rec prova1 =
  lazy (Build_stream (True, (lazy (Build_stream (True,
    (lazy (Build_stream (False, (lazy (Build_stream (False, prova1)))))))))))

(** val prova2 : bool stream **)

let rec prova2 =
  lazy (Build_stream (True, (lazy (Build_stream (True,
    (lazy (Build_stream (False, (lazy (Build_stream (False,
    (lazy (Build_stream (False, prova2))))))))))))))

(** val prova3 : bool stream **)

let prova3 =
  lazy (Build_stream (True, (lazy (Build_stream (True,
    (lazy (Build_stream (False, (lazy (Build_stream (False,
    always_false)))))))))))

(** val prova4 : bool stream **)

let prova4 =
  lazy (Build_stream (True, (lazy (Build_stream (True,
    (lazy (Build_stream (False, (lazy (Build_stream (False,
    always_true)))))))))))

(** val testprova1 : nat list **)

let testprova1 =
  push_prompt p (fun _ -> take_ipp (infinite_bool prova1) (S (S O)))

(** val testprova2 : nat list **)

let testprova2 =
  push_prompt p (fun _ -> take_ipp (infinite_bool prova2) (S (S O)))

(** val testprova3 : nat list **)

let testprova3 =
  push_prompt p (fun _ -> take_ipp (infinite_bool prova3) (S (S O)))

(** val testprova4 : nat list **)

let testprova4 =
  push_prompt p (fun _ -> take_ipp (infinite_bool prova4) (S (S O)))

(** val example_ET : bool stream **)

let rec example_ET =
  lazy (Build_stream (True, (lazy (Build_stream (False,
    (lazy (Build_stream (True, (lazy (Build_stream (False,
    example_ET)))))))))))

(** val example_EF : bool stream **)

let rec example_EF =
  lazy (Build_stream (False, (lazy (Build_stream (True,
    (lazy (Build_stream (False, (lazy (Build_stream (True,
    example_EF)))))))))))

(** val example_ET1 : bool stream **)

let example_ET1 =
  lazy (Build_stream (True, (lazy (Build_stream (False,
    (lazy (Build_stream (True, (lazy (Build_stream (False,
    always_true)))))))))))

(** val example_EF1 : bool stream **)

let example_EF1 =
  lazy (Build_stream (False, (lazy (Build_stream (True,
    (lazy (Build_stream (False, (lazy (Build_stream (True,
    always_false)))))))))))

(** val example_ET2 : bool stream **)

let example_ET2 =
  lazy (Build_stream (True, (lazy (Build_stream (False,
    (lazy (Build_stream (True, (lazy (Build_stream (False,
    always_false)))))))))))

(** val example_EF2 : bool stream **)

let example_EF2 =
  lazy (Build_stream (False, (lazy (Build_stream (True,
    (lazy (Build_stream (False, (lazy (Build_stream (True,
    always_true)))))))))))

(** val example_ET3 : bool stream **)

let example_ET3 =
  lazy (Build_stream (True, (lazy (Build_stream (False,
    (lazy (Build_stream (True, (lazy (Build_stream (False,
    (lazy (Build_stream (True, (lazy (Build_stream (True,
    (lazy (Build_stream (True, always_true))))))))))))))))))))

(** val example_EF3 : bool stream **)

let example_EF3 =
  lazy (Build_stream (True, (lazy (Build_stream (False,
    (lazy (Build_stream (True, (lazy (Build_stream (False,
    (lazy (Build_stream (True, (lazy (Build_stream (True,
    (lazy (Build_stream (True, always_false))))))))))))))))))))

(** val test_ET : nat list **)

let test_ET =
  push_prompt p (fun _ -> take_ipp (infinite_bool example_ET) (S (S O)))

(** val test_EF : nat list **)

let test_EF =
  push_prompt p (fun _ -> take_ipp (infinite_bool example_EF) (S (S O)))

(** val test_ET1 : nat list **)

let test_ET1 =
  push_prompt p (fun _ -> take_ipp (infinite_bool example_ET1) (S (S O)))

(** val test_EF1 : nat list **)

let test_EF1 =
  push_prompt p (fun _ -> take_ipp (infinite_bool example_EF1) (S (S O)))

(** val test_ET2 : nat list **)

let test_ET2 =
  push_prompt p (fun _ ->
    take_ipp (infinite_bool example_ET2) (S (S (S (S O)))))

(** val test_EF2 : nat list **)

let test_EF2 =
  push_prompt p (fun _ ->
    take_ipp (infinite_bool example_EF2) (S (S (S (S O)))))

(** val test_ET3 : nat list **)

let test_ET3 =
  push_prompt p (fun _ ->
    take_ipp (infinite_bool example_ET3) (S (S (S (S (S (S O)))))))

(** val test_EF3 : nat list **)

let test_EF3 =
  push_prompt p (fun _ ->
    take_ipp (infinite_bool example_EF3) (S (S (S (S (S (S O)))))))
