open Base

(** Untyped grammar, no semantics *)
module Version0 = struct
  module Expr = struct
    type t =
      | Void : t
      | Eps : t
      | Or : t * t -> t
      | Seq : t * t -> t
      | Fix : (t -> t) -> t
  end

  let nat_grammar : Expr.t =
    let open Expr in
    Fix (fun nat -> Or (Eps, Seq (Eps, nat)))

  let unfold (n : int) (f : Expr.t -> Expr.t) : Expr.t =
    let rec kleene n curr = if n = 0 then curr else kleene (n - 1) (f curr) in
    kleene n Expr.Void

  let nat_5 = unfold 5 (fun nat -> Or (Eps, Seq (Eps, nat)))
end

(** Typed grammar, language semantics & sampling using fair-coin *)
module Version1 = struct
  (* Expr.t is now generic over the type of values it generate *)
  module Expr = struct
    type 'a t =
      | Void : 'a t
      | Eps : 'a -> 'a t
      | Or : 'a t * 'a t -> 'a t
      | Seq : 'a t * 'b t -> ('a * 'b) t
      | Map : ('a -> 'b) * 'a t -> 'b t

    let rec pp : type a. a t Fmt.t =
      let open Fmt in
      fun ppf -> function
        | Void -> string ppf "Void"
        | Eps _ -> pf ppf "@[<hov 2>(Eps _)@]"
        | Or (e1, e2) -> pf ppf "@[<hov 2>(Or %a@ @ %a)@]" pp e1 pp e2
        | Seq (e1, e2) -> pf ppf "@[<hov 2>(Seq@ %a@ %a)@]" pp e1 pp e2
        | Map (_, e) -> pf ppf "@[<hov 2>(Map@ %a)@]" pp e

    let void = Void
    let eps x = Eps x
    let ( + ) x y = Or (x, y)
    let ( * ) x y = Seq (x, y)
    let ( ==> ) x f = Map (f, x)
    let rec unfold f n = if n = 0 then Void else f (unfold f (n - 1))
  end

  type nat = int
  type tree = Leaf | Node of nat * tree * tree

  let rec pp_tree ppf =
    let open Fmt in
    function
    | Leaf -> string ppf "Leaf"
    | Node (x, l, r) ->
        pf ppf "@[<hov 2>(Node %a@ %a@ %a)@]" int x pp_tree l pp_tree r

  let nat_f : nat -> nat Expr.t =
    let open Expr in
    unfold (fun nat ->
        (* base case: generate 0 *)
        eps 0
        + (* inductive case: recursively generate a nat, then add 1 to the result  *)
        (nat ==> fun x -> Int.(x + 1)))

  let nat = nat_f 10

  let tree_f =
    let open Expr in
    unfold (fun tree ->
        (* base case: leaf *)
        eps Leaf
        + (* inductive case: node attached with a nat as data *)
        (nat * tree * tree ==> fun ((x, l), r) -> Node (x, l, r)))

  let tree = tree_f 5

  module Gen = struct
    type 'a domain = 'a list

    let rec denote : type a. a Expr.t -> a domain = function
      | Expr.Void -> []
      | Eps x -> [ x ]
      | Or (e1, e2) -> denote e1 @ denote e2
      | Seq (e1, e2) ->
          let res = denote e1 in
          List.concat_map res ~f:(fun x ->
              List.map (denote e2) ~f:(fun y -> (x, y)))
      | Map (f, e) -> List.map (denote e) ~f
  end

  module Rand = struct
    type rand = bool Sequence.t
    type 'a domain = rand -> ('a * rand) option

    let rec denote : type a. a Expr.t -> a domain = function
      | Expr.Void -> fun _ -> None
      | Eps x -> fun bs -> Some (x, bs)
      | Or (e1, e2) -> (
          fun bs ->
            match Sequence.next bs with
            | None -> assert false
            | Some (b, bs) -> if b then denote e1 bs else denote e2 bs)
      | Seq (e1, e2) -> (
          fun bs ->
            match denote e1 bs with
            | None -> None
            | Some (x, bs) -> (
                match denote e2 bs with
                | None -> None
                | Some (y, bs) -> Some ((x, y), bs)))
      | Map (f, e) -> (
          fun bs ->
            match denote e bs with
            | None -> None
            | Some (x, bs) -> Some (f x, bs))

    let of_seed : int -> rand =
     fun seed ->
      Random.init seed;
      Sequence.unfold ~init:() ~f:(fun () ->
          let b = Random.bool () in
          Some (b, ()))

    let run seed e = denote e (of_seed seed) |> Option.map ~f:fst

    let run_n e n =
      Sequence.take
        (Sequence.unfold ~init:0 ~f:(fun i -> Some (run i e, i + 1))
        |> Sequence.filter_opt)
        n
      |> Sequence.to_list
  end
end

(** Sampling using biased-coin *)
module Version2 = struct
  module Expr = struct
    type annot = int

    type 'a t =
      | Void : 'a t
      | Eps : 'a -> 'a t
      | Or : (annot * 'a t) * (annot * 'a t) -> 'a t
      | Seq : 'a t * 'b t -> ('a * 'b) t
      | Map : ('a -> 'b) * 'a t -> 'b t

    let rec pp : type a. a t Fmt.t =
      let open Fmt in
      fun ppf -> function
        | Void -> string ppf "Void"
        | Eps _ -> pf ppf "@[<hov 2>(Eps _)@]"
        | Or ((w1, e1), (w2, e2)) ->
            pf ppf "@[<hov 2>(Or <%d@ %a>@ <%d@ %a>)@]" w1 pp e1 w2 pp e2
        | Seq (e1, e2) -> pf ppf "@[<hov 2>(Seq@ %a@ %a)@]" pp e1 pp e2
        | Map (_, e) -> pf ppf "@[<hov 2>(Map@ %a)@]" pp e

    let void = Void
    let eps x = Eps x
    let ( + ) x y = Or (x, y)
    let ( * ) x y = Seq (x, y)
    let ( ==> ) x f = Map (f, x)
    let rec unfold f n = if n = 0 then Void else f (unfold f (n - 1))
  end

  type nat = int
  type tree = Leaf | Node of nat * tree * tree

  let rec pp_tree ppf =
    let open Fmt in
    function
    | Leaf -> string ppf "Leaf"
    | Node (x, l, r) ->
        pf ppf "@[<hov 2>(Node %a@ %a@ %a)@]" int x pp_tree l pp_tree r

  let nat_f : nat -> nat Expr.t =
    let open Expr in
    unfold (fun nat ->
        (* base case: generate 0 *)
        (1, eps 0)
        + (* inductive case: recursively generate a nat, then add 1 to the result  *)
        (3, nat ==> fun x -> Int.(x + 1)))

  let nat = nat_f 10

  let tree_f =
    let open Expr in
    unfold (fun tree ->
        (1, eps Leaf)
        + (3, nat * tree * tree ==> fun ((x, l), r) -> Node (x, l, r)))

  let tree = tree_f 5
  let num_bits n = Int.ceil_log2 n

  let bits_to_int bs =
    List.fold bs ~init:0 ~f:(fun acc b -> (acc lsl 1) + if b then 1 else 0)

  let rec flip_biased (w1, w2) bs =
    let w = w1 + w2 in
    let bs, rest = Sequence.split_n bs (num_bits w) in
    let n = bits_to_int bs in
    if n < w1 then (true, rest)
    else if n < w then (false, rest)
    else flip_biased (w1, w2) rest

  module Rand = struct
    type rand = bool Sequence.t
    type 'a t = rand -> ('a * rand) option

    let rec denote : type a. a Expr.t -> a t =
     fun e bs ->
      match e with
      | Expr.Void -> None
      | Eps x -> Some (x, bs)
      | Or ((w1, e1), (w2, e2)) ->
          let b, bs = flip_biased (w1, w2) bs in
          if b then denote e1 bs else denote e2 bs
      | Seq (e1, e2) ->
          Option.bind (denote e1 bs) ~f:(fun (x, bs) ->
              Option.bind (denote e2 bs) ~f:(fun (y, bs) -> Some ((x, y), bs)))
      | Map (f, e) -> Option.map (denote e bs) ~f:(fun (x, bs) -> (f x, bs))

    let of_seed : int -> rand =
     fun seed ->
      Random.init seed;
      Sequence.unfold ~init:() ~f:(fun () ->
          let b = Random.bool () in
          Some (b, ()))

    let run seed e = denote e (of_seed seed) |> Option.map ~f:fst

    let run_n e n =
      Sequence.take
        (Sequence.unfold ~init:0 ~f:(fun i -> Some (run i e, i + 1))
        |> Sequence.filter_opt)
        n
      |> Sequence.to_list
  end
end

module Expr = struct
  type annot = string * int

  type 'a t =
    | Void : 'a t
    | Eps : 'a -> 'a t
    | Or : (annot * 'a t) * (annot * 'a t) -> 'a t
    | Seq : 'a t * 'b t -> ('a * 'b) t
    | Map : ('a -> 'b) * 'a t -> 'b t

  let rec pp : type a. a t Fmt.t =
    let open Fmt in
    fun ppf -> function
      | Void -> string ppf "Void"
      | Eps _ -> pf ppf "@[<hov 2>(Eps _)@]"
      | Or (((l1, _), e1), ((l2, _), e2)) ->
          pf ppf "@[<hov 2>(Or <%s@ %a>@ <%s@ %a>)@]" l1 pp e1 l2 pp e2
      | Seq (e1, e2) -> pf ppf "@[<hov 2>(Seq@ %a@ %a)@]" pp e1 pp e2
      | Map (_, e) -> pf ppf "@[<hov 2>(Map@ %a)@]" pp e

  let void = Void
  let eps x = Eps x
  let ( + ) x y = Or (x, y)
  let ( * ) x y = Seq (x, y)
  let ( ==> ) x f = Map (f, x)
  let rec unfold f n = if n = 0 then Void else f (unfold f (n - 1))
end

type nat = int
type tree = Leaf | Node of nat * tree * tree

let rec pp_tree ppf =
  let open Fmt in
  function
  | Leaf -> string ppf "Leaf"
  | Node (x, l, r) ->
      pf ppf "@[<hov 2>(Node %a@ %a@ %a)@]" int x pp_tree l pp_tree r

let nat_f : int -> nat Expr.t =
  let open Expr in
  unfold (fun nat : nat t ->
      (("Z", 1), eps 0) + (("S", 2), nat ==> fun x -> Int.(x + 1)))

let nat = nat_f 10

let tree_f =
  let open Expr in
  unfold (fun tree ->
      (("l", 1), eps Leaf)
      + (("n", 3), nat * tree * tree ==> fun ((x, l), r) -> Node (x, l, r)))

let tree = tree_f 5

module Trace = struct
  type label = string
  type labels = label list
  type 'a domain = labels -> ('a * labels) list

  let rec denote : type a. a Expr.t -> a domain =
   fun e ts ->
    match e with
    | Expr.Void -> []
    | Eps x -> [ (x, ts) ]
    | Or (((l1, _), e1), ((l2, _), e2)) -> (
        match ts with
        | [] -> []
        | t :: ts ->
            if String.equal t l1 then denote e1 ts
            else if String.equal t l2 then denote e2 ts
            else [])
    | Seq (e1, e2) ->
        let res = denote e1 ts in
        List.concat_map res ~f:(fun (x, ts) ->
            denote e2 ts |> List.map ~f:(fun (y, ts) -> ((x, y), ts)))
    | Map (f, e) -> denote e ts |> List.map ~f:(fun (x, ts) -> (f x, ts))
end

module Gen = struct
  type 'a t = 'a list

  let rec denote : type a. a Expr.t -> a t = function
    | Expr.Void -> []
    | Eps x -> [ x ]
    | Or ((_, e1), (_, e2)) -> denote e1 @ denote e2
    | Seq (e1, e2) ->
        let res = denote e1 in
        List.concat_map res ~f:(fun x ->
            List.map (denote e2) ~f:(fun y -> (x, y)))
    | Map (f, e) -> List.map (denote e) ~f
end

(* module Reflect = struct
     type 'a t = 'a -> ('a * string list) list

     let rec denote : type a. a Expr.t -> a t = function
       | Expr.Void -> fun _ -> []
       | Eps x -> fun _ -> [ (x, []) ]
       | Or (((l1, _), e1), ((l2, _), e2)) ->
           fun x ->
             let r1 = denote e1 x in
             let r2 = denote e2 x in
             List.map ~f:(fun (y, ts) -> (y, l1 :: ts)) r1
             @ List.map ~f:(fun (y, ts) -> (y, l2 :: ts)) r2
       | Seq (e1, e2) ->
           fun x ->
             let r1 = denote e1 x in
             List.concat_map r1 ~f:(fun (y, ts) ->
                 let r2 = denote e2 y in
                 List.map r2 ~f:(fun (z, ts') -> (z, ts @ ts')))
       | Map (_, g, e) -> (
           fun x -> match g x with None -> [] | Some y -> denote e y)
   end *)
