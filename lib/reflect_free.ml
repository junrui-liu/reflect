open Base

module Expr = struct
  type annot = string * int

  type ('b, 'a) t =
    | Void : ('a, 'a) t
    | Eps : 'a -> ('a, 'a) t
    | Or : (annot * ('b, 'a) t) * (annot * ('b, 'a) t) -> ('b, 'a) t
    | Seq : ('b1, 'a1) t * ('b2, 'a2) t -> ('b1 * 'b2, 'a1 * 'a2) t
    | Map : ('a1 -> 'a2) * ('b2 -> 'b1 option) * ('b1, 'a1) t -> ('b2, 'a2) t

  type 'a r = ('a, 'a) t

  let rec pp : type a b. (b, a) t Fmt.t =
    let open Fmt in
    fun ppf -> function
      | Void -> string ppf "Void"
      | Eps _ -> pf ppf "@[<hov 2>(Eps _)@]"
      | Or (((l1, _), e1), ((l2, _), e2)) ->
          pf ppf "@[<hov 2>(Or @[ <%s %a>@  <%s %a>@])@]" l1 pp e1 l2 pp e2
      | Seq (e1, e2) -> pf ppf "@[<hov 2>(Seq@ %a@ %a)@]" pp e1 pp e2
      | Map (_, _, e) -> pf ppf "@[<hov 2>(Map@ %a)@]" pp e

  let void = Void
  let eps x = Eps x

  let exact equal x =
    Map (Fn.id, (fun y -> if equal x y then Some x else None), Eps x)

  let ( + ) x y = Or (x, y)
  let ( * ) x y = Seq (x, y)
  let ( ==> ) x (f, g) = Map (f, g, x)
  let rec unfold f n = if n = 0 then Void else f (unfold f (n - 1))
end

type nat = Z | S of nat [@@deriving equal]

let rec nat_to_int = function Z -> 0 | S n -> 1 + nat_to_int n
let pp_nat = Fmt.using nat_to_int Fmt.int

type tree = Leaf | Node of nat * tree * tree [@@deriving equal]

let rec pp_tree ppf =
  let open Fmt in
  function
  | Leaf -> string ppf "Leaf"
  | Node (x, l, r) ->
      pf ppf "@[<hov 2>(Node %a@ %a@ %a)@]" pp_nat x pp_tree l pp_tree r

let nat_f =
  let open Expr in
  unfold (fun nat ->
      (("Z", 1), exact equal_nat Z)
      + ( ("S", 2),
          nat ==> ((fun x -> S x), function S x -> Some x | _ -> None) ))

let nat = nat_f 10

let tree_f nat =
  let open Expr in
  unfold (fun tree ->
      (("l", 1), exact equal_tree Leaf)
      + ( ("n", 3),
          nat * tree * tree
          ==> ( (fun ((x, l), r) -> Node (x, l, r)),
                function Node (x, l, r) -> Some ((x, l), r) | _ -> None ) ))

let tree = tree_f nat 5

module Parser = struct
  type tokens = string list
  type 'a t = tokens -> ('a * tokens) list

  let rec denote : type a b. (b, a) Expr.t -> a t =
   fun e ->
    Logs.debug (fun m -> m "Denote: %a\n" Expr.pp e);
    fun ts ->
      Logs.debug (fun m -> m "Tokens: %a\n" Fmt.(list string) ts);
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
      | Map (f, _, e) -> denote e ts |> List.map ~f:(fun (x, ts) -> (f x, ts))
end

module Rand = struct
  type rand = bool Sequence.t
  type 'a t = rand -> ('a * rand) option

  let rec denote : type a b. (b, a) Expr.t -> a t = function
    | Expr.Void -> fun _ -> None
    | Eps x -> fun bs -> Some (x, bs)
    | Or ((_, e1), (_, e2)) -> (
        fun bs ->
          match Sequence.next bs with
          | None -> assert false
          | Some (b, bs) -> if b then denote e1 bs else denote e2 bs)
    | Seq (e1, e2) ->
        fun bs ->
          Option.bind (denote e1 bs) ~f:(fun (x, bs) ->
              Option.bind (denote e2 bs) ~f:(fun (y, bs) -> Some ((x, y), bs)))
    | Map (f, _, e) ->
        fun bs -> Option.map (denote e bs) ~f:(fun (x, bs) -> (f x, bs))

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

module Gen = struct
  type 'a t = 'a list

  let rec denote : type a b. (b, a) Expr.t -> a t = function
    | Expr.Void -> []
    | Eps x -> [ x ]
    | Or ((_, e1), (_, e2)) -> denote e1 @ denote e2
    | Seq (e1, e2) ->
        let res = denote e1 in
        List.concat_map res ~f:(fun x ->
            List.map (denote e2) ~f:(fun y -> (x, y)))
    | Map (f, _, e) -> List.map (denote e) ~f
end

module ReflectRandom = struct
  type 'a t = 'a -> ('a * bool list) list

  let ( @@@ ) f x = f x

  let rec denote : type a b. (b, a) Expr.t -> b -> (a * bool list) list =
   fun (type b a) (e : (b, a) Expr.t) (x : b) : (a * bool list) list ->
    let r : (a * bool list) list =
      match e with
      | Expr.Void -> []
      | Eps x -> [ (x, []) ]
      | Or ((_, e1), (_, e2)) ->
          let r1 = denote e1 x in
          let r2 = denote e2 x in
          List.map ~f:(fun (y, ts) -> (y, true :: ts)) r1
          @ List.map ~f:(fun (y, ts) -> (y, false :: ts)) r2
      | Seq (e1, e2) ->
          let x, y = x in
          let r1 = denote e1 x in
          let r2 = denote e2 y in
          List.concat_map r1 ~f:(fun (x, ts1) ->
              List.map r2 ~f:(fun (y, ts2) -> ((x, y), ts1 @ ts2)))
      | Map (f, g, e) -> (
          match g x with
          | None -> []
          | Some y ->
              let r = denote e y in
              List.map r ~f:(fun (y, ts) -> (f y, ts)))
    in
    r

  let run e x = denote e x |> List.map ~f:snd
end

let () =
  Logs.set_level (Some Logs.Debug);
  Logs.set_reporter (Logs_fmt.reporter ())

module ReflectTrace = struct
  type 'a t = 'a -> ('a * string list) list

  let ( @@@ ) f x = f x

  let rec denote : type a b. (b, a) Expr.t -> b -> (a * string list) list =
   fun (type b a) (e : (b, a) Expr.t) (x : b) : (a * string list) list ->
    let r : (a * string list) list =
      match e with
      | Expr.Void -> []
      | Eps x -> [ (x, []) ]
      | Or (((l1, _), e1), ((l2, _), e2)) ->
          let r1 = denote e1 x in
          let r2 = denote e2 x in
          List.map ~f:(fun (y, ts) -> (y, l1 :: ts)) r1
          @ List.map ~f:(fun (y, ts) -> (y, l2 :: ts)) r2
      | Seq (e1, e2) ->
          let x, y = x in
          let r1 = denote e1 x in
          let r2 = denote e2 y in
          List.concat_map r1 ~f:(fun (x, ts1) ->
              List.map r2 ~f:(fun (y, ts2) -> ((x, y), ts1 @ ts2)))
      | Map (f, g, e) -> (
          match g x with
          | None -> []
          | Some y ->
              let r = denote e y in
              List.map r ~f:(fun (y, ts) -> (f y, ts)))
    in
    Logs.debug (fun m ->
        m "Denote %a = %a" Expr.pp e
          Fmt.(list (brackets @@ list string))
          (List.map ~f:snd r));
    r

  let run e x = denote e x |> List.map ~f:snd
end

let () =
  Logs.set_level (Some Logs.Debug);
  Logs.set_reporter (Logs_fmt.reporter ())
