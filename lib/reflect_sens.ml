open Base

module Expr = struct
  type annot = string * int

  type ('b, 'a) t =
    | Void : ('a, 'a) t
    | Eps : 'a -> ('a, 'a) t
    | Or : (annot * ('b, 'a) t) * (annot * ('b, 'a) t) -> ('b, 'a) t
    | Bind :
        ('b2, 'a1) t * ('a1 -> ('b1, 'a2) t) * ('b1 -> 'b2 option)
        -> ('b1, 'a2) t

  type 'a r = ('a, 'a) t

  let rec pp : type a b. (b, a) t Fmt.t =
    let open Fmt in
    fun ppf -> function
      | Void -> string ppf "Void"
      | Eps _ -> pf ppf "@[<hov 2>(Eps _)@]"
      | Or (((l1, _), e1), ((l2, _), e2)) ->
          pf ppf "@[<hov 2>(Or @[ <%s %a>@  <%s %a>@])@]" l1 pp e1 l2 pp e2
      | Bind (e1, _, _) -> pf ppf "@[<hov 2>(Seq@ %a@ _)@]" pp e1

  module DSL = struct
    let bind x f g = Bind (x, f, g)
    let lmap g f = f g
    let map f x g = bind x (fun x -> Eps (f x)) g

    let exact equal x =
      lmap (fun y -> if equal x y then Some x else None) (map Fn.id (Eps x))

    let ( >>= ) = bind
    let void = Void
    let eps x = Eps x
    let ( ==> ) x f = map f x
    let ( <> ) x y = (x, y)
    let ( + ) x y = Or (x, y)
  end

  let void = Void
  let eps x = Eps x
  let bind x (f, g) = Bind (x, f, g)
  let ( >>= ) = bind
  let map (f, g) x = Bind (x, (fun x -> Eps (f x)), g)

  let exact (equal : 'a -> 'a -> bool) (x : 'a) : ('a, 'a) t =
    let f = Fn.id in
    map (f, fun y -> if equal x y then Some x else None) (Eps x)

  let ( ==> ) x (f, g) = map (f, g) x
  let ( + ) x y = Or (x, y)
  let ( ^ ) x y = (x, y)

  let ( * ) e1 e2 =
    e1
    >>= (fun x -> e2 >>= (fun y -> Eps (x, y)) ^ Fn.compose Option.some snd)
        ^ Fn.compose Option.some fst

  let rec unfold f n = if n = 0 then Void else f (unfold f (n - 1))
end

type tree = Leaf | Node of int * tree * tree [@@deriving equal]

let leaf = Leaf
let node x l r = Node (x, l, r)
let only x = Node (x, Leaf, Leaf)

let rec pp_tree ppf =
  let open Fmt in
  function
  | Leaf -> string ppf "Leaf"
  | Node (x, l, r) ->
      pf ppf "@[<hov 2>(Node %a@ %a@ %a)@]" int x pp_tree l pp_tree r

(* let nat_f =
   let open Expr in
   unfold (fun nat ->
       (("Z", 1), exact equal_nat Z)
       + ( ("S", 2),
           nat ==> ((fun x -> S x), function S x -> Some x | _ -> None) )) *)

let nat_f =
  let open Expr in
  unfold (fun nat ->
      (("natZ", 1), exact Int.equal 0)
      + ( ("natS", 2),
          nat
          ==> (fun x -> Int.(x + 1)) ^ fun x ->
              if x > 0 then Some (x - 1) else None ))

let nat = nat_f 10

let tree_f nat =
  let open Expr in
  unfold (fun tree ->
      (("l", 1), exact equal_tree Leaf)
      + ( ("n", 3),
          nat * tree * tree
          ==> ( (fun ((x, l), r) -> Node (x, l, r)),
                function Node (x, l, r) -> Some ((x, l), r) | _ -> None ) ))

let rec range (lo, hi) =
  let open Expr in
  if lo >= hi then void
  else
    (("rangeZ", 1), exact Int.equal lo)
    + (("rangeS", 1), range (Int.(lo + 1), hi))

let focus_int = function Node (x, _, _) -> Some x | _ -> None
let focus_l = function Node (_, l, _) -> Some l | _ -> None
let focus_r = function Node (_, _, r) -> Some r | _ -> None

let rec bst ((lo, hi) : int * int) : (tree, tree) Expr.t =
  let open Expr in
  if lo >= hi then exact equal_tree Leaf
  else
    (("bstLeaf", 1), exact equal_tree Leaf)
    + ( ("bstNode", 5),
        range (lo, hi)
        >>= (fun i ->
              bst (lo, i)
              >>= (fun l ->
                    bst (Int.(i + 1), hi)
                    >>= (fun r -> eps (Node (i, l, r))) ^ focus_r)
                  ^ focus_l)
            ^ focus_int )

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
      | Bind (e1, f, _) ->
          List.bind (denote e1 ts) ~f:(fun (x, ts) -> denote (f x) ts)
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
    | Bind (e1, f, _) ->
        fun bs -> Option.bind (denote e1 bs) ~f:(fun (x, bs) -> denote (f x) bs)

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
    | Bind (e1, f, _) -> List.bind (denote e1) ~f:(fun x -> denote (f x))
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
      | Bind (e1, f, g) -> (
          match g x with
          | None -> []
          | Some y ->
              let r1 = denote e1 y in
              List.bind r1 ~f:(fun (res, ts1) ->
                  let r2 = denote (f res) x in
                  List.map r2 ~f:(fun (y, ts2) -> (y, ts1 @ ts2))))
    in
    r

  let run e x = denote e x |> List.map ~f:snd
end

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
      | Bind (e1, f, g) -> (
          match g x with
          | None -> []
          | Some y ->
              let r1 = denote e1 y in
              List.bind r1 ~f:(fun (res, ts1) ->
                  let r2 = denote (f res) x in
                  List.map r2 ~f:(fun (y, ts2) -> (y, ts1 @ ts2))))
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

let bst_0_10 = bst (0, 10)
let tree = node 5 (only 3) (node 7 (only 6) (only 9))

let bs =
  Sequence.of_list
    [
      false;
      false;
      false;
      false;
      false;
      false;
      true;
      false;
      false;
      false;
      false;
      true;
      true;
      true;
      false;
      false;
      true;
      false;
      true;
      false;
      false;
      true;
      true;
    ]
