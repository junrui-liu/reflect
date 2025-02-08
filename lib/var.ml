open Base

module type T1 = sig
  type 'a t
end

(** Iteraction tree (minus silent nodes) *)
module ITree (E : T1) = struct
  type _ t = Leaf : 'r -> 'r t | Node : 'a E.t * ('a -> 'r t) -> 'r t

  let leaf x = Leaf x
  let node x f = Node (x, f)

  module Monad = struct
    let return = leaf

    (** Graft a continuation onto every leaf node *)
    let rec bind : type a b. a t -> (a -> b t) -> b t = function
      | Leaf x -> fun k -> k x
      | Node (e, k) -> fun k' -> Node (e, fun x -> bind (k x) k')

    let ( >>= ) = bind
  end
end

module type Handler = functor (T : T1) (Event : T1) -> sig
  type 'r handler = { self : 'a. 'a Event.t -> ('a -> 'r T.t) -> 'r T.t }
end

(** An effect defines what to do in the leaf case (via return) and in the node case (via handler) *)
module type EFF = functor (Event : T1) -> sig
  type 'a t

  val return : 'a -> 'a t

  type 'r handler = { self : 'a. 'a Event.t -> ('a -> 'r t) -> 'r t }

  val handler : 'a handler
end

(** Fold over a tree using an effect *)
module Interpret (Event : T1) (F : EFF) = struct
  module Eff = F (Event)

  let rec run : type a. a ITree(Event).t -> a Eff.t = function
    | Leaf v -> Eff.return v
    | Node (e, k) -> Eff.handler.self e (fun x -> run (k x))
end

module VarE (Dom : T) = struct
  type _ t = Get : string -> Dom.t t
end

module VarH (Dom : T) = struct
  type _ env = Dom.t Map.M(String).t
  type 'a t = Dom.t env -> 'a

  let return (v : 'a) : 'a t = fun _ -> v

  type 'r handler = { self : 'a. 'a VarE(Dom).t -> ('a -> 'r t) -> 'r t }

  let h : type a r. a VarE(Dom).t -> (a -> r t) -> r t = function
    | Get x ->
        fun (k : Dom.t -> r t) env ->
          let v = Map.find_exn env x in
          k v env

  let handler : 'r handler = { self = h }
end

module IntVar = VarE (Int)
module Env = Interpret (IntVar)

module Expr = struct
  type binop = Add | Sub | Mul
  type t = Var of string | Nat of int | Binop of binop * t * t
end

(** Abstract domain *)
module type DOM = sig
  type t
  (** Value domain *)

  val nat : int -> t
  (** Interpret nat into domain *)

  val binop : Expr.binop -> t -> t -> t
  (** Interpret binop into binary operator on domain *)
end

(** Free interpretation of expr as interaction trees, parameterized by an interpretation of nat and binop *)
module EvalFree (D : DOM) = struct
  open Expr
  module E = VarE (D)
  module H = VarH (D)
  module Tree = ITree (E)

  let rec lift2 : binop -> D.t Tree.t -> D.t Tree.t -> D.t Tree.t =
   fun op t1 t2 ->
    match (t1, t2) with
    | Leaf m, Leaf n -> Leaf (D.binop op m n)
    | Node (e, k), _ -> Node (e, fun m -> lift2 op (k m) t2)
    | _, Node (e, k) -> Node (e, fun m -> lift2 op (k m) t1)

  let rec eval : t -> D.t Tree.t = function
    | Var x -> Tree.node (E.Get x) Tree.leaf
    | Nat n -> Tree.leaf (D.nat n)
    | Binop (op, e1, e2) -> lift2 op (eval e1) (eval e2)
end

module Nat = struct
  type t = int

  let nat n = n
  let binop = function Expr.Add -> ( + ) | Sub -> ( - ) | Mul -> ( * )
end

module EvalInt = EvalFree (Nat)
