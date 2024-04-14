open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser
       
let rec chk_expr : expr -> texpr tea_result = function 
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     chk_expr body >>= fun t ->
     if t=tRes 
     then chk_expr target
     else error
         "LetRec: Type of recursive function does not match
declaration")
 (* | Record([]) ->
    error "record: empty record"
  | Record(fs) ->
    let (ids, bes) = List.split fs
    in let (bs,es) = List.split bes
    in if List.length (List.sort_uniq compare ids) = List.length ids
    then chk_exprs es >>= fun tes ->
      return (RecordType (List.combine ids tes))
    else error "record: duplicate fields"
  | Proj(e,id) ->
    chk_expr e >>= fun te ->
    (match te with
    | RecordType tfs ->
      (match List.assoc_opt id tfs with
      | Some t -> return t
      | None -> error "proj: field does not exist")
    | _ -> error "proj: target not a record")
*)
  | NewRef(e) ->
    chk_expr e >>= fun te ->
    return (RefType te)
  | DeRef(e) -> 
    chk_expr e >>= fun te ->
    (match te with
    | (RefType q) -> return q
    | _ -> error "deref: Expected a reference type")
  | SetRef(e1, e2) ->
    chk_expr e1 >>= fun te ->
    chk_expr e2 >>= fun _ ->
    (match te with
    | (RefType _) -> return UnitType
    | _ -> error "setref: Expected a reference type")
  | BeginEnd([]) ->
    return UnitType
  | BeginEnd(es) ->
    let r = List.rev es
    in let h = List.hd r
    in chk_expr h >>= fun te ->
    return te
  | EmptyList(t) ->
    (match t with
    | Some x -> return (ListType x)
    | _ -> error "emptylist: not a valid type")
  | Cons(e1, e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    (match t2 with
    | (ListType x) -> if (x=t1) then return (ListType t1) else error "cons: type of head and tail do not match"
    | _ -> error "cons: invalid type")
  | IsEmpty(e) ->
    chk_expr e >>= fun te ->
    (match te with
    | (ListType _) -> return BoolType
    | (TreeType _) -> return BoolType
    | _ -> error "isempty: not a valid type")
  | Hd(e) -> 
    chk_expr e >>= fun te ->
    (match te with
    | (ListType x) -> return x
    | _ -> error "hd: invalid argument")
  | Tl(e) ->
    chk_expr e >>= fun te ->
    return te
  | EmptyTree(t) ->
    (match t with
    | Some x -> return (TreeType x)
    | _ -> error "emptytree: not a valid type")
  | Node(de, le, re) ->
    chk_expr de >>= fun v ->
    chk_expr le >>= fun l ->
    chk_expr re >>= fun r ->
    (match l, r with
    | (TreeType x), (TreeType y) -> if (x=y) && (x=v) then return (TreeType v) else error "node: types not matched"
    | _ -> error "node: invalid argument")
  | CaseT(target, emptycase, id1, id2, id3, nodecase) ->
    chk_expr target >>= fun t ->
    extend_tenv id1 t >>+
    extend_tenv id2 t >>+
    extend_tenv id3 t >>+
    (match t with 
    | (TreeType _) ->
      chk_expr emptycase >>= fun ec ->
      chk_expr nodecase >>= fun nc ->
      if (ec!=nc) then return nc else error "caset: cases have different types"
    | _ -> error "caset: target not a tree")

  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint"
  | _ -> failwith "chk_expr: implement"    
and
  chk_prog (AProg(_,e)) =
  chk_expr e
and
  chk_exprs es =
    match es with
    | [] -> return []
    | h::t ->
      chk_expr h >>= fun th ->
      chk_exprs t >>= fun l ->
      return (th::l)

(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr t)



