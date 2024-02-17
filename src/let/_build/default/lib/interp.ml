open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds
    
(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return (BoolVal (n = 0))
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return (PairVal(ev1,ev2))
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (l,_) ->
    return l
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (_,r) ->
    return r
  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"
  | EmptyTree(_) -> 
    return (TreeVal Empty)
  | Node(e1,e2,e3) ->
    eval_expr e1 >>= fun v ->
    eval_expr e2 >>= fun ev2 ->
    tree_of_treeVal ev2 >>= fun l ->
    eval_expr e3 >>= fun ev3 ->
    tree_of_treeVal ev3 >>= fun r ->
    return (TreeVal(Node(v, l, r)))
  | IsEmpty(e) ->
    eval_expr e >>= fun ev ->
    tree_of_treeVal ev >>= fun t ->
    return (BoolVal(t = Empty))
  | CaseT(e1, e2, id1, id2, id3, e3) ->
    eval_expr e1 >>= fun case ->
    eval_expr e2 >>= fun ret1 ->
    eval_expr e3 >>= fun ret2 ->
    apply_env id1 >>= fun v ->
    apply_env id2 >>= fun ll ->
    tree_of_treeVal ll >>= fun l ->
    apply_env id3 >>= fun rr ->
    tree_of_treeVal rr >>= fun r ->
    match case with
    | TreeVal Empty -> return ret1
    | TreeVal (Node(v,ll,rr)) -> return ret2





(*

interp "
caseT emptytree() of {
  emptytree() -> emptytree(),
  node(a,l,r) -> l
}";;

*)


  | _ -> failwith "Not implemented yet!"

(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e


(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c
  


