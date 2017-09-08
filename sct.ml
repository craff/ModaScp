open Timed

(** Size change principle. This module implements a decision procedure based
    on the work of Chin Soon Lee, Neil D. Jones and Amir M. Ben-Amram (POPL
    2001). It is used by PML to check that typing and subtyping proofs are
    well-founded. *)

(** Representation of the set {-1, 0, ∞} *)
type cmp = Min1 | Zero | Infi

(** String representation. *)
let cmp_to_string : cmp -> string =
  function Min1 -> "<" | Zero -> "=" | Infi -> "?"

let cprint = fun ff t -> Format.fprintf ff "%s" (cmp_to_string t)

(** Addition operation (minimum) *)
let (<+>) : cmp -> cmp -> cmp = min

(** Multiplication operation. *)
let (<*>) : cmp -> cmp -> cmp = fun e1 e2 ->
  match (e1, e2) with
  | (Infi, _   ) | (_   , Infi) -> Infi
  | (Min1, _   ) | (_   , Min1) -> Min1
  | (Zero, Zero) -> Zero

(** Type of a size change matrix. *)
type matrix = (int * int * cmp) list

(** Transposition. Just sorting column index
    first, do not permutte the indexes themselves *)
let transpose : matrix -> matrix =
  let cmp (i,j,x) (i',j',x) =
    match compare j j' with
    | 0 -> compare i i'
    | c -> c
  in
  List.sort cmp

(** Matrix product. *)
let prod : matrix -> matrix -> matrix = fun m1 m2 ->
  let m2 = transpose m2 in
  let rec fn acc = function
    | [] -> List.rev acc
    | (i,_,_)::_ as m1 ->
       let rec gn acc = function
         | [] -> acc
         | (_,j,_)::_ as m2 ->
            let rec hn c m1 m2 = match m1, m2 with
              | (i',k1,x1)::m1', (k2,j',x2)::m2' when i' = i && j' = j ->
                 begin
                   match compare k1 k2 with
                   | 0 -> hn (c <+> (x1 <*> x2)) m1' m2'
                   | -1 -> hn c m1' m2
                   | _ -> hn c m1 m2'
                 end
              | m1, (k2,j',x2)::m2' when j' = j ->
                 hn c m1 m2'
              | _ -> (c,m2)
            in
            let (c,m2) = hn Infi m1 m2 in
            let acc = if c <> Infi then (i,j,c)::acc else acc in
            gn acc m2
       in
       let acc = gn acc m2 in
       let rec kn = function
         | (i',_,_)::m1 when i' = i -> kn m1
         | m1 -> m1
       in
       fn acc (kn m1)
  in
  fn [] m1

(** Check if a matrix corresponds to a decreasing idempotent call. *)
let decreasing : matrix -> bool = fun m ->
  try
    List.iter (fun (i,j,c) -> if i = j && c = Min1 then raise Exit) m;
    false
  with Exit -> true

(** Check if a matrix subsumes another one (i.e. gives more infomation). *)
let subsumes : matrix -> matrix -> bool = fun m1 m2 ->
  let rec fn m1 m2 = match m1, m2 with
    | (i1,j1,c1)::m1', (i2,j2,c2)::m2' ->
       assert (c1 <> Infi);
       assert (c2 <> Infi);
       begin
         match compare i1 i2 with
         | 0 ->
            begin
              match compare j1 j2 with
              | 0 -> if not (c1 >= c2) then raise Exit; fn m1' m2'
              | -1 -> raise Exit
              | 1 -> fn m1 m2'
              | _ -> assert false
            end
         | -1 -> raise Exit
         | 1 -> fn m1 m2'
         | _ -> assert false
       end
    | [], _ -> ()
    | _, [] -> raise Exit
  in
  try
    fn m1 m2; true
  with Exit -> false

(** Index of a function symbol. *)
type index = int

(** Conversion to int. *)
let int_of_index : index -> int = fun i -> i

(** Index of the root. *)
let root : index = -1

(** Map with indices as keys. *)
module Key =
  struct
    type t = index
    let compare = compare
  end
module IMap = Map.Make(Key)
module ISet = Set.Make(Key)

(** A call [{callee; caller; matrix; is_rec}] represents a call to the
    function symbol with key [callee] by the function symbole with the
    key [caller]. The [matrix] gives the relation between the parameters
    of the caller and the callee. The coefficient [matrix.(a).(b)] give
    the relation between the [a]-th parameter of the caller and the
    [b]-th argument of the callee. The boolean [is_rec] is true when the
    call is a reccursive call (i.e. a call to a generalised hypothesis
    lower in the tree. It is [false] for every call to subtyping in the
    typing algorithm and the same goes for rules introducing a new
    induction hypothesis. Every other call refers to a previously
    introduced induction hypothesis and its boolean is [true]. *)
type call =
  { callee : index  (** Key of the function symbol being called. *)
  ; caller : index  (** Key of the calling function symbol. *)
  ; matrix : matrix (** Size change matrix of the call. *) }

(** Representation of a function symbol. *)
type symbol =
  { index : index        (** Index for use in a [call]. *)
  ; name  : string       (** Name of the symbol. *)
  ; arity : int          (** Arity of the symbol (number of args). *)
  ; args  : string array (** Name of the arguments. *) }

(** Internal state of the SCT, including the representation of symbols and
    the call graph. *)
type call_graph =
  { next_index : index ref
  ; symbols    : symbol IMap.t ref
  ; calls      : call list ref
  ; loop_nodes : ISet.t ref
  ; tbl        : (int, matrix list) TimedHashtbl.t array ref }

(** Synonym of [call_graph]. *)
type t = call_graph

(** Creation of a new initial [call_graph]. It contains the initial root
    symbol. *)
let create : unit -> t =
  let root = { index = -1 ; name  = "R" ; arity = 0 ; args  = [||] } in
  let syms = IMap.singleton (-1) root in
  fun () -> { next_index = ref 0
            ; symbols = ref syms
            ; calls = ref []
            ; loop_nodes = ref ISet.empty
            ; tbl = ref [||] }

(** Creation of a new symbol. The return value is the key of the created
    symbol, to be used in calls. *)
let create_symbol : t -> string -> string array -> index =
  fun g name args ->
    let arity = Array.length args in
    let index = !(g.next_index) in
    let sym = {index ; name ; arity ; args} in
    incr g.next_index;
    g.symbols := IMap.add index sym !(g.symbols);
    index

(** Add a new up call to the call graph. *)
let add_call : t -> call -> unit =
  fun g c ->
    g.calls := c::!(g.calls)

(** Gives the arity of the symbol corresponding to the given key. The symbol
    must exist. *)
let arity : index -> t -> int =
  fun key g ->
    let sym = IMap.find key !(g.symbols) in
    sym.arity

open Format

let print_call : formatter -> symbol IMap.t -> call -> unit = fun ff tbl c ->
  let caller_sym = IMap.find c.caller tbl in
  let callee_sym = IMap.find c.callee tbl in
  let print_args = LibTools.print_array pp_print_string "," in
  fprintf ff "%s%d(%a%!) <- %s%d%!(" caller_sym.name c.caller
    print_args caller_sym.args callee_sym.name c.callee;
  for i = 0 to callee_sym.arity - 1 do
    if i > 0 then fprintf ff ",";
    let some = ref false in
    for j = 0 to caller_sym.arity - 1 do
      try
        let (_,_,c) = List.find (fun (i',j',x) -> i = i' && j = j') c.matrix in
        let sep = if !some then " " else "" in
        fprintf ff "%s%s%s" sep (cmp_to_string c) caller_sym.args.(j);
        some := true
      with Not_found -> ()
    done
  done;
  fprintf ff ")%!"

let latex_print_calls ff tbl =
  let arities = IMap.bindings !(tbl.symbols) in
  let calls = !(tbl.calls) in
  fprintf ff "\\begin{dot2tex}[dot,options=-tmath]\n  digraph G {\n";
  let arities = List.filter (fun (j,_) ->
    List.exists (fun c -> j = c.caller || j = c.callee) calls)
    (List.rev arities)
  in
  let numbering = List.mapi (fun i (j,_) -> (j,i)) arities in
  let index j = List.assoc j numbering in
  let not_unique name =
    List.fold_left (fun acc (_,sym) -> if sym.name = name then acc+1 else acc) 0 arities
                   >= 2
  in
  let f (j,sym) =
    if not_unique sym.name then
      fprintf ff "    N%d [ label = \"%s_{%d}\" ];\n" (index j) sym.name (index j)
    else
      fprintf ff "    N%d [ label = \"%s\" ];\n" (index j) sym.name
  in
  List.iter f (List.filter (fun (i,_) ->
    List.exists (fun c -> i = c.caller || i = c.callee) calls) arities);
  let print_call arities {callee = i; caller = j; matrix = m} =
    let {name = namej; arity = aj; args = prj} =
      try List.assoc j arities with Not_found -> assert false
    in
    let {name = namei; arity = ai; args = pri} =
      try List.assoc i arities with Not_found -> assert false
    in
    fprintf ff "    N%d -> N%d [label = \"\\left(\\begin{smallmatrix}"
      (index j) (index i);
    for i = 0 to ai - 1 do
      if i > 0 then fprintf ff "\\cr\n";
      for j = 0 to aj - 1 do
        if j > 0 then fprintf ff "&";
        let x =
          try
            let (_,_,x) =
              List.find (fun (i',j',x) -> i = i' && j = j') m in x
          with
            Not_found -> Infi
        in
        let x = match x with
          | Infi -> "\\infty"
          | Zero -> "0"
          | Min1 -> "-1"
        in
        fprintf ff "%s" x
      done;
    done;
    fprintf ff "\\end{smallmatrix}\\right)\"]\n%!"
  in
  List.iter (print_call arities) calls;
  fprintf ff "  }\n\\end{dot2tex}\n"

exception Loop

(** the main function, checking if calls are well-founded *)
let sct : t -> unit = fun ftbl ->
  let num_fun = !(ftbl.next_index) in
  let arities = !(ftbl.symbols) in
  Io.log_sct "SCT starts (%d)...\n%!" !(ftbl.next_index);
  let tbl =
    let tbl = !(ftbl.tbl) in
    let old = Array.length !(ftbl.tbl) in
    if num_fun > old then
      Array.init num_fun
                 (fun i -> if i < old then tbl.(i)
                           else TimedHashtbl.create 13)
    else tbl
  in
  let print_call ff = print_call ff arities in
  (* counters to count added and composed edges *)
  let added = ref 0 and composed = ref 0 in
  (* function adding an edge, return a boolean indicating
     if the edge is new or not *)
  let add_edge i j m =
    (* test idempotent edges as soon as they are discovered *)
    if i = j && prod m m = m && not (decreasing m)
    then
      begin
        Io.log_sct "edge %a idempotent and looping\n%!" print_call
          {callee = i; caller = j; matrix = m };
        raise Loop
      end
    else
      let ti = tbl.(i) in
      let ms = try TimedHashtbl.find ti j with Not_found -> [] in
      if List.exists (fun m' -> subsumes m' m) ms then
        false
      else (
        let ms = m :: List.filter (fun m' -> not (subsumes m m')) ms in
        TimedHashtbl.replace ti j ms;
        true)
  in
  (* adding initial edges *)
  Io.log_sct "initial edges to be added:\n%!";
  List.iter (fun c -> Io.log_sct "\t%a\n%!" print_call c) !(ftbl.calls);
  let new_edges = ref !(ftbl.calls) in
  (* compute the transitive closure of the call graph *)
  Io.log_sct "start completion\n%!";
  let rec fn () =
    match !new_edges with
    | [] -> ()
    | {callee = i; caller = j}::l when j < 0 ->
       new_edges := l;
       fn () (* ignore root *)
    | ({callee = i; caller = j; matrix = m} as c)::l ->
       assert (i >= 0);
       new_edges := l;
       if add_edge i j m then begin
         Io.log_sct "\tedge %a added\n%!" print_call c;
         incr added;
         let t' = tbl.(j) in
         TimedHashtbl.iter (fun k t ->
           List.iter (fun m' ->
             let c' = { callee = j; caller = k; matrix = m' } in
             Io.log_sct "\tcompose: %a * %a = %!" print_call c print_call c';
             let m'' = prod m' m in
             incr composed;
             let c'' = { callee = i; caller = k; matrix = m'' } in
             new_edges := c'' :: !new_edges;
             Io.log_sct "%a\n%!" print_call c'';
             ) t) t'
         end else
         Io.log_sct "\tedge %a is old\n%!" print_call c;
       fn ()
  in
  fn ();
  ftbl.tbl := tbl;
  ftbl.calls := [];
  Io.log_sct "SCT ends: %5d edges added, %6d composed\n%!" !added !composed
