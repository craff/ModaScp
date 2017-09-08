open Bindlib
open Modal

module Act = struct
  type t = string
  let compare  = Pervasives.compare
  let to_string s = s
  let print ff = Format.fprintf ff "%s"
end

module Prop = struct
  type t = bool * string
  let compare = Pervasives.compare
  let imply = (=)
  let neg (b,n) = (not b,n)
  let print ff (b,l) =
    let n = if b then "" else "~" in
    Format.fprintf ff "%s%s" n l
  let to_string (b,s) = if b then s else "~"^s

end

module Modal = Modal.Make(Act)(Prop)

include Modal

let parser lid = ''[a-z][a-zA-Z0-9_']*''
let parser uid = ''[A-Z][a-zA-Z0-9_']+''
let parser id = lid | uid
let parser int = s:''[0-9]+'' -> int_of_string s

type prio =
  PAtom | PTime | PConj | PDisj | PImpl | PEqui

let top = PEqui

let prev = function
  | PAtom -> assert false
  | PTime -> PAtom
  | PConj -> PTime
  | PDisj -> PConj
  | PImpl -> PDisj
  | PEqui -> PImpl

(****************************************************************************
 *                             Keyword management                           *
 ****************************************************************************)

let keywords = Hashtbl.create 20

let is_keyword : string -> bool = Hashtbl.mem keywords

let check_not_keyword : string -> unit = fun s ->
  if is_keyword s then Earley.give_up ()

let new_keyword : string -> unit Earley.grammar = fun s ->
  let ls = String.length s in
  if ls < 1 then raise (Invalid_argument "invalid keyword");
  if is_keyword s then raise (Invalid_argument "keyword already defied");
  Hashtbl.add keywords s s;
  let f str pos =
    let str = ref str in
    let pos = ref pos in
    for i = 0 to ls - 1 do
      let (c,str',pos') = Input.read !str !pos in
      if c <> s.[i] then Earley.give_up ();
      str := str'; pos := pos'
    done;
    let (c,_,_) = Input.read !str !pos in
    match c with
    | 'a'..'z' | 'A'..'Z' | '_' -> Earley.give_up ()
    | _                         -> ((), !str, !pos)
  in
  Earley.black_box f (Charset.singleton s.[0]) false s

let _False_ = new_keyword "False"
let _True_ = new_keyword "True"
let _X_ = parser (new_keyword "X") | "○" | "◯"
let _A_ = parser (new_keyword "A") | "[]" | "□"
let _E_ = parser (new_keyword "E") | "<>" | "◊"
let _L_ = parser '<' | "⟨"
let _R_ = parser '>' | "⟩"
let _F_ = new_keyword "F"
let _G_ = new_keyword "G"
let _U_ = new_keyword "U"
let _B_ = new_keyword "B"
let _N_ = parser '!' | '~' | "¬"
let _Mu = parser (new_keyword "M") | "μ"
let _Nu = parser (new_keyword "N") | "ν"


let cst c = fun env -> c
let cs1 c f = fun env -> c (f env)
let cs2 c f g = fun env -> c (f env) (g env)
let csl c l = fun env -> c (List.map (fun f -> f env) l)

let bfix cst names body index =
  let names = Array.of_list names in
  let body = Array.of_list body in
  if Array.length names <> Array.length body then Earley.give_up ();
  if index < 0 || index >= Array.length names then Earley.give_up ();
  (fun env ->
    box_apply (cst index)
              (mbind vvar names
                      (fun xs ->
                        let env = ref env in
                        Array.iter2 (fun name v ->
                            env := (name,v)::!env) names xs;
                        box_array (Array.map (fun f -> f !env) body))))

let bmu = bfix (fun index x -> Mu(Inf,index,x))
let bnu = bfix (fun index x -> Nu(Inf,index,x))


let parser args =
  | l:id -> [l]
  | '(' l:id ls:{ _:',' id}* ')' -> l::ls

let parser index =
  | EMPTY -> 0
  | '[' n:int ']' -> n

let parser form prio =
  | _True_               when prio = PAtom -> cst always
  | _False_              when prio = PAtom -> cst never
  | l:id                 when prio = PAtom ->
                              check_not_keyword l;
                              (fun env -> try
                                  List.assoc l env
                                with
                                  Not_found -> atom (true,l))
  | _Mu names:args '.' body:body idx:index when prio = top -> bmu names body idx
  | _Nu names:args '.' body:body idx:index when prio = top -> bnu names body idx

  | '(' f:(form top) ')' when prio = PAtom -> f
  | _N_ f:(form PAtom)   when prio = PAtom -> cs1 neg' f
  | _G_ f:(form PAtom)   when prio = PAtom -> cs1 globally f
  | _F_ f:(form PAtom)   when prio = PAtom -> cs1 eventually f
  | _X_ f:(form PAtom)   when prio = PAtom -> cs1 next f
  | _A_ f:(form PAtom)   when prio = PAtom -> cs1 cAll f
  | _E_ f:(form PAtom)   when prio = PAtom -> cs1 cExi f
  | '[' a:lid ']' f:(form PAtom)   when prio = PAtom -> cs1 (mAll a) f
  | _L_ a:lid _R_ f:(form PAtom)   when prio = PAtom -> cs1 (mExi a) f
  | f:(form (prev prio)) when prio > PAtom -> f
  | f:(form PAtom)  _U_  g:(form PTime)      when prio = PTime -> cs2 until f g
  | f:(form PAtom)  _B_  g:(form PTime)      when prio = PTime -> cs2 before f g
  | f:(form PTime) l:{_:'&' g:(form PTime)}+ when prio = PConj -> csl conj (f::l)
  | f:(form PConj) l:{_:'|' g:(form PConj)}+ when prio = PDisj -> csl disj (f::l)
  | f:(form PDisj)  "=>" g:(form PImpl)      when prio = PImpl -> cs2 imply' f g
  | f:(form PImpl) "<=>" g:(form PImpl)      when prio = PEqui -> cs2 equiv f g

and body =
  | f:(form top) -> [f]
  | '(' l:(form top) ls:{ _:',' (form top)}* ')' -> l::ls

let parser formula =
  | f:(form top) EOF -> unbox (f [])

let blank = Earley.blank_regexp "\\(\\(#[^\n]*\\)\\|[ \n\t\r]\\)*"

let action = ref sat

let spec = Arg.align
  [ ( "--debug"
    , Arg.String Io.set_debug
    , "s  Display the debugging informations
                   'p': progress
                   'r': search for recursion (loop)
                   's': sat/time solver
                   't': show time
                   'v': verbose result
                   'y': size change principle")
  ; ( "--sat"
    , Arg.Unit (fun () ->  action := sat)
    , "check for satisfiability" )
  ; ( "--valid"
    , Arg.Unit (fun () ->  action := prove)
    , "check for validity" )
  ]

let _ = Arg.parse spec (fun _ -> ()) ""

let main () =
  Earley.handle_exception (fun () ->
      let f = Earley.parse_channel formula blank stdin in
      !action f) ()

let _ = main ()
