open Modal

module Act = struct
  type t = string
  let compare  = Pervasives.compare
  let to_string a = a
end

module Prop = struct
  type t = bool * int
  let compare = Pervasives.compare
  let imply = (=)
  let neg (b,n) = (not b,n)
  let to_string (b,n) = Printf.sprintf "(%b,%d)" b n
end

module Modal = Modal.Make(Act)(Prop)

include Modal


type automata =
  { num_states : int
  ; transitions : (int * string * int) list
  ; init : int
  }

let to_nu a =
  Bindlib.unbox (
      nu a.init a.num_states (fun xs ->
           Array.init a.num_states (fun i ->
                        let l = List.filter (fun (i',_,_) -> i' = i) a.transitions in
                        conj (List.map (fun (_,s,j) -> mExi s xs.(j)) l))))
