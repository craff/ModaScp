open Bindlib
open Print
open Sct
open Timed

let chr_scp = Chrono.create "scp"
let chr_search = Chrono.create "search"
let chr_add = Chrono.create "add"
let chr_solve = Chrono.create "solve"
let chr_simp = Chrono.create "simplify"

(** Signature for that actions *)
module type Act = sig
  type t
  val compare : t -> t -> int
  val to_string : t -> string
end

(** Signature for the predicate usually giving properties of states *)
module type Prop = sig
  type t
  val imply : t -> t -> bool
  val neg : t -> t
  val compare : t -> t -> int
  val to_string : t -> string
end

(** The min functor *)
module Make(Act:Act)(Prop:Prop) = struct

  (** type of time, that can index mus and nus *)
  type time =
    | Inf              (** inifinite ordinal *)
    | Var of (int * int)

  (** Formula of the modal mu calculus + Next from LTL,
      Next means and transition, inclusing invisible ones *)
   and modal = {
       address: int;
       key: int;
       data: modal';
       keep:Obj.t list; (* to keep refs to the hashed binders *)
     }

   and modal' =
    (** Logical connectives *)
    | Atom of Prop.t        (** atomic formulas, denotes a set of states *)
    | Conj of modal list    (** conjonction *)
    | Disj of modal list    (** disjonction *)
    (** Modalities of the modal mu calculus *)
    | MAll of Act.t * modal (** MAll(a,m) holds iff m holds after
                                all a-labelled transition *)
    | MExi of Act.t * modal (** MExi(a,m) holds iff m holds after
                                some a-labelled transition *)
    (** CTL Modalities *)
    | CAll of modal         (** CAll(m) holds iff m holds after
                                all labelled transitions *)
    | CExi of modal         (** CExi(m) holds iff m holds after
                                some labelled transition *)
    (** LTL modality *)
    | Next of modal         (** Next(m) holds iff m holds in the next states,
                                which we may reach by a labelled transition or
                                an invisible one *)
    (** fixpoints *)
    | Mu   of time * int * (modal, modal array) mbinder (** Least fixpoint *)
    | Nu   of time * int * (modal, modal array) mbinder (** Greatest fixpoint *)

    | VVar of modal var
    | HVar of int
    | IVar of int * int

  (* Time printing *)
  let tprint ff = function
    | Inf -> ()
    | Var(t,f) -> Format.fprintf ff "?"  (* FIXME *)

  let key m = m.key

  let hash m = m.key

  (** total order on time *)
  let rec compare_time t1 t2 =
    match (t1,t2) with
    | Var _, Inf -> -1
    | Inf, Var _ -> 1
    | Inf, Inf -> 0
    | Var(m1,f1), Var(m2,f2) ->
       match compare m1 m2 with
       | 0 -> f1 - f2
       | c -> c

  module HModal = struct
    let mkHVar n = { address = -n; key = Hashtbl.hash (`HVar, n); data = HVar n; keep = [] }

    let canonical_vars f =
      let occurs = mbinder_occurs f in
      let i = ref 0 in
      let r = mbinder_rank f in
      Array.map (fun b ->
          let n = if b then (incr i; r + !i) else 0 in
          mkHVar n) occurs

    let hash_mbinder ptr f =
      let canonicals = msubst f (canonical_vars f) in
      ptr := Obj.repr canonicals :: !ptr;
      Hashtbl.hash(mbinder_occurs f,Array.map key canonicals)

    let hash' data =
      let ptr = ref [] in
      let h = match data with
        | HVar n      -> Hashtbl.hash (`HVar, n)
        | VVar v      -> hash_var v
        | Atom a      -> Hashtbl.hash (`Atom, a)
        | Conj l      -> Hashtbl.hash (`Conj, List.map key l)
        | Disj l      -> Hashtbl.hash (`Disj, List.map key l)
        | MAll (a, m) -> Hashtbl.hash (`MAll, a, key m)
        | MExi (a, m) -> Hashtbl.hash (`MExi, a, key m)
        | CAll m      -> Hashtbl.hash (`CAll, key m)
        | CExi m      -> Hashtbl.hash (`CExi, key m)
        | Next m      -> Hashtbl.hash (`Next, key m)
        | Mu(t,i,f)   -> Hashtbl.hash (`Mu,t,i,hash_mbinder ptr f)
        | Nu(t,i,f)   -> Hashtbl.hash (`Nu,t,i,hash_mbinder ptr f)
        | IVar(n,m)   -> Hashtbl.hash (`IVar,n,m)
      in
      (h, !ptr)

    let equal_mbinder f f' =
      mbinder_rank f = mbinder_rank f' &&
        mbinder_occurs f = mbinder_occurs f' &&
        begin
          try
            let a  = msubst f  (canonical_vars f) in
            let a' = msubst f' (canonical_vars f) in
            Array.iteri (fun i x ->
                let y = a'.(i) in
                if x.address <> y.address then raise Exit) a;
            true
          with Exit -> false
        end

    let equal' m1 m2 = m1 == m2 || match (m1, m2) with
      | HVar n1     , HVar n2     -> n1 = n2
      | VVar v1     , VVar v2     -> compare_vars v1 v2 = 0
      | Atom a1     , Atom a2     -> Prop.compare a1 a2 = 0
      | Conj l1     , Conj l2     ->
         List.length l1 = List.length l2 &&
           List.for_all2 (fun x y -> x.address = y.address) l1 l2
      | Disj l1     , Disj l2     ->
         List.length l1 = List.length l2 &&
           List.for_all2 (fun x y -> x.address = y.address) l1 l2
      | MAll(a1, m1), MAll(a2,m2) ->
         Act.compare a1 a2 = 0 && m1.address = m2.address
      | MExi(a1, m1), MExi(a2,m2) ->
         Act.compare a1 a2 = 0 && m1.address = m2.address
      | CAll(m1)    , CAll(m2)    -> m1.address = m2.address
      | CExi(m1)    , CExi(m2)    -> m1.address = m2.address
      | Next(m1)    , Next(m2)    -> m1.address = m2.address
      | Mu(t1,i1,f1), Mu(t2,i2,f2)->
         i1 = i2 && compare_time t1 t2 = 0 && equal_mbinder f1 f2
      | Nu(t1,i1,f1), Nu(t2,i2,f2)->
         i1 = i2 && compare_time t1 t2 = 0 && equal_mbinder f1 f2
      | IVar(n1,m1) , IVar(n2,m2) -> n1 = n2 && m1 = m2
      | _           , _           -> false

    let equal m1 m2 = equal' m1.data m2.data
    type t = modal
    let hash = hash
  end

  module WModal = Weak.Make(HModal)
  (** A total order on formulas, This order indirectly select the next
      litteral in the solver procedure, so changing it is not at all
      neutral *)

  let hashtbl = WModal.create 1001
  let get_addr =
    let c = ref 1 in
    fun () ->
    let c' = !c in
    c := c' + 1;
    c'

  let rec hashCons data =
    let key, keep = HModal.hash' data in
    let address = get_addr () in
    let data' = { address; key; data; keep } in
    (*Format.eprintf "Hashing: %a %d %d ⇒ " print data' key address;*)
    try
      let res = WModal.find hashtbl data' in
      (*Format.eprintf "Found %a\n%!" print res;*)
      res
    with Not_found ->
      (*Format.eprintf "Not found\n%!";*)
      WModal.add hashtbl data';
      data'

  (** vvar as a function, for Bindlib *)
  and vvar x = hashCons (VVar x)

  (** Printing functions *)
  and vprint ff v = sprint ff (name_of v)

  and print ff m = match m.data with
    | Atom a    -> Format.pp_print_string ff (Prop.to_string a)
    | Conj []   -> Format.fprintf ff "⊤"
    | Disj []   -> Format.fprintf ff "⊥"
    | Conj l    -> Format.fprintf ff "(%a)" (lprint " ∧ " print) l
    | Disj l    -> Format.fprintf ff "(%a)" (lprint " ∨ " print) l
    | MAll(a,m) -> Format.fprintf ff "[%s]%a" (Act.to_string a) print m
    | MExi(a,m) -> Format.fprintf ff "⟨%s⟩%a" (Act.to_string a) print m
    | CAll(m)   -> Format.fprintf ff "[]%a" print m
    | CExi(m)   -> Format.fprintf ff "⟨⟩%a" print m
    | Next(m)   -> Format.fprintf ff "O%a" print m
    | Mu(t,n,b) ->
       let (names, ms) = unmbind vvar b in
       Format.fprintf ff "μ(%a)_%d%a.(%a)" (aprint ", " vprint)
                      names n tprint t (aprint ", " print) ms
    | Nu(t,n,b) ->
       let (names, ms) = unmbind vvar b in
       Format.fprintf ff "ν(%a)_%d%a.(%a)" (aprint ", " vprint)
                      names n tprint t (aprint ", " print) ms
    | VVar v    -> vprint ff v
    | IVar(d,n) -> Format.fprintf ff "IVar(%d,%d)" d n
    | HVar(n)   -> Format.fprintf ff "HVar(%d)" n

  let rec old_ileq m1 m2 =
    let ileq = old_ileq in
    if m1 == m2 then 0 else
      match m1.data, m2.data with
      | Atom(a1), Atom(a2) -> Prop.compare a1 a2
      | Atom _, _ -> -1
      | _, Atom _ -> 1
      | Disj(l1), Disj(l2)
      | Conj(l1), Conj(l2) ->
         let rec gn ms1 ms2 =
           match ms1,ms2 with
           | [], [] -> 0
           | [], _  -> 1
           | _, []  -> -1
           | m1::ms1, m2::ms2 ->
              begin
                match ileq m1 m2 with
                | 0 -> gn ms1 ms2
                | c -> c
              end
         in
         gn l1 l2
      | Disj _, _ -> -1
      | _, Disj _ -> 1
      | Conj _, _ -> -1
      | _, Conj _ -> 1
      | Nu(t1,i1,f1), Nu(t2,i2,f2)
      | Mu(t1,i1,f1), Mu(t2,i2,f2) ->
         begin
           match compare i1 i2 with
           | 0 ->
              begin
                match compare (mbinder_arity f1) (mbinder_arity f2) with
                | 0 ->
                   let (v,m) = unmbind vvar f1 in
                   begin
                     match ileq m.(i1) (msubst f2 (Array.map free_of v)).(i2) with
                     | 0 -> compare_time t1 t2
                     | c -> c
                   end
                | c -> c
              end
           | c -> c
         end
      | Nu _, _ -> -1
      | _, Nu _ -> 1
      | Mu _, _ -> -1
      | _, Mu _ -> 1
      | Next(m1), Next(m2) -> ileq m1 m2
      | Next _, _ -> -1
      | _, Next _ -> 1
      | CAll(m1), CAll(m2)
      | CExi(m1), CExi(m2) -> ileq m1 m2
      | CAll _, _ -> -1
      | _, CAll _ -> 1
      | CExi _, _ -> -1
      | _, CExi _ -> 1
      | MAll(a1,m1), MAll(a2,m2)
      | MExi(a1,m1), MExi(a2,m2) ->
         begin
           match Act.compare a1 a2 with
           | 0 -> ileq m1 m2
           | c -> c
         end
      | MAll _, _ -> -1
      | _, MAll _ -> 1
      | MExi _, _ -> -1
      | _, MExi _ -> 1
      | VVar(v1), VVar(v2) -> compare_vars v1 v2
      (*| VVar _, _ -> -1
      | _, VVar _ -> 1*)
      | HVar _, _      -> assert false
      | _     , HVar _ -> assert false
      | IVar _, _
      | _, IVar _ -> assert false

  let ileq m1 m2 =
    if m1.address = m2.address then (assert (old_ileq m1 m2 = 0); 0) else
      (assert (old_ileq m1 m2 <> 0 ||
                 (Format.eprintf "%a  <>  %a\n" print m1 print m2; false));
      match m1.data, m2.data with
      | Atom _, Atom _ -> compare m1.address m2.address
      | Atom _, _      -> -1
      | _     , Atom _ -> 1
      | Disj _, Disj _ -> compare m1.address m2.address
      | Disj _, _      -> -1
      | _     , Disj _ -> 1
      | Conj _, Conj _ -> compare m1.address m2.address
      | Conj _, _      -> -1
      | _, Conj _      -> 1
      | Nu   _, Nu   _ -> compare m1.address m2.address
      | Nu   _, _      -> -1
      | _     , Nu   _ -> 1
      | Mu   _, Mu   _ -> compare m1.address m2.address
      | Mu   _, _      -> -1
      | _     , Mu   _ -> 1
      | Next _, Next _ -> compare m1.address m2.address
      | Next _, _      -> -1
      | _     , Next _ -> 1
      | CAll _, CAll _ -> compare m1.address m2.address
      | CAll _, _      -> -1
      | _, CAll _      -> 1
      | CExi _, CExi _ -> compare m1.address m2.address
      | CExi _, _      -> -1
      | _     , CExi _ -> 1
      | MAll _, MAll _ -> compare m1.address m2.address
      | MAll _, _      -> -1
      | _     , MAll _ -> 1
      | MExi _, MExi _ -> compare m1.address m2.address
      | MExi _, _      -> -1
      | _     , MExi _ -> 1
      | VVar _, VVar _ -> compare m1.address m2.address
      | VVar _, _      -> -1
      | _     , VVar _ -> 1
      | HVar _, _      -> assert false
      | _     , HVar _ -> assert false
      | IVar _, IVar _ -> assert false)

  let ileq = old_ileq

  module Mod = struct
    type t = modal
    let compare = ileq
  end
  module MMap = Map.Make(Mod)

  let index m = m.address

  (** Smart constructors *)
  let atom' a = hashCons (Atom a)
  let atom a = box (atom' a)
  let next' m = hashCons (Next m)
  let cAll' m = hashCons (CAll m)
  let cExi' m = hashCons (CExi m)
  let mAll' a m = hashCons (MAll(a,m))
  let mExi' a m = hashCons (MExi(a,m))

  (** Sorting and simplifiying disjunction *)
  let rec _Disj l =
    let rec fn (acc:modal list) m = match acc, m.data with
      | _, Conj [] -> raise Exit (* True in a disjunction *)
      | _, Disj l' -> List.fold_left fn acc l'
      | ({ data = Next m1}::acc), Next m2 -> next'(_Disj [m1;m2])::acc
      | ({ data = CAll m1}::acc), CAll m2 -> cAll'(_Disj [m1;m2])::acc
      | ({ data = CExi m1}::acc), CExi m2 -> cExi'(_Disj [m1;m2])::acc
      | ({ data = MAll(a1, m1)}::acc), MAll(a2,m2) when Act.compare a1 a2 = 0 ->
         mAll' a1 (_Disj [m1;m2]) :: acc
      | ({ data = MExi(a1, m1)}::acc), MExi(a2,m2) when Act.compare a1 a2 = 0 ->
         mExi' a1 (_Disj [m1;m2]) :: acc
      | _, _ -> m::acc
    in
    try
      let l = List.fold_left fn [] l in
      let l = List.sort_uniq ileq l in
      match l with
      | [m] -> m
      | _ -> hashCons (Disj l)
    with Exit ->
      hashCons (Conj [])

  (** Sorting and simplifiying conjunction *)
  let _Conj l =
    let rec fn acc m = match m.data with
      | Disj [] -> raise Exit (* False in a conjonction *)
      | Conj l' -> List.fold_left fn acc l'
      | _ -> m::acc
    in
    try
      let l = List.fold_left fn [] l in
      let l = List.sort_uniq ileq l in
      match l with
      | [m] -> m
      | _ -> hashCons (Conj l)
    with Exit ->
      hashCons (Disj [])

  let conj l = box_apply (fun x -> _Conj x) (box_list l)
  let disj l = box_apply (fun x -> _Disj x) (box_list l)

  let always = conj []
  let never  = disj []
  let always' = unbox always
  let never'  = unbox never

  let mAll' a m = hashCons (MAll(a,m))
  let mAll  a m = box_apply (mAll' a) m
  let mExi' a m = hashCons (MExi(a,m))
  let mExi  a m = box_apply (mExi' a) m
  let cAll' m = hashCons (CAll(m))
  let cAll  m = box_apply cAll'  m
  let cExi' m = hashCons (CExi(m))
  let cExi  m = box_apply cExi' m
  let next' m = hashCons (Next(m))
  let next  m = box_apply next' m

  (** mu and nu smart constructors given in two variants, with
      function [mu] and [nu] taking an array of [modal box] and [mu']
      and [nu'] an array of [modal var] *)
  let mu ?(time=Inf) idx s fn =
    let names = Array.init s (fun i -> "M" ^ string_of_int i) in
    box_apply (fun x -> hashCons (Mu(time,idx,x)))
              (mbind vvar names
                      (fun xs -> box_array (fn xs)))

  let mu' ?(time=Inf) idx s fn =
    let names = Array.init s (fun i -> "M" ^ string_of_int i) in
    box_apply (fun x -> hashCons (Mu(time,idx,x)))
              (mvbind vvar names
                      (fun xs -> box_array (fn xs)))

  let nu ?(time=Inf) idx s fn =
    let names = Array.init s (fun i -> "M" ^ string_of_int i) in
    box_apply (fun x -> hashCons (Nu(time,idx,x)))
              (mbind vvar names
                      (fun xs -> box_array (fn xs)))

  let nu' ?(time=Inf) idx s fn =
    let names = Array.init s (fun i -> "M" ^ string_of_int i) in
    box_apply (fun x -> hashCons (Nu(time,idx,x)))
              (mvbind vvar names
                      (fun xs -> box_array (fn xs)))

  (** unary mu and nu *)
  let mu0 ?(time=Inf) fn =
    mu ~time 0 1 (fun x -> [| fn x.(0) |])

  let nu0 ?(time=Inf) fn =
    nu ~time 0 1 (fun x -> [| fn x.(0) |])

  (** lifting function *)
  let lift : modal -> modal bindbox = fun m ->
    let rec fn m = match m.data with
      | Mu(t,n,b) ->
         mu' ~time:t n (mbinder_arity b)
            (fun xs -> Array.map fn (msubst b (Array.map free_of xs)))
      | Nu(t,n,b) ->
         nu' ~time:t n (mbinder_arity b)
            (fun xs -> Array.map fn (msubst b (Array.map free_of xs)))
      | Conj l -> conj (List.map fn l)
      | Disj l -> disj (List.map fn l)
      | MAll (a,m) -> mAll a (fn m)
      | MExi (a,m) -> mExi a (fn m)
      | CAll (m) -> cAll (fn m)
      | CExi (m) -> cExi (fn m)
      | Next (m) -> next (fn m)
      | Atom b -> atom b
      | VVar m -> box_of_var m
      | IVar _ -> assert false
      | HVar _ -> assert false
    in
    fn m

  (** Give distinct an consecutive number to every mu *)
  let uniformise : modal -> int * modal = fun m ->
    let count = ref 0 in
    let get () =
      let c = !count in
      count := c + 1;
      c
    in
    let rec fn m = match m.data with
      | Mu(t,n,b) ->
         mu' ~time:(Var(get(),0)) n (mbinder_arity b)
            (fun xs -> Array.map fn (msubst b (Array.map free_of xs)))
      | Nu(t,n,b) ->
         nu' n (mbinder_arity b)
            (fun xs -> Array.map fn (msubst b (Array.map free_of xs)))
      | Conj l -> conj (List.map fn l)
      | Disj l -> disj (List.map fn l)
      | MAll (a,m) -> mAll a (fn m)
      | MExi (a,m) -> mExi a (fn m)
      | CAll (m) -> cAll (fn m)
      | CExi (m) -> cExi (fn m)
      | Next (m) -> next (fn m)
      | Atom b -> atom b
      | VVar m -> box_of_var m
      | IVar _ -> assert false
      | HVar _ -> assert false
    in
    (!count, unbox (fn m))
  (** Give distinct an consecutive number to every mu *)

  let collect_changes : modal -> (int * bool) array = fun m ->
    let res = ref [] in
    let rec fn m = match m.data with
      | Mu(t,n,b) ->
         begin
           match t with
           | Var(m,0) -> res := (m,false) :: !res
           | Var(m,1) -> res := (m,true)  :: !res
           | _ -> assert false
         end;
         let (names, ms) = unmbind vvar b in
         Array.iter fn ms
      | Nu(t,n,b) ->
         let (names, ms) = unmbind vvar b in
         Array.iter fn ms
      | Conj l -> List.iter fn l
      | Disj l -> List.iter fn l
      | MAll (a,m) -> fn m
      | MExi (a,m) -> fn m
      | CAll (m) -> fn m
      | CExi (m) -> fn m
      | Next (m) -> fn m
      | Atom b -> ()
      | VVar m -> ()
      | IVar _ -> assert false
      | HVar _ -> assert false
    in
    fn m;
    Array.of_list (List.rev !res)

  let collect_initial : modal -> int array * int option array = fun m ->
    let res = ref [] in
    let rec fn m = match m.data with
      | Mu(t,n,b) ->
         res := m.address :: !res;
         let (names, ms) = unmbind vvar b in
         Array.iter fn ms
      | Nu(t,n,b) ->
         let (names, ms) = unmbind vvar b in
         Array.iter fn ms
      | Conj l -> List.iter fn l
      | Disj l -> List.iter fn l
      | MAll (a,m) -> fn m
      | MExi (a,m) -> fn m
      | CAll (m) -> fn m
      | CExi (m) -> fn m
      | Next (m) -> fn m
      | Atom b -> ()
      | VVar m -> ()
      | IVar _ -> assert false
      | HVar _ -> assert false
    in
    fn m;
    let vars = Array.of_list (List.rev !res) in
    let rels = Array.map (fun _ -> None) vars in
    (vars, rels)

  let flatten_rels : int array -> int option array -> int array =
    fun vars rels ->
      let vars = Array.copy vars in
      let len = Array.length vars in
      assert (Array.length rels = len);
      let sler = Array.make len None in
      let new_rel = Array.make len None in
      Array.iteri (fun i o ->
          match o with
          | None -> ()
          | Some j ->
             match sler.(j) with
             | None -> sler.(j) <- Some i; new_rel.(i) <- Some j
             | Some i' -> vars.(i) <- vars.(i'))
                  rels;
      vars


  type litteral =
    | LAtom of Prop.t
    | LPos of litteral'
    | LNeg of litteral'

   and litteral' =
     | LConj of modal
     | LMAll of (Act.t * modal)
     | LMExi of (Act.t * modal)
     | LCAll of modal
     | LCExi of modal
     | LNext of modal

  let negLit = function
    | LAtom a -> LAtom (Prop.neg a)
    | LPos l -> LNeg l
    | LNeg l -> LPos l

  let implyLit a1 a2 =
    let f l1 l2 = match (l1, l2) with
      | (LConj m1, LConj m2) -> m1.address = m2.address
      | (LCAll m1, LCAll m2) -> m1.address = m2.address
      | (LCExi m1, LCExi m2) -> m1.address = m2.address
      | (LNext m1, LNext m2) -> m1.address = m2.address
      | (LMAll (a1,m1), LMAll(a2,m2)) -> Act.compare a1 a2 = 0 && m1.address = m2.address
      | (LMExi (a1,m1), LMExi(a2,m2)) -> Act.compare a1 a2 = 0 && m1.address = m2.address
      | _ -> false
    in
    match (a1, a2) with
    | (LAtom a1, LAtom a2) -> Prop.imply a1 a2
    | LPos l1, LPos l2 -> f l1 l2
    | LNeg l1, LNeg l2 -> f l1 l2

  type clause = litteral list

  type clauses = clause list

  module HashModal = struct
    type t = modal
    let hash m1 = m1.key
    let equal m1 m2 = m1.address = m2.address
  end

  module ModalTbl = Hashtbl.Make(HashModal)

  let pred0 = function
    | Inf -> assert false
    | Var(n,p) -> Var(n,p+1)

  type modalInfo = { arity : int
                   ; diffs : (modal * (int * bool) array) ModalTbl.t
                   ; mutable clauses : clauses
                   }

  let print_litteral' ff l = match l with
    | LConj m -> Format.fprintf ff "%d " m.address
    | LMAll(a,m) -> Format.fprintf ff "[%s]%d " (Act.to_string a) m.address
    | LMExi(a,m) -> Format.fprintf ff "⟨%s⟩%d " (Act.to_string a) m.address
    | LCAll m -> Format.fprintf ff "[]%d " m.address
    | LCExi m -> Format.fprintf ff "⟨⟩%d " m.address
    | LNext m -> Format.fprintf ff "O%d" m.address

  let print_litteral ff l = match l with
    | LAtom(a) -> Format.fprintf ff "%s " (Prop.to_string a)
    | LPos(m)  -> Format.fprintf ff "+%a " print_litteral' m
    | LNeg(m)  -> Format.fprintf ff "-%a " print_litteral' m


  let print_clause ff l = List.iter (print_litteral ff) l

  let print_diff ff l =
    Array.iter (fun (n,b) ->
        if b then Format.fprintf ff "%d-1 " n
        else Format.fprintf ff "%d " n) l

  let printModalInfo ff (m, info) =
    Format.fprintf ff "F(%d) = %a\n" m.address print m;
    Format.fprintf ff "A(%d) = %d\n" m.address info.arity;
    Format.fprintf ff "C(%d) =\n" m.address;
    List.iter (Format.fprintf ff "  %a\n" print_clause) info.clauses;
    Format.fprintf ff "D(%d) =\n" m.address;
    ModalTbl.iter
      (fun m (m', diff) ->
        Format.fprintf ff "  %d -> %d(%a)\n" m.address m'.address print_diff diff)
      info.diffs

  let rec buildMap : modal -> modalInfo ModalTbl.t * modal = fun m ->
    let tbl = ModalTbl.create 101 in
    let rec addToMap m0 =
      let diffs = ModalTbl.create 17 in
      let rec clauses : modal option -> clauses -> modal -> clauses = fun parent cls m ->
        Format.printf "clauses %a\n%!" print m;
        match m.data with
        | Mu(t,i,f) ->
           let t = pred0 t in
           let v = Array.init (mbinder_arity f) (fun i -> hashCons(Mu(t,i,f))) in
           let m = (msubst f v).(i) in
           clauses parent cls m
        | Nu(t,i,f) ->
           assert(t=Inf);
           let v = Array.init (mbinder_arity f) (fun i -> hashCons(Nu(t,i,f))) in
           let m = (msubst f v).(i) in
           clauses parent cls m
        | Conj l -> List.fold_left (clauses parent) cls l
        | Disj l ->
           let cls, l = List.fold_left mk_litteral (cls,[]) l in
           let l = match parent with
             | None -> l
             | Some ({ data = Conj _ } as p) -> LNeg (LConj p) :: l
             | _ -> assert false
           in
           l::cls
        | _ ->
           clauses parent cls (hashCons(Disj[m]))

      and mk_litteral = fun (cls,acc) m ->
        match m.data with
        | Mu(t,i,f) ->
           let t = pred0 t in
           let v = Array.init (mbinder_arity f) (fun i -> hashCons(Mu(t,i,f))) in
           let m = (msubst f v).(i) in
           mk_litteral (cls,acc) m
        | Nu(t,i,f) ->
           assert(t=Inf);
           let v = Array.init (mbinder_arity f) (fun i -> hashCons(Nu(t,i,f))) in
           let m = (msubst f v).(i) in
           mk_litteral (cls,acc) m
        | Conj _ ->
           let cls = clauses (Some m) cls  m in
           (cls, LPos (LConj m) :: acc)
        | Disj l ->
           List.fold_left mk_litteral (cls,acc) l
        | Atom a ->
           (cls, LAtom a :: acc)
        | m0 ->
           let diff = collect_changes m in
           let f = function
             | Next m -> (LNext m, m, addToMap m)
             | CAll m -> (LCAll m, m, addToMap m)
             | CExi m -> (LCExi m, m, addToMap m)
             | MAll(a,m) -> (LMAll (a,m), m, addToMap m)
             | MExi(a,m) -> (LMExi (a,m), m, addToMap m)
             | _ -> assert false
           in
           let lit,m,m' = f m0 in
           Format.printf "Add diff %d %d\n" m.address m'.address;
           ModalTbl.add diffs m (m', diff);
           (cls, LPos lit :: acc)
      in

      Format.printf "addToMap %a\n%!" print m0;
      let (arity, um) = uniformise m0 in
      Format.printf "addToMap %a\n%!" print um;
      if not (ModalTbl.mem tbl um) then
        begin
          let r = { arity; diffs; clauses = [] } in
          ModalTbl.add tbl um r;
          Format.printf "Not found %d (%d)\n%!" um.address (ModalTbl.length tbl);
          r.clauses <- clauses None [] um;
        end
      else
        Format.printf "Found %d (%d)\n%!" um.address (ModalTbl.length tbl);
      um
    in

    let um = addToMap m in
    (tbl, um)

  (** negation *)
  let neg : modal -> modal = fun m ->
    let rec fn m = match m.data with
      | Mu(t,n,b) ->
         nu ~time:t n (mbinder_arity b)
            (fun xs -> Array.map fn (msubst b (Array.map unbox xs)))
      | Nu(t,n,b) ->
         mu ~time:t n (mbinder_arity b)
            (fun xs -> Array.map fn (msubst b (Array.map unbox xs)))
      | Conj l -> disj (List.map fn l)
      | Disj l -> conj (List.map fn l)
      | MAll (a,m) -> mExi a (fn m)
      | MExi (a,m) -> mAll a (fn m)
      | CAll (m) -> cExi (fn m)
      | CExi (m) -> cAll (fn m)
      | Next (m) -> next (fn m)
      | Atom b -> atom (Prop.neg b)
      | VVar m -> box_of_var m
      | IVar _ -> assert false
      | HVar _ -> assert false
    in
    unbox (fn m)

  (** lazy negation, in bindlib *)
  let neg' = box_apply neg

  (** derived constructors *)
  let imply m1 m2 = _Disj [neg m1; m2]
  let imply' m1 m2 = disj [neg' m1; m2]

  let disj2 m1 m2 = disj [m1; m2]
  let conj2 m1 m2 = conj [m1; m2]
  let equiv m1 m2 = conj2 (imply' m1 m2) (imply' m2 m1)

  let globally m = nu0 (fun x -> conj2 m (next x))
  let eventually m = mu0 (fun x -> disj2 m (next x))
  let until f g = mu0 (fun x -> disj2 (conj2 f (next x)) g)
  let before f g = nu0 (fun x -> disj2 (conj2 f (next x)) g) (* CHECK ? *)

  (** A tree structure to store induction hypothesese, these is a map
      associating to the induction hypothesis (a sorted list of
      formulas), its index for the scp *)
  type 'a modal_tree =
    { leaf : 'a option ref (** if leaf is not None, we have reach a value
                               associated to the list we searched for *)
    ; next : (dmodal, 'a modal_node) TimedHashtbl.t
      (** A table associating to the debruijn representation the
          content of table for lists starting with
          a formula with such a debruijn representation *)
    }


   (** - the formula is the formula at this point of the list.
       - the modal tree stores the table for the rest of the list.
       TODO: the only information in m is the position of the infinite
       time. This could be made simpler and more efficient, with no
       need for a list, by recording the position of tje infinite
       in the leaf.
    *)
  and 'a modal_node = (modal * 'a modal_tree) list

  let empty_tree () = { leaf = ref None; next = TimedHashtbl.create 13 }

  (** The proving context *)
  type context =
    { cgraph : call_graph         (** the call graph *)
    ; indtop : index * time array (** the current vertex in the call graph *)
    ; indhyp : (index * modal list) modal_tree  (** the stored induction hypothesis *)
    }

  let empty_ctx () =
    { cgraph = create ()
    ; indtop = (root, [||])
    ; indhyp = empty_tree ()
    }

  (** Creation of an induction hypothesis from a list of formula *)
  let mk_indhyp ctx ms =
    let res = ref [] in
    let rec fn m1 =
      match m1.data with
      | Nu(t1,i1,f1) ->
         if t1 != Inf && not (List.exists (fun t -> compare_time t1 t = 0) !res)
         then res := t1 :: !res;
         let (v,m) = unmbind vvar f1 in
         Array.iter fn m
      | Mu(t1,i1,f1) ->
         if t1 != Inf && not (List.exists (fun t -> compare_time t1 t = 0) !res)
         then res := t1 :: !res;
         let (v,m) = unmbind vvar f1 in
         Array.iter fn m
      | Disj(l1)
      | Conj(l1) ->
         List.iter fn l1
      | MAll(_,m1)
      | MExi(_,m1)
      | CAll(m1)
      | CExi(m1)
      | Next(m1) ->
         fn m1
      | VVar _ | Atom _ -> ()
      | HVar _ -> assert false
      | IVar _ -> assert false
    in
    let _ = List.iter fn ms in
    let indexes = Array.of_list (List.rev !res) in
    let names = Array.mapi (fun i _ -> "x" ^ string_of_int i) indexes in
    let index = create_symbol ctx.cgraph "I" names in
    (index, indexes)

  (** adds an induction hypothesis to the dedicated table *)
  let rec add_indhyp ms0 ms d adone =
    match ms with
    | [] -> assert (!(adone.leaf)=None); adone.leaf:=Some (d,ms0)
    | m::ms ->
       let tbl = adone.next in
       let key = debruijn m in
       let l = try TimedHashtbl.find tbl key with Not_found -> [] in
       let rec fn = function
         | [] ->
            let next = empty_tree () in
            add_indhyp ms0 ms d next;
            let l = (m, next)::l in
            TimedHashtbl.replace tbl key l
         | (m',next)::rest when ileq m m' = 0 ->
            add_indhyp ms0 ms d next;
         | _::rest ->
            fn rest
       in
       fn l

  (** Raised when an induction hypothesis applies *)
  exception Induction

  (** Try to apply the hyduction hypotheses in ctx to prove ms *)
  let check_rec ctx s1 =
    let s1 = List.sort ileq s1 in
    (** TODO: positivity context ?
              leq too strong ?, after all we can translate the variables.
              Equality up to time is however incorrect
                (replace leq with (fun x y -> ileq x y = 0) and test fails)
    *)
    let (caller, param) = ctx.indtop in
    let h = Array.length param in
    try
      let (hyp,s2), diag = patmatch ctx.indhyp s1 in
      let w = Array.length diag in
      Io.log_rec "s1 = %a\n" (lprint "\n     " print) s1;
      Io.log_rec "s2 = %a\n" (lprint "\n     " print) s2;
      Io.log_rec "diag %d x %a\n" w
                 (aprint " "
                         (fun ff t ->
                           Format.fprintf ff "%a" tprint t)) diag;
      Io.log_rec "Ind %d x %a\n%!" (Array.length param)
                 (aprint " " tprint) param;
      let matrix =
        let acc = ref [] in
        for i = h-1 downto 0 do
          Array.iteri (fun j t ->
              let c = cmp_time t param.(i) in
              if c <= Zero then acc := (i,j,c) :: !acc) diag
        done;
        !acc
      in
      Io.log_rec "m = (%a)\n%!" (lprint ", " (fun ff (i,j,c) ->
                                          Format.fprintf ff "(%d,%d,%a)" i j cprint c)) matrix;
      let call = { caller; callee=hyp; matrix } in
      add_call ctx.cgraph call;
      Chrono.add_time chr_scp sct ctx.cgraph;
      raise Induction
    with Not_found ->
      let (index,diag) = try mk_indhyp ctx s1 with Exit -> assert false in
      (*Io.log_rec "s0 = %a\n"
                 (lprint "\n     "
                         (fun ff m ->
                           Format.fprintf ff "%a" print m))
                 s1;*)
      let w = Array.length diag in
      (*Io.log_rec "Sub %d %a x %d %a\n\n%a\n\n%!" w (aprint " " tprint) diag
                 (Array.length param) (aprint " " tprint) param
                 (lprint "\n" print) s1;*)
      let matrix =
        let acc = ref [] in
        for i = h-1 downto 0 do
          for j = w-1 downto 0 do
            let c = cmp_time diag.(j) param.(i) in
            if c <= Zero then acc := (i,j,c) :: !acc
          done
        done;
        !acc
      in
      let call = { caller; callee=index; matrix } in
      add_call ctx.cgraph call;
      ignore (Chrono.add_time chr_add (add_indhyp s1 s1 index) ctx.indhyp);
      { ctx with indtop = (index, diag) }

  (** Simplify a formula [m] assuming [a] to be true *)
  let simplify a m =
    let a' = neg a in
    let rec simplify m =
      if leq a m then always'
      else if leq m a' then never'
      else
        match m.data with
        | Conj l -> _Conj (List.map simplify l)
        | Disj l -> _Disj (List.map simplify l)
        | _ -> m
    in
    let m = simplify m in
    if m == never' then raise Exit; m

  (** simplify a formula, knowing a sequent *)
  let seq_simplify s m =
    (** No need to simplify a Mu of Nu, they will be expanded *)
    match m.data with Mu _ | Nu _ -> m | _ ->
    let m = List.fold_left (fun m a -> simplify (atom' a) m) m s.atom in
    let m = List.fold_left (fun m (a,m') -> simplify (mAll' a m') m) m s.mAll in
    let m = List.fold_left (fun m (a,m') -> simplify (mExi' a m') m) m s.mExi in
    let m = List.fold_left (fun m m' -> simplify (cAll' m') m) m s.cAll in
    let m = List.fold_left (fun m m' -> simplify (cExi' m') m) m s.cExi in
    let m = List.fold_left (fun m m' -> simplify (next' m') m) m s.next in
    (** Simplification by blocked nu and disjunction are not worth it *)
    (*let m = List.fold_left (fun m m' -> simplify m' m) m s.disj in
      let m = List.fold_left (fun m m' -> simplify m' m) m s.blnu in
    *)
    (m:modal)

  (** simplify a sequent, knowing a formula, an accumulator ms is
      given, because some disjunction may be transformed in something
      else and need to be readded *)
  let simplify_seq ms m s =
    (** No need to simplify by conjunction, they will be splitted *)
    (** Simplification by disjunction is not worst it either *)
    match m.data with Conj _ | Disj _ -> (ms, s) | _ ->
    (** disjunction can be simplyfied by anything *)
    let disj = List.map (simplify m) s.disj in
    let (ms, disj) = List.fold_left (fun (ms, d) m' ->
                         match m'.data with
                         | Disj (_::_::_) -> (ms, m'::d)
                         | Disj _ -> assert false
                         | _ -> (m'::ms, d)) (ms, []) disj
    in
    let s = { s with disj } in
    match m.data with
    | Atom(a) ->
       let atom = List.filter (fun a' ->
                      if Prop.(imply a' (neg a)) then raise Exit;
                      not (Prop.imply a a')) s.atom
       in
       (ms, { s with atom })
    | MAll(a,m) ->
       let mAll = List.filter
                    (fun (a',m') -> not (Act.compare a a' = 0 && leq m m'))
                    s.mAll
       in
       let s = { s with mAll } in
       (ms, s)
    | MExi(a,m) ->
       let mExi = List.filter
                    (fun (a',m') -> not (Act.compare a a' = 0 && leq m m'))
                    s.mExi
       in
       let s = { s with mExi } in
       (ms, s)
    | CAll(m) ->
       let cAll = List.filter (fun m' -> not (leq m m')) s.cAll in
       let s = { s with cAll } in
       (ms, s)
    | CExi(m) ->
       let cExi = List.filter (fun m' -> not (leq m m')) s.cExi in
       let s = { s with cExi } in
       (ms, s)
    | Next m ->
       let next = List.filter (fun m' -> not (leq m m')) s.next in
       let s = { s with next } in
       (ms, s)
    | Disj _ | Mu _ | Nu _ | Conj _  ->
       (ms, s)
    | VVar _ | IVar _ | HVar _ -> assert false

  (** Add a list of formulas to a sequent *)
  let rec add_to_seq s ms =
    match ms with
    | [] -> s
    | m::ms ->
       let m = Chrono.add_time chr_simp (seq_simplify s) m in
       let (ms, s) = Chrono.add_time chr_simp (simplify_seq ms m) s in
       match m.data with
       | Atom a -> add_to_seq {s with atom = a::s.atom } ms
       | Conj l -> add_to_seq s (l@ms)
       | Disj [] -> raise Exit
       | Disj [m] -> add_to_seq s (m::ms)
       | Disj l ->
          add_to_seq { s with disj = m::s.disj } ms
       | Mu(t,i,f) ->
          let s = { s with posi = t::s.posi } in
          let (ubnu,blnu) =
            List.partition (fun m -> match m.data with Nu(t',_,_) ->
                                                       compare_time t t' = 0
                                                     | _ -> false) s.blnu
          in
          let s = { s with blnu } in
          let v = Array.init (mbinder_arity f) (fun i -> hashCons(Mu(pred m t,i,f))) in
          let m = (msubst f v).(i) in
          add_to_seq s (m::ubnu@ms)
       | Nu(t,i,f) when t == Inf
                     || List.exists (fun t0 -> compare_time t0 t = 0) s.posi ->
          let v = Array.init (mbinder_arity f) (fun i -> hashCons(Nu(pred' m t,i,f))) in
          let m = (msubst f v).(i) in
          add_to_seq s (m::ms)
       | Nu(t,i,f) ->
          add_to_seq { s with blnu = m :: s.blnu } ms
       | MAll(a,m) -> add_to_seq { s with mAll = (a,m)::s.mAll } ms
       | MExi(a,m) -> add_to_seq { s with mExi = (a,m)::s.mExi } ms
       | CAll(m) -> add_to_seq { s with cAll = m::s.cAll } ms
       | CExi(m) -> add_to_seq { s with cExi = m::s.cExi } ms
       | Next(m) ->
          add_to_seq { s with next = m::s.next } ms
       | VVar _ | IVar _ | HVar _ -> assert false


  exception Contradiction

  let len_one = function
      [] -> raise Contradiction
    | [_] -> true
    | _ -> false

  (** tests if a formula is contradictory *)
  let solver : modal -> bool = fun m ->
    Format.printf "original: %a\n\n%!" print m;
    let (tbl, m) = buildMap m in
    Format.printf "uniform:  %a\n\n%!" print m;
    ModalTbl.iter (fun m r -> Format.printf "%a\n\n" printModalInfo (m, r)) tbl;

    (** a reference to compute the progress in the problem *)
    let total = ref 0.0 in

    (** this function perform case analysis on formula appearing in a disjunction *)
    let rec case_analysis : float -> context -> seq -> clauses -> unit =
      Io.log_prg "\r%f %e %d    %!" !total f !(ctx.cgraph.next_index);
      fun f ctx seq clauses ->
        let rec unit_propagation seq clauses =
          let units, clauses = List.patitiion len_one clauses in
          if units = [] then (seq, clauses) else
          let seq = units @ seq in
          let clauses =
            List.filter (fun cl ->
                List.exists (fun l2 ->
                    List.exists (fun l1 -> implyLit l1 l2) units) cl) clauses in
          let nunits = List.map negList units in
          let clauses =
            List.map (fun cl ->
                List.filter (fun l2 ->
                        List.exists (fun l1 -> implyLit l1 l2) nunits) cl) clauses in
          unit_propagation seq clauses
        in
        let seq, clausess = unit_propagation seq clauses in
        match clauses with
        | [] -> time_analysis float context clauses
        | (l::_)::_ ->
           let f = f /. 2.0 in
           try
             Io.log_sat "case %a\n%!" print_litteral l;
             case_analysis f ctx (l::seq) clauses
           with Contradiction ->
             Pervasives.(total := !total +. f);
             let l = negLit l in
             Io.log_sat "case %a\n%!" print_litteral l;
             case_analysis f ctx (l::seq) clauses
        | _  -> Format.eprintf "%a\n%!" print m; assert false

    (** when case analysis is finished, we look what happens in the next state *)
    and time_analysis : float -> context -> seq -> bool = fun f ctx s ->
      let nexts = ref [] in
      let calls = ref [] in
      let cexis = ref [] in
      let malls = ref [] in
      let mexis = ref [] in
      List.iter (function
                 | LAtom _ | LNeg _ | LPos (Conj _) -> ()
                 | LPos (LNext m) -> nexts := m :: ! nexts
                 | LPos (LCAll m) -> calls := m :: ! calls
                 | LPos (LCExi m) -> cexis := m :: ! cexis
                 | LPos (LMAll (a,m)) -> malls := (a,m) :: ! malls
                 | LPos (LMExi (a,m)) -> mexis := (a,m) :: ! mexis) seq;


      let s0 = { empty_seq with posi = s.posi } in
      (** Common code for all case analysis *)
      let rec next_time : float -> context -> modal list -> bool = fun f ctx ms ->
        let ms = List.filter has_no_nu_deco ms in
        if ms = [] then false else
        try
          let ctx = check_rec ctx ms in
          case_analysis f ctx s0 ms
        with
        | Induction -> Io.log_sat "INDUCTION\n%!"; Pervasives.(total := !total +. f); true
        | Loop -> Io.log_sat "LOOP\n%!"; false
      in
      let nb =
        let i = if s.next = [] then 0 else 1 in
        i + List.length s.mExi + List.length s.cExi
      in
      let f = f /. float nb in
      List.exists (fun (a,m) ->
          pure_test (fun () ->
              Io.log_sat "pa %a |-\n%!" print_seq (s, []);
              let ms = List.filter (fun (a',m) -> a = a') s.mAll in
              let ms = List.map snd ms @ s.cAll in
              let ms = m::ms in
              next_time f ctx ms
            ) ()
        ) s.mExi
      ||
        List.exists (fun m ->
            pure_test (fun () ->
                Io.log_sat "pn %a |-\n%!" print_seq (s, []);
                next_time f ctx (m :: s.cAll)) ()) s.cExi
      ||
        pure_test (fun () ->
            Io.log_sat "pn %a |-\n%!" print_seq (s, []);
            next_time f ctx s.next) ()
    in

    let ctx = empty_ctx () in
    let params = collect_initial m in
    let clauses = ModalTbl.find tbl m in
    let run () = Chrono.add_time chr_solve (case_analysis 100.0 ctx empty_seq) (clauses,params) in
    let time = ref 0.0 in
    let rt t = time := t in
    let res = Chrono.time rt run () in
    Io.log_prg "\r                                                \r%!";
    Chrono.iter (Io.log_tim "%8s: %fs %d\n");
    Io.log_tim "   total: %fs\n%!" !time;
    res

  let _ = Printexc.record_backtrace true

  let prove m0 =
    try
      Io.log_ver "PROVING: %a\n%!" print m0;
      let res = solver (neg m0) in
      Format.printf (if res then "valid\n%!" else "invalid\n%!");
      res
    with
    | e ->
       Printexc.print_backtrace stderr;
       raise e

  let sat m0 =
    try
      Io.log_ver "CHECKING SAT: %a\n%!" print m0;
      let res = solver m0 in
      Format.printf (if res then "unsatifiable\n%!" else "satifiable\n%!");
      res
    with
    | e ->
       Printexc.print_backtrace stderr;
       raise e

end
