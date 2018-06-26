open Bindlib
open Modal


module Act = struct
  type t = int
  let compare = compare
  let to_string = string_of_int
end

module Prop = struct
  type t = bool * int
  let compare = Pervasives.compare
  let imply = (=)
  let neg (b,n) = (not b,n)
  let to_string (b,n) = Printf.sprintf "(%b,%d)" b n
end

module Modal = Modal.Make(Act)(Prop)

open Modal

let _ = Io.set_debug (if Array.length Sys.argv >= 2 then Sys.argv.(1) else "")

let test2 =
  let f1 = unbox (nu 0 1 (fun x -> [|conj [mAll 0 x.(0); mAll 1 x.(0)]|])) in
  let f2 = unbox (nu 0 1 (fun x -> [|mAll 0 x.(0)|])) in
  assert (prove (imply f1 f2))

let test1 =
  let f1 = unbox (mu 0 1 (fun x -> [|mAll 0 x.(0)|])) in
  let f2 = unbox (nu 0 1 (fun x -> [|mAll 0 x.(0)|])) in
  assert (prove (imply f1 f2))

let test3 =
  let f1 = unbox (nu 0 2 (fun x -> [|mAll 0 x.(0); mAll 1 x.(1)|])) in
  let f2 = unbox (nu 1 2 (fun x -> [|mAll 1 x.(0); mAll 0 x.(1)|])) in
  assert (prove (imply f1 f2))

open FiniteAutomata

let abn =
  { num_states = 3
  ; init = 0
  ; transitions = [(0,"a",1); (1,"b",0); (0,"EOF",2)]
  }

let aan =
  { num_states = 2
  ; init = 0
  ; transitions = [(0,"a",0); (0,"EOF",1)]
  }

let abn2 =
  { num_states = 5
  ; init = 0
  ; transitions = [(0,"a",1); (1,"b",2);(2,"a",3); (3,"b",0); (0,"EOF",4); (2,"EOF",4)]
  }

let abn3 =
  { num_states = 7
  ; init = 0
  ; transitions = [(0,"a",1); (1,"b",2);(2,"a",3); (3,"b",4);(4,"a",5);(5,"b",0)
                  ;(0,"EOF",6); (2,"EOF",6); (4,"EOF",6)]
  }

let f = to_nu abn

let k = to_nu aan

let g = to_nu abn2

let h = to_nu abn3

let _ = Format.printf "f = %a\n%!" Modal.print f
let _ = Format.printf "k = %a\n%!" Modal.print k
let _ = Format.printf "g = %a\n%!" Modal.print g
let _ = Format.printf "h = %a\n%!" Modal.print h

let _ = assert (not (prove (imply f k)))
let _ = assert (not (prove (imply k f)))

let _ = assert (prove (imply f g))
let _ = assert (prove (imply g f))

let _ = assert (prove (imply h g))
let _ = assert (prove (imply g h))

let rec conjs ?(cond=(fun _ -> true)) n f =
  let rec fn acc n =
    if n <= 0 then acc else
      if cond n then fn (f n :: acc) (n-1) else fn acc (n-1)
  in
  conj (fn [] n)

let rec disjs ?(cond=(fun _ -> true)) n f =
  let rec fn acc n =
    if n <= 0 then acc else
      if cond n then fn (f n :: acc) (n-1) else fn acc (n-1)
  in
  disj (fn [] n)

let psi n = nu1 (fun x ->
  conj [next x;
        disjs n (fun i ->
                conj [atom (true,i);
                      conjs ~cond:(fun j -> i <> j) n (fun j -> atom (false,j))])])

let even i = i mod 2 = 0
let odd i = i mod 2 <> 0

let phi n0 =
  let rec a l n =
    if n = 0 then
      conjs n0 (fun i -> imply' (atom (true, i)) (next (List.nth l (i-1))))
    else
      let q = if even n then nu1 else mu1 in
      q (fun x ->  a (x::l) (n - 1))
  and b =
    disj [disjs ~cond:even n0 (fun i ->
           conj [nu1 (fun x -> conj [next x; mu1 (fun y -> disj [atom (true, i); next y])]);
                 conjs ~cond:(fun j -> odd j && j > i) n0 (fun j ->
                         mu1 (fun x -> disj [next x; nu1 (fun y -> conj [atom (false, j); next y])]))]);
          conjs ~cond:(fun j -> odd j) n0 (fun j ->
                         mu1 (fun x -> disj [next x; nu1 (fun y -> conj [atom (false, j); next y])]))]
  in
  unbox (imply' (psi n0) (equiv (a [] n0) b))

let sphi n0 =
  let rec a l n =
    if n = 0 then
      conjs n0 (fun i -> imply' (atom (true, i)) (next (List.nth l (i-1))))
    else
      let q = if even n then nu1 else mu1 in
      q (fun x ->  a (x::l) (n - 1))
  and b =
    disj [disjs ~cond:even n0 (fun i ->
           conj [nu1 (fun x -> conj [next x; mu1 (fun y -> disj [atom (true, i); next y])]);
                 conjs ~cond:(fun j -> odd j && j > i) n0 (fun j ->
                         mu1 (fun x -> disj [next x; nu1 (fun y -> conj [atom (false, j); next y])]))]);
          conjs ~cond:(fun j -> odd j) n0 (fun j ->
                         mu1 (fun x -> disj [next x; nu1 (fun y -> conj [atom (false, j); next y])]))]
  in
  unbox (equiv (a [] n0) b)

let bad_phi n0 =
  let rec a l n =
    if n = 0 then
      conjs n0 (fun i -> imply' (atom (true, i)) (next (List.nth l (i-1))))
    else
      let q = if even n then nu1 else mu1 in
      q (fun x ->  a (x::l) (n - 1))
  and b =
    disj [disjs ~cond:even n0 (fun i ->
           conj [nu1 (fun x -> conj [next x; mu1 (fun y -> disj [atom (true, i); next y])]);
                 conjs ~cond:(fun j -> even j && j > i) n0 (fun j ->
                         mu1 (fun x -> disj [next x; nu1 (fun y -> conj [atom (false, j); next y])]))]);
          conjs ~cond:(fun j -> even j) n0 (fun j ->
                         mu1 (fun x -> disj [next x; nu1 (fun y -> conj [atom (false, j); next y])]))]
  in
  unbox (imply' (psi n0) (equiv (a [] n0) b))

let _ =
  for i = 1 to 5 do
    Format.printf "bad_phi %d\n%!" i;
    assert (not (prove (bad_phi i)))
  done

let _ =
  for i = 1 to 5 do
    Format.printf "sphi %d\n%!" i;
    assert (not (prove (sphi i)))
  done

let _ =
  for i = 1 to 5 do
    Format.printf "phi %d\n%!" i;
    assert (prove (phi i))
  done


let inverse p1 =
  let a = Array.make (List.length p1) (0,false) in
  List.iteri (fun j (i,b) -> a.(i-1) <- (j+1,b)) p1;
  Array.to_list a

let munus ls0 =
  let ls1 = inverse ls0 in
  let n0 = List.length ls0 in
  let rec a l ls =
    match ls with
    | [] ->
       let l = List.rev l in
      conjs n0 (fun i -> imply' (atom (true, i)) (next (List.nth l (fst (List.nth ls1 (i-1)) - 1))))
    | (_,b)::ls ->
      let q = if b then mu1 else nu1 in
      q (fun x ->  a (x::l) ls)
  in
  unbox (a [] ls0)

let munus2 ls1 ls2 =
  let n0 = List.length ls1 in (* psi useless in fact ... *)
  imply (unbox (psi n0)) (imply (munus ls1) (munus ls2))

let rec permutations : 'a list -> 'a list list = function
  | []  -> []
  | [x]   -> [[x]]
  | l   ->
      let aux x =
        let lmx = List.filter (fun y -> y <> x) l in
        List.map (fun l -> x::l) (permutations lmx)
      in
      List.concat (List.map aux l)

let rec choice : 'a list -> ('a * bool) list list = function
  | []    -> []
  | [x]   -> [[(x,true)]; [(x,false)]]
  | x::xs -> let l = choice xs in
             let lxtru = List.map (fun l -> (x,true)::l) l in
             let lxfls = List.map (fun l -> (x,false)::l) l in
             lxtru @ lxfls

let test_permutations p1 p2 =
  let aux (i, is_mu1) =
    let is_mu2 = List.assoc i p2 in
    is_mu1 || not is_mu2
  in
  List.for_all aux p1 &&
  let aux = function
    | (i, true ) -> true
    | (i, false) ->
        let rec right_mu_of i = function
          | []   -> []
          | j::r when fst j = i -> List.map fst (List.filter (fun (_,b) -> b) r)
          | j::r -> right_mu_of i r
        in
        let left_mu_of i p =
          let rec left_mu acc = function
            | []   -> assert false
            | j::r when fst j = i -> List.rev_map fst acc
            | j::r -> left_mu (if snd j then j::acc else acc) r
          in left_mu [] p
        in
        let right_mu = right_mu_of i p1 in
        let left_mu = left_mu_of i p2 in
        List.for_all (fun e -> not (List.mem e left_mu)) right_mu
  in
  List.for_all aux p1

let print_perm =
  Print.lprint "" (fun ff (i,b) ->
                 let q = if b then "μ" else "ν" in
                 Format.fprintf ff "%sX%d" q i)

let test size =
  let permutations = permutations (Array.to_list (Array.init size (fun i -> i+1))) in
  let right_perm = List.concat (List.map choice permutations) in

  let left_perm = choice (Array.to_list (Array.init size (fun i -> i+1))) in

  List.iter (fun p1 -> List.iter (fun p2 ->
                           Format.eprintf "%a => %a\n%!" print_perm p1 print_perm p2;
    assert (prove (munus2 p1 p2) = test_permutations p1 p2)
  ) right_perm) left_perm

let _ =
  for i = 1 to 3 do
    test i
  done

  (*
  PROVED: (

ν(M0)_0.(μ(M1)_0.((((true,1) ∧ OM1) ∨ ((true,2) ∧ OM0)))) ∨
ν(M0)_0.(μ(M1)_0.((((false,1) ∨ OM0) ∧ ((false,2) ∨ OM1))))

mu X nu Y < nu Y mu X
 ∨ μ(M0)_0.(((((false,1) ∨ (true,2)) ∧ ((false,2) ∨ (true,1))) ∨ OM0)))

PROVED: (


μ(M0)_0.(μ(M1)_0.(ν(M2)_0.((((false,1) ∨ OM2) ∧ ((false,2) ∨ OM0) ∧ ((false,3) ∨ OM1))))))
nu Y nu Z mu X
<
nu Z nu Y mu X
ν(M0)_0.(ν(M1)_0.(μ(M2)_0.((((true,1) ∧ OM2) ∨ ((true,2) ∧ OM1) ∨ ((true,3) ∧ OM0))))) ∨

μ(M0)_0.(((((false,1) ∨ (true,2) ∨ (true,3)) ∧ ((false,2) ∨ (true,1) ∨ (true,3)) ∧ ((false,3) ∨ (true,1) ∨ (true,2))) ∨ OM0)) ∨

PROVED: (

μ(M0)_0.(μ(M1)_0.(ν(M2)_0.((((false,1) ∨ OM2) ∧ ((false,2) ∨ OM0) ∧ ((false,3) ∨ OM1))))))
nu Y nu Z mu X
<
nu Z nu Y mu X
ν(M0)_0.(ν(M1)_0.(μ(M2)_0.((((true,1) ∧ OM2) ∨ ((true,2) ∧ OM1) ∨ ((true,3) ∧ OM0)))))


 ∨ μ(M0)_0.(((((false,1) ∨ (true,2) ∨ (true,3)) ∧ ((false,2) ∨ (true,1) ∨ (true,3)) ∧ ((false,3) ∨ (true,1) ∨ (true,2))) ∨ OM0)) ∨

let inverse p1 =
  let a = Array.make (List.length p1) (0,false) in
  List.iteri (fun j (i,b) -> a.(i-1) <- (j+1,b)) p1;
  Array.to_list a

PROVED: (

 μ(M0)_0.(μ(M1)_0.(ν(M2)_0.((((false,1) ∨ OM2) ∧ ((false,2) ∨ OM0) ∧ ((false,3) ∨ OM1))

 nu Y nu Z mu X
<
 nu Z nu Y mu X

ν(M0)_0.(ν(M1)_0.(μ(M2)_0.((((true,1) ∧ OM2) ∨ ((true,2) ∧ OM1) ∨ ((true,3) ∧ OM0))))) ∨


 μ(M0)_0.(((((false,1) ∨ (true,2) ∨ (true,3)) ∧ ((false,2) ∨ (true,1) ∨ (true,3)) ∧ ((false,3) ∨ (true,1) ∨ (true,2))) ∨ OM0)) ∨

   *)
