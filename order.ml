(** general functions related to ordring and comparison *)

let lex2 fa a1 a2 fb b1 b2 =
  match fa a1 a2 with
  | 0 -> fb b1 b2
  | c -> c

let lex3 fa a1 a2 fb b1 b2 fc c1 c2 =
  match fa a1 a2 with
  | 0 -> lex2 fb b1 b2 fc c1 c2
  | c -> c

let lex4 fa a1 a2 fb b1 b2 fc c1 c2 fd d1 d2 =
  match fa a1 a2 with
  | 0 -> lex3 fb b1 b2 fc c1 c2 fd d1 d2
  | c -> c

let rec lexl f l1 l2 =
  match l1, l2 with
  | []     , []      ->  0
  | []     , _       ->  1
  | _      , []      -> -1
  | m1::ms1, m2::ms2 -> lex2 f m1 m2 (lexl f) ms1 ms2
