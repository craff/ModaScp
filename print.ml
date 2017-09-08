let rec lprint sep pr ff = function
  | [] -> ()
  | [x] -> pr ff x
  | x::l -> Format.fprintf ff "%a%s%a" pr x sep (lprint sep pr) l

let sprint ff = Format.fprintf ff "%s"

let aprint sep pr ff a = lprint sep pr ff (Array.to_list a)
