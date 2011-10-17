
let mapl =
 mod
  write
   (fun_c f(x) is
    let imapl X args = x in
    read imapl as imap in 
    let f X l = args in
    case l of
    { inl (mt) => inl (),
      inr (cons) =>
       let hd X tl = cons in
        inr (apply_s(f,hd), apply_c(imap,(imapl,(f,tl))) )
    })
in
let l1l =
 mod
  write
   (inr (1, (inr (2, (inr (3, (inr (4, inl ()))))))))
in
let f =
 (fun_s f(x) is
  x + 1)
in
let ansl =
 mod
  read mapl as map in
  read l1l as l1 in
  let ans = apply_c(map, (mapl,(f,l1))) in
  write ans
in

ansl
