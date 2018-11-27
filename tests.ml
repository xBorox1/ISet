#load "iSet.cmo";;
open ISet;;
open List;;

let m = 1000000000;;

let random_list size =
        Random.self_init();
        let rec helper size acc las =
                if size = 0 then acc
                else 
                        let x = Random.int m + las in
                        let y = Random.int m + x in
                        helper (size - 1) ((x,y)::acc) y
        in
        helper size [] (-1) |> rev;;

let random_permutation lst =
        Random.self_init();
        let lst2 = map (fun h -> (Random.bits (), h)) lst in
        let random_lst2 = sort compare lst2 in
        map (fun (a, h) -> h) random_lst2;;

let add_list lst =
        fold_left (fun tr k -> add k tr) empty lst;;

let rec testuj_add_elements sizet sizel =
        if sizet = 0 then true
        else 
                let l = random_list sizel in
                let per = random_permutation l in
                let tr = add_list per in
                elements tr = l && (testuj_add_elements (sizet - 1) sizel);;


let nieparzyste size =
        let rec helper n acc =
                if n < 0 then acc
                else helper (n - 2) ((n, n)::acc) in
        helper size [];;

let nieparzyste_tr size = add_list (nieparzyste size);;

let randxy x y =
        Random.self_init();
        (Random.int (y - x + 1)) + x;;

let usun_z_np (x, y) tr =
        let tr2 = remove (x, y) tr in
        not (ISet.mem (randxy x y) tr2);;

let dodaj_do_np (x, y) tr =
        let tr2 = add (x, y) tr in
        ISet.mem (randxy x y) tr2;;

let testuj_np sizet sizetr =
        Random.self_init() ;
        let tr = nieparzyste_tr sizetr in
        let rec helper sizet tree =
                if sizet = 0 then true
                else
                let a = Random.int 2 in
                let x = Random.int sizetr in
                let y = Random.int 10 + x in
                let (b, tr2) = if a = 1 then ((dodaj_do_np (x, y) tree), (add (x, y) tree))
                        else ((usun_z_np (x, y) tree), (remove (x, y) tree)) in
                (b && (helper (sizet - 1) tr2))
         in
                helper sizet tr;;
                
let testuj_below sizel =
        let tr = nieparzyste_tr sizel in
        let rec testuj n =
                if n = 0 then true
                else ((below n tr) = ((n - 1) / 2) + 1) && (testuj (n - 1))
        in
                testuj sizel;;

let testuj_split sizel =
        Random.self_init() ;
        let tr = nieparzyste_tr sizel in
        let rec testuj n tr =
                if n = 0 then true
                else
                        let x = (Random.int (2 * (below sizel tr) - 1)) + 1 in
                        let y = (Random.int x) + 1 in
                        let (tr2, p, _) = (ISet.split x tr) in
                        let p2 = (x mod 2 = 1) in
                        let tr2 = if p2 then (add (x, x) tr2) else tr2 in
                        ((below y tr2) = ((y - 1) / 2) + 1) && (p = p2) && ((ISet.mem x tr) = p2) &&
                        (testuj (n - 1) tr2)
        in
                testuj sizel tr;;

let random_tree size =
        add_list (random_list size);;



let x = empty;;
assert(is_empty x = true);;
let x = add (1, 2) x;;
assert(is_empty x = false);;
assert(is_empty (remove (1, 2) x) = true);;
let x = remove (1, 1) x;;
assert(is_empty x = false);;
let x = remove (2, 2) x;;
assert(is_empty x = true);;
let x = add (1, 1) empty;;
let x = add (3, 3) x;;
let x = add (5, 5) x;;
assert(is_empty (remove (1, 5) x) = true);;
let x = add (2, 4) x;;
assert(is_empty x = false);;
let x = remove (1, 5) x;;
assert(is_empty x = true);;

assert( testuj_add_elements 1 100000 = true);;
assert( testuj_add_elements 100 1000 = true);;

let tr = random_tree 100000;;
assert( (fold (fun (x, y) acc -> acc + x + y) tr 0) = (fold_left (fun acc (x, y) -> acc + x + y) 0 (elements tr)));;
assert( (fold (fun (x, y) acc -> (x + y)::acc) tr [] = fold_left (fun acc (x, y) -> (x + y)::acc) [] (elements tr)));;


assert( (testuj_np 1000 99999) = true );;
assert( (testuj_np 10 99999) = true );;
assert( (testuj_np 100 99999) = true );;

assert((testuj_below 999) = true);;

assert((testuj_split 99999) = true);;

let a = ref 0;;

let f_it1 =
        fun _ -> begin
                a := !a + 1;
        end;;

let tr = nieparzyste_tr 901;;
ISet.iter (f_it1) tr;;
assert(!a = 451);;

let b = ref [];;

let f_it2 =
        fun k -> begin
                b := k::(!b);
        end;;

ISet.iter (f_it2) tr;;
assert((elements tr) = (rev !b) );;

let tr = add (min_int, max_int) empty;;
assert(below 6 tr = max_int);;
