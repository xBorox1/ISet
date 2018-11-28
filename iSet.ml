(*
 * ISet - Interval sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl, Jacek Chrzaszcz, Michal Borowski
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

(** Interval Set.

    This is an interval set, i.e. a set of integers, where large
    intervals can be stored as single elements. Intervals stored in the
    set are disjoint. 

*)

(* Autor : Michał Borowski *)
(* Code Reviewer : Michał Makowski *)

(*************************)
(*          TYPY         *)
(*************************)

(* Typ reprezentujący przedział jako jego lewy i prawy kraniec. lewy <= prawy *)
type interval = int * int

(* Typ reprezentujący zbiór jako drzewo AVL przedziałów. Najdłuższa ścieżka od korzenia do liścia *)
(* jest maksymalnie o 2 większa od najkrótszej. *)
(* t = lewe poddrzewo * przedział * prawe poddrzewo * wysokość drzewa * suma długości przedziałów *)
(* LUB *)
(* Puste drzewo *)
type t =
        | Node of t * interval * t * int * int
        | Empty

(*************************)
(*         STAŁE         *)
(*************************)

let empty = Empty

let bad_interval = (1, -1)

(*************************)
(*FUNKCJE NA PRZEDZIAŁACH*)
(*************************)

(* Sprawdza czy wartość v jest w przedziale [x, y]. *)
let val_in_interval v (x, y) =
        x <= v && v <= y

(* Sprawdza czy jeden przedział zawiera się w drugim. *)
let interval_in_interval (x, y) (x2, y2) =
        x2 <= x && y <= y2

(* Liczba liczb całkowitych w przedziale. *)
let length (x, y) =
        let l = y - x + 1 in
        if l <= 0 then max_int else l

(*************************)
(* SELEKTORY PODSTAWOWE  *)
(*************************)

let height = function
        | Empty -> 0
        | Node (_, _, _, h, _) -> h

let sum = function
        | Empty -> 0
        | Node (_, _, _, _, s) -> s

(*************************)
(*      KONSTRUKTORY     *)
(*************************)

(* Tworzy drzewo składające się z jednego przedziału. *)
let element k = Node(Empty, k, Empty, 1, length k)

(* Funkcja tworząca drzewo mając wartość, lewe i prawe poddrzewo. *)
(* Zakładamy, że argumenty są takie, że wynikowe drzewo jest AVL. *)
let make l k r =
        let s = length k + sum l + sum r in
        let sm = if s <= 0 then max_int else s
        in
        Node (l, k, r, max (height l) (height r) + 1, sm)

(*************************)
(*  FUNKCJE POMOCNICZE   *)
(*************************)

(* Balansuje drzewo, czyli przekształca je tak aby spełniało warunek AVL. *)
(* Podane poddrzewa mają różnice wysokości co najwyżej 3. *)
let bal l k r =
        let hl = height l in
        let hr = height r in
        if hl > hr + 2 then
                match l with
                        | Node (ll, lk, lr, _, _) ->
                        if height ll >= height lr then make ll lk (make lr k r)
                        else
                                (match lr with
                                | Node (lrl, lrk, lrr, _, _) ->
                                make (make ll lk lrl) lrk (make lrr k r)
                                | Empty -> assert false)
                        | Empty -> assert false
        else if hr > hl + 2 then
                match r with
                        | Node (rl, rk, rr, _, _) ->
                        if height rr >= height rl then make (make l k rl) rk rr
                        else
                                (match rl with
                                | Node (rll, rlk, rlr, _, _) ->
                                make (make l k rll) rlk (make rlr rk rr)
                                | Empty -> assert false)
                        | Empty -> assert false
        else make l k r

(* Najmniejszy element w drzewie. *)
let rec min_elt = function
  | Node (Empty, k, _, _, _) -> k
  | Node (l, _, _, _, _) -> min_elt l
  | Empty -> raise Not_found

(* Usuwa najmniejszy element z drzewa. *)
let rec remove_min_elt = function
  | Node (Empty, _, r, _, _) -> r
  | Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "ISet.remove_min_elt"

(* Łączy 2 drzewa, które można złączyć w drzewo AVL jednym balansowaniem. *)
let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      bal t1 k (remove_min_elt t2)

(*************************)
(*  OPERACJE NA DRZEWIE  *)
(*************************)

(* Funkcja dodająca przedział k przy założeniu, że żadne *)
(* wartości z przedziału k nie znajdują się w tym drzewie. *)
let rec add_el k set =
        match set with
        | Empty -> element k
        | Node(l, k2, r, _, _) ->
                if k < k2 then bal (add_el k l) k2 r
                else bal l k2 (add_el k r)

(* Usuwa przedział, który w całości zawiera się w danym drzewie. *)        
let rec remove_exist (x, y) set =
        match set with
        | Empty -> invalid_arg "ISet.remove_exist"
        | Node (l, (setx, sety), r, _, _) ->
                if interval_in_interval (x, y) (setx, sety) then
                        let ll = if x = setx then l else add_el (setx, x - 1) l in
                        let rr = if y = sety then r else add_el (y + 1, sety) r in
                        merge ll rr
                else if (x, y) < (setx, sety) then bal (remove_exist (x, y) l) (setx, sety) r
                else bal l (setx, sety) (remove_exist (x, y) r)

let rec remove (x, y) set =
        (* Funkcja pomocnicza, znajduje przedziały do usuwania. *)
        let rec find_next (x, y) set =
                match set with
                | Empty -> bad_interval
                | Node(l, (setx, sety), r, _, _) ->
                        if interval_in_interval (x, y) (setx, sety) then (x, y)
                        else if interval_in_interval (setx, sety) (x, y) then (setx, sety)
                        else if y < setx then find_next (x, y) l
                        else if x <= setx then (setx, y)
                        else if x <= sety then (x, sety)
                        else find_next (x, y) r
        in
                let k = find_next (x, y) set in
                if k = bad_interval then set
                else remove (x, y) (remove_exist k set)

let add (x, y) set =
        (* Znajduje przedział ze zbioru zawierający daną wartość, jeśli taki istnieje. *)
        let rec find_val v set =
                match set with
                | Empty -> bad_interval
                | Node(l, (setx, sety), r, _, _) ->
                        if v < setx then find_val v l
                        else if v > sety then find_val v r
                        else (setx, sety)
        in
                let (l1, r1) = if x = min_int then bad_interval else find_val (x - 1) set
                in let (l2, r2) = if y = max_int then bad_interval else find_val (y + 1) set 
                in
                let x2 = if (l1, r1) = bad_interval then x else l1 in
                let y2 = if (l2, r2) = bad_interval then y else r2 in
                let set2 = remove (x2, y2) set in
                add_el (x2, y2) set2

(* Równoważy drzewo spełniające warunek BST, o zrównoważonych poddrzewach. *)
let rec join l v r =
  match (l, r) with
    (Empty, _) -> add_el v r
  | (_, Empty) -> add_el v l
  | (Node(ll, lv, lr, lh, _), Node(rl, rv, rr, rh, _)) ->
      if lh > rh + 2 then bal ll lv (join lr v r) else
      if rh > lh + 2 then bal (join l v rl) rv rr else
      make l v r

let split x set =
  let rec loop x = function
    |  Empty ->
        (Empty, false, Empty)
    | Node (l, v, r, _, _) ->
        if val_in_interval x v then
              let (setx, sety) = v in
              let ll = if x = setx then l else add_el (setx, x - 1) l in
              let rr = if x = sety then r else add_el (x + 1, sety) r in
              (ll, true, rr)
        else if (x, x) < v then
          let (ll, pres, rl) = loop x l in (ll, pres, join rl v r)
        else
          let (lr, pres, rr) = loop x r in (join l v lr, pres, rr)
  in
  let setl, pres, setr = loop x set in
  setl, pres, setr

(*************************)
(*OPERACJE NA ELEMENTACH *)
(*************************)

let is_empty t =
        t = Empty
        
let mem v set =
        let rec loop = function
          | Node (l, (x, y), r, _, _) ->
                 (val_in_interval v (x, y)) || loop (if v < x then l else r)
          | Empty -> false in
        loop set

let elements set = 
        let rec loop acc = function
                | Empty -> acc
                | Node(l, k, r, _, _) -> loop (k :: loop acc r) l in
        loop [] set

let iter f set =
        let rec loop = function
                | Empty -> ()
                | Node (l, k, r, _, _) -> loop l; f k; loop r in
        loop set

let fold f set acc =
        let rec loop acc = function
                | Empty -> acc
                | Node (l, k, r, _, _) ->
                        loop (f k (loop acc l)) r in
        loop acc set

let below x set = 
        let rec below_helper x set acc =
                match set with
                | Empty -> if acc < 0 then max_int else acc
                | Node (l, (setx, sety), r, _, _) ->
                        if x < setx then below_helper x l acc
                        else if x > sety then below_helper x r (acc + sum l + length (setx, sety))
                        else 
                                let ans = acc + sum l + length (setx, x) in 
                                if ans <= 0 then max_int else ans
        in
                below_helper x set 0
