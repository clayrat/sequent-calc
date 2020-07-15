module Elem

import Data.Fin
import Data.List
import Data.List.Elem

%default total

public export
elem2Nat : Elem a g -> Nat
elem2Nat  Here      = Z
elem2Nat (There el) = S (elem2Nat el)

public export
elem2Fin : Elem a g -> Fin (length g)
elem2Fin  Here      = FZ
elem2Fin (There el) = FS (elem2Fin el)

public export
fin2Elem : (xs : List a) -> Fin (length xs) -> (x ** Elem x xs)
fin2Elem (x::xs)  FZ    = (x ** Here)
fin2Elem (x::xs) (FS f) = let (x ** p) = fin2Elem xs f in
                          (x ** There p)

public export
dropWithElem : (g : List t) -> Elem a g -> List t
dropWithElem (x::xs)  Here      = xs
dropWithElem (x::xs) (There el) = dropWithElem xs el

public export
addToElem : {d : List t} -> (n : Nat) -> Elem a (drop n d) -> Elem a d
addToElem           Z    el = el
addToElem {d=[]}   (S n) el = absurd el
addToElem {d=x::d} (S n) el = There $ addToElem n el
