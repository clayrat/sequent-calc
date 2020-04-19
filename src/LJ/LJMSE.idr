module LJ.LJMSE

import Data.List
import Data.List.Quantifiers
import Subset
import Iter
import Lambda.STLC.Ty

%default total
%access public export

mutual
  data Term : List Ty -> Ty -> Type where
    Var  : Elem a g -> Term g a
    Lam  : Term (a::g) b -> Term g (a~>b)
    RSel : Cmd g a -> Term g a

  data CoTerm : List Ty -> Ty -> Ty -> Type where
    Nil  : CoTerm g a a
    Cons : Term g a -> CoTerm g b c -> CoTerm g (a~>b) c
    LSel : Cmd (a::g) b -> CoTerm g a b

  data Cmd : List Ty -> Ty -> Type where
    Cut : Term g a -> CoTerm g a b -> Cmd g b

mutual
  renameTerm : Subset g d -> Term g a -> Term d a
  renameTerm sub (Var el) = Var (sub el)
  renameTerm sub (Lam t)  = Lam (renameTerm (ext sub) t)
  renameTerm sub (RSel c) = RSel (renameCmd sub c)

  renameCoTerm : Subset g d -> CoTerm g a b -> CoTerm d a b
  renameCoTerm sub  Nil       = Nil
  renameCoTerm sub (Cons t k) = Cons (renameTerm sub t) (renameCoTerm sub k)
  renameCoTerm sub (LSel c)   = LSel (renameCmd (ext sub) c)

  renameCmd : Subset g d -> Cmd g a -> Cmd d a
  renameCmd sub (Cut t k) = Cut (renameTerm sub t) (renameCoTerm sub k)
