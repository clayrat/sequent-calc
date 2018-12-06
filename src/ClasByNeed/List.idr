module ClasByNeed.Identifier

import Control.Monad.Syntax
import Control.Monad.State

%default total
%access public export

infixl 5 |>
(|>) : List a -> a -> List a
xs |> x = xs ++ [x]

{-
data ViewL a = EmptyL | ConsL a (List a)

viewl : List a -> ViewL a
viewl []      = EmptyL
viewl (x::xs) = ConsL x xs
-}

-- TODO indexed view
data ViewR a = EmptyR | ConsR (List a) a

viewr : List a -> ViewR a
viewr     []    = EmptyR
viewr xs@(_::_) = ConsR (init xs) (last xs)

split : (a -> Bool) -> List a -> Maybe (List a, a, List a) 
split p xs = case break p xs of
  (left, [])       => Nothing
  (left, x::right) => Just (left, x, right)


