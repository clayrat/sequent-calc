module L.Scherer.Subset

import Data.List

%access public export
%default total

Subset : List a -> List a -> Type
Subset {a} xs ys = {x : a} -> Elem x xs -> Elem x ys

data IsSubset : List a -> List a -> Type where 
  Id    :                 IsSubset           l            l    
  ConsR : IsSubset l m -> IsSubset           l  (      a::m) 
  Cons2 : IsSubset l m -> IsSubset (      a::l) (      a::m) 
  Swap  : IsSubset l m -> IsSubset (   a::b::l) (   b::a::m)
  Rot   : IsSubset l m -> IsSubset (a::b::c::l) (c::a::b::m)  

shift : IsSubset l m -> Subset l m  
shift  Id        el                        = el
shift (ConsR s)  el                        = There $ shift s el
shift (Cons2 s)  Here                      = Here
shift (Cons2 s) (There  el)                = There $ shift s el 
shift (Swap s)   Here                      = There Here
shift (Swap s)  (There  Here)              = Here
shift (Swap s)  (There (There el))         = There $ There $ shift s el
shift (Rot s)    Here                      = There Here
shift (Rot s)   (There  Here)              = There $ There Here
shift (Rot s)   (There (There  Here))      = Here
shift (Rot s)   (There (There (There el))) = There $ There $ There $ shift s el