module Main

-- port of http://www.cs.indiana.edu/~sabry/papers/sequent_code.tar

import ABS.L                                                         
import ABS.AI                                                        
import ABS.Name.L                                           
import ABS.Value.L                                          
import ABS.Name.AM                                          
import ABS.Value.AM                                         

%default total
%access public export

td : (C -> (Nat, C)) -> (I -> (Nat, C)) -> DB -> IO ()
td evl evm t =                                               
    let 
     is = compile t                                           
     (ms, ma) = evm is                                         
     (cs, ca) = evl (embedI is)                                   
     in 
    do putStrLn $ "Answer using abstract machine: (" ++ show ms ++ " steps)"                 
       printLn ma                                               
       putStrLn $ "Answer using calculus: (" ++ show cs ++ " steps)"
       printLn ca                                               
       putStrLn "--------------------------------" 
                                                                 
tn : DB -> IO ()
tn d = do putStrLn "=== Name:"
          td (eval Name.L.step) Name.AM.eval d

tv : DB -> IO ()
tv d = do putStrLn "=== Value:"
          td (eval Value.L.step) Value.AM.eval d 

var : Nat -> DB
var = DBvar                                                   

app : DB -> DB -> DB
app = DBapp

lam : DB -> DB
lam = DBlam

v0 : DB
v0 = var 0

v1 : DB
v1 = var 1

v2 : DB
v2 = var 2

v3 : DB
v3 = var 3

v4 : DB
v4 = var 4

t1 : DB
t1 = lam v0

t2 : DB
t2 = app t1 v0                                           

t3 : DB
t3 = app t1 t1

t4 : DB
t4 = app t3 t3                                                   

t5 : DB
t5 = app t4 (app t4 t3)                                          

t6 : DB
t6 = app t5 (app t5 (app t4 t3))

-- cooked

ff : DB
ff = lam $ lam v1

tt : DB
tt = lam $ lam v0

if_ : DB
if_ = lam $ lam $ lam $ app (app v2 v0) v1

zero : DB
zero = lam $ lam v1

succ : DB
succ = lam $ lam $ lam $ app v0 v2

one : DB
one = app succ zero

two : DB
two = app succ one

three : DB
three = app succ two

isZero : DB
isZero = lam $ app (app v0 tt) (lam ff)

const : DB
const = lam $ lam v1

pair : DB
pair = lam $ lam $ lam $ app (app v0 v2) v1

fstc : DB
fstc = lam $ app v0 (lam $ lam v1)

sndc : DB
sndc = lam $ app v0 (lam $ lam $ v0)

fix : DB
fix = lam $ app (lam $ app v1 $ app v0 v0) (lam $ app v1 $ app v0 v0)

add : DB
add = app fix $ lam $ lam $ lam $ app (app v1 v0) (lam $ app succ (app (app v3 v0) v1))

mul : DB
mul = app fix $ lam $ lam $ lam $ app (app v1 zero) (lam $ app (app add v1) (app (app v3 v0) v1))

fac : DB
fac = app fix $ lam $ lam $ app (app v0 one) (lam $ app (app mul v1) (app v2 v0))

eqnat : DB
eqnat = app fix $ lam $ lam $ lam $ app (app v1 (app (app v0 tt) (app const ff))) (lam $ app (app v1 ff) (lam $ app (app v4 v1) v0))

sumto : DB
sumto = app fix $ lam $ lam $ app (app v0 zero) (lam $ app (app add v1) (app v2 v0))

n5 : DB
n5 = app (app add two) three

n6 : DB
n6 = app (app add three) three

main : IO ()
main = 
  let test = app (app eqnat one) two in
    do tn test
       tv test 