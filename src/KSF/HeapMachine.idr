module KSF.HeapMachine

import KSF.Prelim
import KSF.Refinements
import KSF.Codes
import KSF.ClosMachine
import KSF.Heaps

%access public export
%default total

-- State : Type -> Type -> Type -> Type 
-- State pa ha hp = (List (pa, ha), List (pa, ha), hp)

-- data StepH : (pa -> pa) -> (pa -> Maybe (Com pa)) -> (hp -> ha -> Maybe (Maybe ((pa, ha), ha))) -> (hp -> (pa, ha) -> ha -> (hp, ha)) -> Label -> State pa ha hp -> State pa ha hp -> Type where
--   StepNilH     : {phi : pa -> Maybe (Com pa)} -> {inc : pa -> pa} -> {put : hp -> (pa, ha) -> ha -> (hp, ha)} -> {get : hp -> ha -> Maybe (Maybe ((pa, ha), ha))} ->
--     phi p = Just RetC                                    -> StepH inc phi get put Tau  ((p,a)::t,           v, h) (                   t,        v, h)
--   StepLoadH    : {phi : pa -> Maybe (Com pa)} -> {inc : pa -> pa} -> {put : hp -> (pa, ha) -> ha -> (hp, ha)} -> {get : hp -> ha -> Maybe (Maybe ((pa, ha), ha))} ->
--     phi p = Just (VarC x) -> Heaps.lookup (get h) a x = Just e -> StepH inc phi get put Tau  ((p,a)::t,           v, h) (        (inc p,a)::t,     e::v, h)
--   StepPushValH : {phi : pa -> Maybe (Com pa)} -> {inc : pa -> pa} -> {put : hp -> (pa, ha) -> ha -> (hp, ha)} -> {get : hp -> ha -> Maybe (Maybe ((pa, ha), ha))} ->
--     phi p = Just (LamC q)                                -> StepH inc phi get put Tau  ((p,a)::t,           v, h) (        (inc p,a)::t, (q,a)::v, h)
--   StepBetaH    : {phi : pa -> Maybe (Com pa)} -> {inc : pa -> pa} -> {put : hp -> (pa, ha) -> ha -> (hp, ha)} -> {get : hp -> ha -> Maybe (Maybe ((pa, ha), ha))} ->
--     phi p = Just AppC    -> put h g b = (h1,b1)          -> StepH inc phi get put Beta ((p,a)::t, g::(q,b)::v, h) ((q,b1)::(inc p,a)::t,        v, h1)

--(Code c pa, Heap pa ha hp) => Machine (State pa ha hp) where
--  MRel = ?wat --StepH inc phi get put

--data RepsHC : State pa ha hp -> StateC -> Type where
--  RepresentsC : All2 (RepresentsClos h) t t1 -> All2 (RepresentsClos h) v v1 -> RepsHC (t, v, h) (t1, v1)