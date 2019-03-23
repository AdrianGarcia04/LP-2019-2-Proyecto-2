module Semantics where

import Syntax

type IntF a = Nombre -> [a] -> a
type IntR a = Nombre -> [a] -> Bool
type Estado a = Ind -> a

type Estructura a = ([a], IntF a, IntR a)

actEst :: Estado a -> Ind -> a -> Estado a
actEst e x n = ne
    where ne y = if x == y then n else e y

iTerm :: Estado a -> IntF a -> Term -> a
iTerm e iF t = case t of
    V x -> e x
    F f lt -> iF f [iTerm e iF t | t <- lt] -- La interpretación de la lista de términos.

iForm :: Eq a => Estructura a -> Estado a -> Form -> Bool
iForm str e phi = case phi of
    FalseF -> False
    TrueF -> True
    Pr p lt -> iR p (map (iTerm e iF) lt) where (_, iF, iR) = str
    Eq t1 t2 -> (iTerm e iF t1) == (iTerm e iF t2) where (_, iF, _) = str
    Neg p -> not (iForm str e p)
    Conj p q -> (iForm str e p) && (iForm str e q)
    Disy p q -> (iForm str e p) || (iForm str e q)
    Imp p q -> iForm str e (Disy (Neg p) q)
    Equiv p q -> iForm str e (Conj (Imp p q) (Imp q p))
    All x p -> and [iForm str (actEst e x m) p | m <- u]
        where (u, _, _) = str
    Ex x p -> or ([(iForm str (actEst e x m) p) | m <- u])
        where (u, _, _) = str
