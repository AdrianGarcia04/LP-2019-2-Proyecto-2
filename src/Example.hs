module Ejemplo where

import Syntax
import Semantics

-- Funciones
sumaM m a b = mod (a + b) m
restaM m a b = mod (a - b) m
prodM m a b = mod (a * b) m
expM m a b = mod (a ^ b) m

-- Predicados
prirel a b = gcd a b == 1
divis a b = mod b a == 0

-- Interpretación de funciones
iF :: Int -> IntF Int
iF m f l = case f of
    "s" -> sumaM m (l!!0) (l!!1)
    "p" -> prodM m (l!!0) (l!!1)
    "r" -> restaM m (l!!0) (l!!1)
    "exp" -> expM m (l!!0) (l!!1)
    _ -> read f :: Int

-- Interpretación de predicados
iP :: Int -> IntR Int
iP m p l = case p of
    "Prirel" -> prirel (l!!0) (l!!1)
    "Divis" -> divis (l!!0) (l!!1)

-- Estado de las variables
est = id :: Int -> Int

main = do
    let m = 10
    let u = [1..(m-1)]
    -- ∀ x (x != 0 → ∃ y (x * y = 1))
    let f1 = All 1 ( Imp ( Neg ( Eq (V 1) (F "0" []) ) ) (Ex 2 ( Eq (F "p" [ (V 1), (V 2) ]) (F "1" []) ) ) )
    -- ∀ x, (∀ y ((x != 0 ∧ y != 0) → x + y != 0)))
    let f2 = All 1 ( All 2 ( Imp ( Disy ( Neg ( Eq (V 1) (F "0" []) ) ) ( Neg ( Eq (V 2) (F "0" []) ) ) ) ( Neg ( Eq ( F "s" [ (V 1), (V 2)] ) (F "0" []) ) ) ) )
    -- ∀ x (x != 0 → Divis(1, x) ∧ Divis(-1, x))
    let f3 = All 1 ( Imp ( Neg ( Eq (V 1) (F "0" []) ) ) ( Disy (Pr "Divis" [ (F "1" []), (V 1)]) (Pr "Divis" [ (F "-1" []), (V 1)])) )
    -- ∀ x (∀ y (Divis(x, y) → ∃ z ( Divis((x * y), (y * z) ) ) ) )
    let f4 = All 1 ( All 2 ( Imp ( Pr "Divis" [(V 1), (V 2)] ) ( Ex 3 ( Pr "Divis" [(F "p" [(V 1), (V 2)]), (F "p" [(V 2), (V 3)])] ) ) ) )
    -- ∀ x ( Divis(x, 1) → (x == 1 ∧ x == -1))
    let f5 = All 1 ( Imp ( Pr "Divis" [ (V 1), (F "1" []) ] ) ( Eq (V 1) (F "1" []) ) )
    -- (Prirel(2, 5) ∧ T) → Divis(1, 1)
    let f6 = Imp ( Conj (Pr "Prirel" [(F "2" []), (F "5" [])]) (TrueF)) (Pr "Divis" [(F "1" []), (F "1" [])])

    print $ iForm (u, iF m, iP m) est f1
    print $ iForm (u, iF m, iP m) est f2
    print $ iForm (u, iF m, iP m) est f3
    print $ iForm (u, iF m, iP m) est f4
    print $ iForm (u, iF m, iP m) est f5
    print $ iForm (u, iF m, iP m) est f6
