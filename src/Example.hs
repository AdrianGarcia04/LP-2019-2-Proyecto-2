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

-- Interpretación de funciones
iF :: Int -> IntF Int
iF m f l -> case f of
    "s" -> sumaM m (l!!0) (l!!1)
    "p" -> prodM m (l!!0) (l!!1)
    "r" -> restaM m (l!!0) (l!!1)
    "exp" -> expM m (l!!0) (l!!1)
    _ -> read f :: Int

-- Interpretación de predicados
iP :: Int -> IntR Int
iP m p l = case p of
    "Prirel" -> prirel (l!!0) (l!!1)

-- Estado de las variables
est = id :: Int -> Int

main = do
    let m = 12
    let u = [(1..m-1)]
    let phi
