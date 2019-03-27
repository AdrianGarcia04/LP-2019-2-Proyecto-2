module Semantics where

import Syntax

-- Definimos la interpretación de fórmulas como una función
-- que toma un nombre, una lista de elementos del universo y devuelve un elemento
-- en particular del universo.
type IntF a = Nombre -> [a] -> a

-- Definimos la interpretación de predicados como una función
-- que toma un nombre, una lista de elementos del universo y determina si los
-- elementos se relacionan con el predicado.
type IntR a = Nombre -> [a] -> Bool

-- Definimos el estado de un elemento como una función que va de una variable
-- a un elemento en particular del universo.
type Estado a = Ind -> a

-- Definimos una estructura de tipo a como la tupla formada por una lista
-- de elementos (del mismo tipo) del universo, una interpretación de
-- funciones y una interpretación de predicados.
type Estructura a = ([a], IntF a, IntR a)

-- Actualización de estado. Dado un estado, una variable y un elemento
-- a sustituir, devuelve el estado con la asignación a esa variable cambiada
-- al nuevo valor "a", si aplica.
actEst :: Estado a -> Ind -> a -> Estado a
actEst e x n = ne
    where ne y = if x == y then n else e y

-- Interpretación de términos. Dado un estado, una interpretación de funciones,
-- y un término, aplica la interpretación al término, devolviendo un elemento
-- del universo en particular.
iTerm :: Estado a -> IntF a -> Term -> a
iTerm e iF t = case t of
    V x -> e x
    F f lt -> iF f [iTerm e iF t | t <- lt] -- Interpreta la función con su lista
                                            -- de términos interpretados
                                            -- recursivamente.

-- Interpretación de fórmulas. Dada una estructura, un estado y una fórmula
-- de la LPO, determina el valor de verdad de la fórmula bajo
-- dicha interpretación y estado de las variables.
iForm :: (Eq a) => Estructura a -> Estado a -> Form -> Bool
iForm str e phi = case phi of
    FalseF -> False
    TrueF -> True
    Pr p lt -> iR p (map (iTerm e iF) lt)   -- Interpreta el predicado junto
                                            -- con su lista de términos interpretados
                                            -- recursivamente.
        where (_, iF, iR) = str             -- Descompone la estructura.
    Eq t1 t2 -> (iTerm e iF t1) == (iTerm e iF t2) -- Regresa verdadero si la interpretación
                                                   -- de ambos términos es la misma.
        where (_, iF, _) = str              -- Descompone la estructura.
    Neg p -> not (iForm str e p)
    Conj p q -> (iForm str e p) && (iForm str e q)
    Disy p q -> (iForm str e p) || (iForm str e q)
    Imp p q -> iForm str e (Disy (Neg p) q)
    Equiv p q -> iForm str e (Conj (Imp p q) (Imp q p))
    All x p -> and ([iForm str (actEst e x m) p | m <- u]) -- Aplicamos la conjunción a la lista
                                                           -- de valores booleanos obtenidos
                                                           -- a partir de aplicar la sustitución
                                                           -- recursivamente y actualizar
                                                           -- el valor de la variable ligada.
        where (u, _, _) = str               -- Obtenemos el universo a partir de la estructura.
    Ex x p -> or ([iForm str (actEst e x m) p | m <- u]) -- Análogo al cuantificador universal.
        where (u, _, _) = str               -- Obtenemos el universo a partir de la estructura.


-- Satisfacibilidad de fórmulas. Dada una estructura, un estado y una fórmula
-- de la LPO, determina si la fórmula es satisfacible bajo dicho modelo.
satForm :: (Eq a) => Estructura a -> Estado a -> Form -> Bool
satForm str e phi = iForm str e phi
