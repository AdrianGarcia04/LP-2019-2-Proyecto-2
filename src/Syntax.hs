module Syntax where

import Data.List

-- Definimos los indices como sinónimos de enteros, para usarlos como variables.
type Ind = Int

-- Definimos los nombres de funciones y predicados como cadenas.
type Nombre = String

-- Definición de términos. Son variables o funciones (la aridad está especificada
-- por la longitud de la lista de términos).
data Term = V Ind | F Nombre [Term]

-- Definición de fórmulas.
data Form = TrueF
            | FalseF
            | Pr Nombre [Term]
            | Eq Term Term
            | Neg Form
            | Conj Form Form
            | Disy Form Form
            | Imp Form Form
            | Equiv Form Form
            | All Ind Form
            | Ex Ind Form

-- Dada una fórmula de la LPO, devuelve una lista de las variables libres,
-- i.e. aquellas que no se encuentran bajo el alcance de un cuantificador.
fv :: Form -> [Ind]
fv TrueF = []
fv FalseF = []
fv (Pr _ ts) = concat ([varT t | t <- ts]) -- Encontramos las variables en su lista
                                           -- de términos y los "comprimimos" en una
                                           -- sola lista.
fv (Eq t1 t2) = union (varT t1) (varT t2)
fv (Neg phi) = fv phi
fv (Conj phi psi) = union (fv phi) (fv psi)
fv (Disy phi psi) = union (fv phi) (fv psi)
fv (Imp phi psi) = union (fv phi) (fv psi)
fv (Equiv phi psi) = union (fv phi) (fv psi)
fv (All x phi) = (fv phi) \\ [x]           -- Encontramos las variables libres
                                           -- recursivamente y después eliminamos
                                           -- la variable ligada x.
fv (Ex x phi) = (fv phi) \\ [x]            -- Análogo al cuantificador universal.

-- Dado un término, devuelve una lista con las variables encontradas.
varT :: Term -> [Ind]
varT (V x) = [x]
varT (F _ []) = []
varT (F _ l) = nub (concat ([varT t | t <- l]) ) -- Obtenemos recursivamente
                                                 -- las variables en la función
                                                 -- y las "comprimimos" en una
                                                 -- sola lista. Finalmente,
                                                 -- eliminamos duplicados.

-- Dada una fórmula de la LPO, devuelve una lista de las variables ligadas,
-- i.e. aquellas que se encuentran bajo el alcance de un cuantificador.
bv :: Form -> [Ind]
bv TrueF = []
bv FalseF = []
bv (Pr _ ts) = []
bv (Eq t1 t2) = []
bv (Neg phi) = bv phi
bv (Conj phi psi) = union (bv phi) (bv psi)
bv (Disy phi psi) = union (bv phi) (bv psi)
bv (Imp phi psi) = union (bv phi) (bv psi)
bv (Equiv phi psi) = union (bv phi) (bv psi)
bv (All x phi) = union (bv phi) [x]          -- Encontramos las variables ligadas
                                             -- recursivamente y después agregamos
                                             -- la variable ligada x.
bv (Ex x phi) = union (bv phi) [x]           -- Análogo al cuantificador universal.

-- Cerradura universal. Dada una fórmula de la LPO, devuelve una fórmula con la cerradura universal
-- aplicada, i.e. las variables que se encontraban libres en φ ahora estarán
-- ligadas con el cuantificador universal.
aCl :: Form -> Form
aCl phi = aClaux phi (fv phi) -- Llamada a la función auxiliar con φ y una lista
                              -- que contiene sus variables libres.

aClaux :: Form -> [Ind] -> Form
aClaux phi l = case l of
    [] -> phi
    x:xs -> All x (aClaux phi xs) -- Dada la variable x, agrega a φ un cuantificador
                                  -- universal que liga a x, y continua recursivamente
                                  -- con el resto de variables libres.

-- Cerradura existencial. Dada una fórmula de la LPO, devuelve una fórmula con la cerradura existencial
-- aplicada, i.e. las variables que se encontraban libres en φ ahora estarán
-- ligadas con el cuantificador existencial.
eCl :: Form -> Form
eCl phi = eClaux phi (fv phi) -- Llamada a la función auxiliar con φ y una lista
                              -- que contiene sus variables libres.

eClaux :: Form -> [Ind] -> Form
eClaux phi l = case l of
    [] -> phi
    x:xs -> Ex x (eClaux phi xs)  -- Dada la variable x, agrega a φ un cuantificador
                                  -- existencial que liga a x, y continua recursivamente
                                  -- con el resto de variables libres.

-- Definimos la sustitución en fórmulas de la LPO como una lista
-- de tuplas de la forma (Índice, Término).
type Subst = [(Ind, Term)]

-- Dada una sustitución, determina si es válida.
verifSus :: Subst -> Bool
verifSus s = tieneRep [v | (v,t) <- s] -- Llamada auxiliar con la lista de variables
                                       -- de cada tupla en la lista de sustituciones.

-- Dada una lista de elementos comparables, determina si existen elementos repetidos.
tieneRep :: (Eq a) => [a] -> Bool
tieneRep l = case l of
    [] -> False
    x:xs -> if (elem x xs) then True
            else tieneRep xs

-- Sustitución en términos. Dado un término y una sustitución, devuelve
-- el término con la sustitución aplicada, si es el caso.
apsubT :: Term -> Subst -> Term
apsubT t sus = case t of
    V x -> case sus of
        [] -> V x
        (v,t2):xs -> if (x == v)
                    then t2
                    else apsubT (V x) xs    -- Si la sustitución no aplica,
                                            -- se prueba el resto de sustituciones
                                            -- recursivamente
    F f lt -> F f [apsubT t sus | t <- lt]  -- Regresa la función con una lista
                                            -- de términos donde se aplica
                                            -- recursivamente la sustitución a
                                            -- cada uno.

-- Sustitución en fórmulas. Dada una fórmula de la LPO y una sustitución, devuelve
-- la fórmula con la sustitución aplicada, si es el caso.
apsubF :: Form -> Subst -> Form
apsubF phi sus = case phi of
    TrueF -> TrueF
    FalseF -> FalseF
    Pr p lt -> Pr p [apsubT t sus | t <- lt]        -- Aplicamos la sustitución
                                                    -- de términos a cada término
                                                    -- en la lista del predicado.
    Eq t1 t2 -> Eq (apsubT t1 sus) (apsubT t2 sus)
    Neg p -> Neg (apsubF p sus)
    Conj p q -> Conj (apsubF p sus) (apsubF q sus)
    Disy p q -> Disy (apsubF p sus) (apsubF q sus)
    Imp p q -> Imp (apsubF p sus) (apsubF q sus)
    Equiv p q -> Equiv (apsubF p sus) (apsubF q sus)
    All x p -> if elem x lv
            then error "Sustitución no válida"      -- Si la variable ligada
                                                    -- se encuentra en la sustitución,
                                                    -- ocurre un error.
            else All x (apsubF p sus)               -- En otro caso, aplicamos
                                                    -- recursivamente la sustitución
                                                    -- de fórmulas al resto de la
                                                    -- la fórmula
            where lv = union xs ts                  -- Lista de variables
                                                    -- en la sustitución
                  (xs, tt) = unzip sus              -- Tuplas de la sustitución.
                  ts = concat [varT t | t <- tt]    -- Lista de variables en
                                                    -- los términos de la sustitución.
    Ex x p -> if elem x lv                          -- Análogo al cuantificador universal.
            then error "Sustitución no válida"
            else Ex x (apsubF p sus)
            where lv = union xs ts
                  (xs, tt) = unzip sus
                  ts = concat [varT t | t <- tt]
