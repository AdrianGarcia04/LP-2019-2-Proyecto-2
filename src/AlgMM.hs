module AlgMM where

import Data.List
import Syntax

simpSus :: Subst -> Subst
simpSus sus = [(x, t) | (x, t) <- sus, V x /= t]

compSus :: Subst -> Subst -> Subst
compSus s1 s2 = zs ++ ws
    where zs = simpSus ([(x, apsubT t s2) | (x, t) <- s1])
          ws = [(x, t) | (x, t) <- s2, not (elem x vs1)]
          vs1 = fst (unzip s1)
