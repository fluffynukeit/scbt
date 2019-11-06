module Syntax where

import Data.Text (Text)
import Data.Sequence (Seq)

-- | = Declarative syntax from Figure 2 =
--
-- | Sorts: kappa
data Kappa = Star | N
    deriving (Eq)

-- | Principalities: p
data SmallP = Bang | Slash
    deriving (Eq)


-- | = Algorithmic syntax from Figure 11 =

type Sym = Text

-- | Kind distinguishes between syntax that is valid for
-- Types (Ty), Terms/Monotypes (Tm), or both
data Kind = Ty | Tm

-- | Syntax of types and monotypes
data Syn (k :: Kind) where
    -- | Common syntax between Types and Terms/Monotypes
    Unit :: Syn k
    (:->:) :: Syn k -> Syn k -> Syn k
    (:+:) :: Syn k -> Syn k -> Syn k
    (:*:) :: Syn k -> Syn k -> Syn k
    Alpha :: Sym -> Syn k
    AlphaHat :: Sym -> Syn k

    -- | Syntax for Types only
    V :: Anno Sym Kappa -> Syn Ty -> Syn Ty
    E :: Anno Sym Kappa -> Syn Ty -> Syn Ty
    (:>:) :: P -> Syn Ty -> Syn Ty
    (:/\:) :: Syn Ty -> P -> Syn Ty
    Vec :: Syn Tm -> Syn Ty -> Syn Ty

    -- | Syntax for Terms only
    Zero :: Syn Tm
    Succ :: Syn Tm -> Syn Tm

deriving instance Eq (Syn a)

-- | Convenience types for Types and Terms/Monoterms
type A = Syn Ty
type B = A

type T = Syn Tm
type Tau = T
type Sigma = T

-- | Pattern for identifying a binary connective
pattern Conn a b <- 
    (
    (\case
    c :->: d -> Just (c,d)
    c :+: d -> Just (c,d)
    c :*: d -> Just (c,d)
    _ -> Nothing
    ) 
    -> Just (a,b)
    )

-- | Equalities =
data Equals e f where
    (:=:) :: e -> f -> Equals e f
    deriving (Eq)
infix 7 :=:

-- | Annotation of type a : b
data Anno e f where
    (:::) :: e -> f -> Anno e f
    deriving (Eq)
infix 7 :::

-- | Propositions
type P = Equals (Syn Tm) (Syn Tm)

-- | Contexts
type Gamma = Seq Info

data Info where
    Kappa :: Anno Sym Kappa -> Info
    HatKappa :: Anno Sym Kappa -> Info
    XAp :: Anno Sym (Syn Ty) -> SmallP -> Info
    HatEquals :: Equals (Anno Sym Kappa) (Syn Tm) -> Info 
    Equals :: Equals Sym (Syn Tm) -> Info
    Mark :: Sym -> Info
    deriving (Eq)


