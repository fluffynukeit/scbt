module Syntax where

import Data.Text (Text)
import Data.Sequence (Seq)

-- | Type alias for variable symbols
type Sym = Text

-- | = Declarative syntax from Figure 2 =

-- | EKind distinguishes syntax of expression and values
data EKind = Exp | Val

-- | Convenience types for expressions and values.
type E = DecSyn Exp
type V = DecSyn Val

-- | Declarative syntax of expressions and values
data DecSyn (k :: EKind) where
    -- | Common syntax between expression and values:
    X :: Sym -> DecSyn k
    Un :: DecSyn k
    Lam :: Sym -> E -> DecSyn k
    Rec :: Sym -> V -> DecSyn k
    Ann :: DecSyn k ::: A -> DecSyn k
    Pair :: DecSyn k -> DecSyn k -> DecSyn k
    Inj :: Inj -> DecSyn k -> DecSyn k
    Nil :: DecSyn k
    (::::) :: DecSyn k -> DecSyn k -> DecSyn k
    -- TODO: add data kind to distinguish vector from non-vector

    -- | Syntax for expressions only
    App :: E -> SPlus -> E
    Case :: E -> BigPi -> E

data Inj = Inj1 | Inj2
type S = [E]
data SPlus = SPlus E S

data BigPi = BigPi

--
-- | Sorts: kappa
data Kappa = Star | N
    deriving (Eq)

-- | Principalities: p
data SmallP = Bang | Slash
    deriving (Eq)


-- | = Algorithmic syntax from Figure 11 =

-- | Kind distinguishes between syntax that is valid for
-- Types (Ty), Terms/Monotypes (Tm), or both
data Kind = Ty | Tm

-- | Convenience types for Types and Terms/Monoterms
type A = Syn Ty
type B = A

type T = Syn Tm
type Tau = T
type Sigma = T
type T' = T

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
    V :: Sym ::: Kappa -> A -> A
    E :: Sym ::: Kappa -> A -> A
    (:>:) :: P -> A -> A
    (:/\:) :: A -> P -> A
    Vec :: Syn Tm -> A -> A

    -- | Syntax for Terms only
    Zero :: T
    Succ :: T -> T

deriving instance Eq (Syn a)

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
data (:=:) e f where
    (:=:) :: e -> f -> e :=: f
    deriving (Eq)
infix 6 :=:

-- | Annotation of type a : b
data (:::) e f where
    (:::) :: e -> f -> e ::: f
    deriving (Eq)
infix 7 :::

-- | Propositions
type P = T :=: T'

-- | Contexts
type Gamma = Seq Info
type Delta = Gamma

data Info where
    Kappa :: Sym ::: Kappa -> Info
    HatKappa :: Sym ::: Kappa -> Info
    XAp :: Sym ::: A -> SmallP -> Info
    Equals :: Sym :=: Tau -> Info
    HatEquals :: (Sym ::: Kappa) :=: Tau -> Info
    Mark :: Sym -> Info
    deriving (Eq)


