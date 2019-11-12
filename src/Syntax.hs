module Syntax where

import Data.Text (Text)
import Data.Sequence (Seq)
import Unbound.Generics.LocallyNameless hiding (Alpha)
import Control.Monad.Trans.Maybe (MaybeT)

-- | Type tags for variable symbols
data TVar = TVar
data Var = Var

-- | Variable types
type X = Name Var
type RecX = Rec Var
type Alpha = Name TVar
type Beta = Alpha

type a :.: b = Bind a b

-- | = Declarative syntax from Figure 2 =

-- | EKind distinguishes syntax of expression and values
data EKind = Exp | Val

-- | Convenience types for expressions and values.
type E = DecSyn Exp
type V = DecSyn Val

-- | Declarative syntax of expressions and values
data DecSyn (k :: EKind) where
    -- | Common syntax between expression and values:
    X :: X -> DecSyn k
    Un :: DecSyn k
    Lam :: X :.: E -> DecSyn k
    Rec :: RecX :.: V -> DecSyn k
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
    NoHat :: Alpha -> Syn k
    Hat :: Alpha -> Syn k

    -- | Syntax for Types only
    V :: Alpha ::: Kappa -> A -> A
    E :: Alpha ::: Kappa -> A -> A
    (:>:) :: P -> A -> A
    (:/\:) :: A -> P -> A
    Vec :: Syn Tm -> A -> A

    -- | Syntax for Terms only
    Zero :: T
    Succ :: T -> T

deriving instance Eq (Syn a)

-- | Pattern for identifying a binary connective
pattern Bin a b <- 
    (
    (\case
    c :->: d -> Just (c,d)
    c :+: d -> Just (c,d)
    c :*: d -> Just (c,d)
    _ -> Nothing
    ) 
    -> Just (a,b)
    )

-- | Pattern for extracting a binary operator constructor.
pattern Op a <- 
    (
    (\case
    _ :->: _ -> Just (:->:)
    _ :+: _ -> Just (:+:)
    _ :*: _ -> Just (:*:)
    _ -> Nothing
    ) 
    -> Just a
    )

-- | Pattern for matching either Hat or NoHat.
pattern U u <-
    (
    (\case
    NoHat a -> Just a
    Hat a -> Just a
    _ -> Nothing
    )
    -> Just u
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
type Delta = FreshM Gamma
type DeltaBot = MaybeT FreshM Gamma

data Info where
    Kappa :: Alpha ::: Kappa -> Info
    HatKappa :: Alpha ::: Kappa -> Info
    XAp :: X ::: A -> SmallP -> Info
    Equals :: Alpha :=: Tau -> Info
    HatEquals :: Alpha ::: Kappa :=: Tau -> Info
    Mark :: Alpha -> Info
    MarkHat :: Alpha -> Info
    deriving (Eq)

