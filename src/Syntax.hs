module Syntax where

import Data.Text (Text)
import Data.Sequence (Seq)
import Unbound.Generics.LocallyNameless hiding (Alpha)
import Unbound.Generics.LocallyNameless.Bind (Bind(..))
import Control.Monad.Trans.Maybe (MaybeT)

import Data.Typeable (Typeable)
import GHC.Generics hiding ((:+:), (:*:), (:.:), S)

-- | Variable types for expressions and values.
type X = Name (DecSyn ExpVal)

-- | Shorthand for binding
type a :.: b = Bind a b
pattern a :.: b = B a b
deriving instance (Eq a, Eq b) => Eq (a :.: b)

-- | = Declarative syntax from Figure 2 =

-- | EKind distinguishes syntax of expression and values
data EKind = ExpOnly | ExpVal
type EV = DecSyn ExpVal
type EO = DecSyn ExpOnly
-- An expression is either ExpVal or ExpOnly,
-- so it has type DecSyn j to generally be either.

-- | Declarative syntax of expressions and values
data DecSyn (k :: EKind) where
    -- | Common syntax between expression and values:
    X :: X -> EV
    Un :: EV
    Lam :: X :.: DecSyn k -> EV
    Rec :: X :.: EV -> EV
    Nil :: EV

    -- | Syntax that is invariant to expressions OR values
    Ann :: DecSyn k ::: A -> DecSyn k
    Pair :: DecSyn k -> DecSyn k -> DecSyn k
    Inj1 :: DecSyn k -> DecSyn k
    Inj2 :: DecSyn k -> DecSyn k
    (::::) :: DecSyn k -> DecSyn k -> DecSyn k
    -- TODO: add data kind to distinguish vector from non-vector

    -- | Syntax for expressions only.
    App :: DecSyn k -> SPlus k -> EO
    Case :: DecSyn k -> BigPi -> EO

-- | Spines and non-empty spines
type S a = [DecSyn a]
data SPlus a = SPlus (DecSyn a) (S a)

-- | Branch lists
data BigPi = BigPi

--
-- | Sorts: kappa
data Kappa = Star | N
    deriving (Eq, Show, Generic)

-- | Polarities, fancy P
data Pol = Pos | Neg | None deriving (Eq)

-- | Principalities: p
data SmallP = Bang | Slash
    deriving (Eq, Show, Generic)
type SmallQ = SmallP


-- | = Algorithmic syntax from Figure 11 =

-- | (Mono)Type variables.  Paired with a Kappa for terms/monotypes.
type Alpha k = Name (Syn k)
type Beta k = Alpha k

-- | Kind distinguishes between syntax that is valid for
-- Types (Ty), Terms/Monotypes (Tm), or both.  
data Kind = Ty | Tm

-- | Convenience types for Types and Terms/Monoterms
type A = Syn Ty
type B = A
type C = A

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
    NoHat :: Alpha Tm -> Syn k
    Hat :: Alpha Tm -> Syn k

    -- | Syntax for Types only
    V :: Alpha Tm ::: Kappa :.: A -> A
    E :: Alpha Tm ::: Kappa :.: A -> A
    (:>:) :: P -> A -> A
    (:/\:) :: A -> P -> A
    Vec :: T -> A -> A

    -- | Syntax for Terms only
    Zero :: T
    Succ :: T -> T

deriving instance Eq (Syn a)
deriving instance Typeable (Syn a)
deriving instance Show (Syn a)


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
    Hat a -> Just a
    NoHat a -> Just a
    _ -> Nothing
    )
    -> Just u
    )

-- | Equalities =
data (:=:) e f where
    (:=:) :: e -> f -> e :=: f
    deriving (Eq, Show, Generic)
infix 6 :=:

-- | Annotation of type a : b
data (:::) e f where
    (:::) :: e -> f -> e ::: f
    deriving (Eq, Show, Generic)
infix 7 :::

-- | Propositions
type P = T :=: T'
type Q = P

-- | Contexts
type Gamma = Seq Info
type Delta = FreshM Gamma
type ApDelta = FreshM (A, SmallP, Gamma)
type DeltaBot = FreshMT Maybe Gamma
type CqDelta = ApDelta
runDeltaBot :: DeltaBot -> Maybe Gamma
runDeltaBot = runFreshMT

data Info where
    Kappa :: Alpha Tm ::: Kappa -> Info
    HatKappa :: Alpha Tm ::: Kappa -> Info
    XAp :: X ::: A -> SmallP -> Info
    Equals :: Alpha Tm :=: Tau -> Info
    HatEquals :: Alpha Tm ::: Kappa :=: Tau -> Info
    Mark :: Alpha Tm -> Info
    deriving (Eq, Generic, Show)

