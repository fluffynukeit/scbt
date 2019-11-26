module Syntax where

import Data.Text (Text)
import qualified Data.Sequence as S (Seq, Seq((:|>), Empty))
import Unbound.Generics.LocallyNameless hiding (Alpha)
import Unbound.Generics.LocallyNameless.Bind (Bind(..))
import Control.Monad.Trans.Maybe (MaybeT)

import Data.Typeable (Typeable)
import GHC.Generics hiding ((:+:), (:*:), (:.:), S)

-- | Variable types for expressions and values.
type X = Name (DecSyn Pat)

-- | Shorthand for binding
type a :.: b = Bind a b
pattern a :.: b = B a b
deriving instance (Eq a, Eq b) => Eq (a :.: b)

-- | = Declarative syntax from Figure 2 =
-- Note: patterns don't have () listed in Figure 2 but they should.
-- Also, Wild _ is not listed, but it should as well.

-- | DKind distinguishes declarative syntax of expressions, values
-- and patterns. Each kind identifies the largest applicable
-- set for the syntax.
data DKind = Exp | Val | Pat
type DP = DecSyn Pat
type DV = DecSyn Val
type DE = DecSyn Exp

class ExpOrVal (k :: DKind)
instance ExpOrVal ('Exp)
instance ExpOrVal ('Val)

-- | Declarative syntax of expressions, values, and patterns:
data DecSyn (k :: DKind) where
    -- | Common syntax between expressions, values, and patterns:
    X :: X -> DP
    Nil :: DP
    Un :: DP

    -- | Common syntax between expressions and values, but not patterns:
    Lam :: X :.: DecSyn k -> DV
    Rec :: X :.: DV -> DV

    -- | Syntax for expressions only.
    App :: DecSyn k -> SPlus k -> DE
    Case :: DecSyn k -> BigPi -> DE

    -- | Syntax for patterns only.
    Wild :: DP

    -- | Syntax that is invariant to expressions or values or patterns:
    Pair :: DecSyn k -> DecSyn k -> DecSyn k
    Inj1 :: DecSyn k -> DecSyn k
    Inj2 :: DecSyn k -> DecSyn k
    (::::) :: DecSyn k -> DecSyn k -> DecSyn k
    -- TODO: add data kind to distinguish vector from non-vector?

    -- | Syntax that is invariant to expressions OR values, but NOT patterns:
    Ann :: ExpOrVal k => DecSyn k ::: A -> DecSyn k

-- | Spines and non-empty spines
type S a = [DecSyn a]
data SPlus a = SPlus (DecSyn a) (S a)

-- | Branches and branch lists
data SmallPi = [DP] :=> DE
type BigPi = [SmallPi]
pattern a :|: b = (a:b)

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

-- NOTE: I originally used DataKinds to try to distinguish between
-- terms/monotypes (t, tau, sigma) and types (A, B, C).  This turned
-- out to be very messy for a variety of reasons:
-- - Generic cannot be derived for a GADT, so Generic instance must 
--      be manually defined
-- - Unbound generics as well as Unbound (with TH) choke on 
--      existential types, which is often the way to do subtyping
-- - Require upcasting/downcasting (e.g. via Typeable)
-- - OR require distinct Haskell types for terms/monoterms and types
--      even though they share a syntax.
-- So, for the time being, just dump all the algorithmic syntax into
-- a single type and rely on proper usage manually to make things
-- so much simpler.  Maybe in the I can figure out how TypeFamilies
-- or something else to model the type promotion and demotion but
-- keep a uniform syntax.

-- | (Mono)Type variables.  Paired with a Kappa for terms/monotypes.
type Alpha = Name Syn
type Beta = Alpha

-- | Convenience types for Types and Terms/Monoterms
type A = Syn
type B = A
type C = A

type T = Syn
type Tau = T
type Sigma = T
type T' = T

-- | Syntax of types and monotypes
data Syn where
    -- | Common syntax between Types and Terms/Monotypes
    Unit :: Syn
    (:->:) :: Syn -> Syn -> Syn
    (:+:) :: Syn -> Syn -> Syn
    (:*:) :: Syn -> Syn -> Syn
    NoHat :: Alpha -> Syn
    Hat :: Alpha -> Syn

    -- | Syntax for Types only
    V :: Alpha ::: Kappa :.: A -> A
    E :: Alpha ::: Kappa :.: A -> A
    (:>:) :: P -> A -> A
    (:/\:) :: A -> P -> A
    Vec :: T -> A -> A

    -- | Syntax for Terms only
    Zero :: T
    Succ :: T -> T
    deriving (Eq, Typeable, Show, Generic)

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
type Gamma = S.Seq Info
type Delta = FreshM Gamma

-- | Patterns for Gamma,Info commonly used in paper
pattern Comma a b = (S.:|>) a b
pattern Empty = S.Empty

-- | Various judgment results and runners
type ApDelta = FreshM (A, SmallP, Gamma)
type DeltaBot = FreshMT Maybe Gamma
type CoversResult = FreshM Bool
type CqDelta = ApDelta
runDeltaBot :: DeltaBot -> Maybe Gamma
runDeltaBot = runFreshMT
runApDelta = runFreshM
runDelta = runFreshM

data Info where
    Kappa :: Alpha ::: Kappa -> Info
    HatKappa :: Alpha ::: Kappa -> Info
    XAp :: X ::: A -> SmallP -> Info
    Equals :: Alpha :=: Tau -> Info
    HatEquals :: Alpha ::: Kappa :=: Tau -> Info
    Mark :: Alpha -> Info
    deriving (Eq, Generic, Show)

