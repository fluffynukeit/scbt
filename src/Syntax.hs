module Syntax where

import qualified Data.Sequence as S (Seq, Seq((:|>), Empty))
import Unbound.Generics.LocallyNameless hiding (Alpha)
import Unbound.Generics.LocallyNameless.Bind (Bind(..))

import Data.Typeable (Typeable)
import GHC.Generics hiding ((:+:), (:*:), (:.:), S)

-- | Variable types for expressions and values.
type X = Name (SrcSyn 'Pat)

-- | Shorthand for binding
type a :.: b = Bind a b
pattern (:.:) :: a -> b -> Bind a b
pattern a :.: b = B a b
deriving instance (Eq a, Eq b) => Eq (a :.: b)

-- | = Source syntax from Figure 1 =
-- Note: patterns don't have () listed in Figure 1 but they should.
-- Also, Wild _ is not listed, but it should as well.

-- | SKind distinguishes source syntax of expressions, values
-- and patterns. Each kind identifies the largest applicable
-- set for the syntax.
data SKind = Exp | Val | Pat
type Pattern = SrcSyn 'Pat
type SV = SrcSyn 'Val
type SE = SrcSyn 'Exp

class ExpOrVal (k :: SKind)
instance ExpOrVal ('Exp)
instance ExpOrVal ('Val)

-- | Source syntax of expressions, values, and patterns:
data SrcSyn (k :: SKind) where
    -- | Common syntax between expressions, values, and patterns:
    X :: X -> Pattern
    Nil :: Pattern
    Un :: Pattern

    -- | Common syntax between expressions and values, but not patterns:
    Lam :: X :.: SrcSyn k -> SV
    Rec :: X :.: SV -> SV

    -- | Syntax for expressions only.
    App :: SrcSyn k -> SPlus k -> SE
    Case :: (SrcSyn k, BigPi) -> SE

    -- | Syntax for patterns only.
    Wild :: Pattern

    -- | Syntax that is invariant to expressions or values or patterns:
    Pair :: SrcSyn k -> SrcSyn k -> SrcSyn k
    Inj1 :: SrcSyn k -> SrcSyn k
    Inj2 :: SrcSyn k -> SrcSyn k
    (::::) :: SrcSyn k -> SrcSyn k -> SrcSyn k
    -- TODO: add data kind to distinguish vector from non-vector?

    -- | Syntax that is invariant to expressions OR values, but NOT patterns:
    Ann :: ExpOrVal k => SrcSyn k ::: A -> SrcSyn k

-- | Match on Inj1 or Inj2
pattern InjK :: SrcSyn k -> SrcSyn k
pattern InjK k <- 
  (
  (\case
  Inj1 a -> Just a
  Inj2 a -> Just a
  _ -> Nothing
  )
  -> Just k
  )

-- | Map Inj1/Inj2 to arguments 1 and 2
ak :: SrcSyn k -> a -> a -> a
ak (Inj1 _) a _ = a
ak (Inj2 _) _ b = b
ak _ _ _ = error "Non-injunction passed to ak function."


-- | Spines and non-empty spines
type S a = [SrcSyn a]
data SPlus a = SPlus (SrcSyn a) (S a)

-- | Branches and branch lists
data SmallPi = [Pattern] :=> SE
type BigPi = [SmallPi]
pattern (:|:) :: a -> [a] -> [a]
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
pattern Bin :: Syn -> Syn -> Syn
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
pattern Op :: (Syn -> Syn -> Syn) -> Syn
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
pattern U :: Alpha -> Syn
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
type Delta = Gamma
type DeltaBot = Maybe Gamma

pattern Bottom :: Maybe Delta
pattern Bottom = Nothing

pattern Delta :: Delta -> Maybe Delta
pattern Delta a = Just a

-- | Patterns for Gamma,Info commonly used in paper
pattern Comma :: S.Seq a -> a -> S.Seq a
pattern Comma a b = (S.:|>) a b
pattern Empty :: S.Seq a
pattern Empty = S.Empty

-- | Various judgment results and runners
type Judgment a = FreshM a
type ApDelta = (A, SmallP, Delta)
type CqDelta = ApDelta

runJudgment :: FreshM a -> a
runJudgment = runFreshM

-- | Fact within a context
data Info where
    Kappa :: Alpha ::: Kappa -> Info
    HatKappa :: Alpha ::: Kappa -> Info
    XAp :: X ::: A -> SmallP -> Info
    Equals :: Alpha :=: Tau -> Info
    HatEquals :: Alpha ::: Kappa :=: Tau -> Info
    Mark :: Alpha -> Info
    deriving (Eq, Generic, Show)

