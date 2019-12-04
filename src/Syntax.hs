module Syntax where

import qualified Data.Sequence as S (Seq, Seq((:|>), Empty))
import Unbound.Generics.LocallyNameless hiding (Alpha)
import Unbound.Generics.LocallyNameless.Bind (Bind(..))

import Data.Typeable (Typeable)
import GHC.Generics hiding ((:+:), (:*:), (:.:), S)

-- | Shorthand for binding
type a :.: b = Bind a b
pattern (:.:) :: a -> b -> Bind a b
pattern a :.: b = B a b
deriving instance (Eq a, Eq b) => Eq (a :.: b)

-- | = Source syntax from Figure 1 =
-- Note: patterns don't have () listed in Figure 1 but they should.
-- Also, Wild _ is not listed, but it should as well.

type X = Name E

-- | Expressions
data E where
  X :: X -> E
  Un :: E
  Lam :: X :.: E -> E
  App :: E -> SPlus -> E
  Rec :: X :.: V -> E
  Ann :: E ::: A -> E
  Pair :: E -> E -> E
  Inj1 :: E -> E
  Inj2 :: E -> E
  Case :: (E, BigPi) -> E
  Nil :: E
  (::::) :: E -> E -> E

-- | Values
data V 
  = VX X
  | VUnit
  | VLam (X :.: E)
  | VRec (X :.: V)
  | VAnn (V ::: A)
  | VPair V V
  | VInj1 V
  | VInj2 V
  | VNil
  | VConcat V V

-- | Patterns
data Rho
  = RhoX X
  | RhoUnit
  | RhoPair Rho Rho
  | RhoInj1 Rho
  | RhoInj2 Rho
  | RhoNil
  | RhoConcat Rho Rho
  | Wild

-- | Typeclass supporting convenience patterns for Injections
class Inj a where
  unInj :: a -> Maybe a
  isInj1 :: a -> Maybe Bool

instance Inj Rho where
  unInj (RhoInj1 a) = Just a
  unInj (RhoInj2 a) = Just a
  unInj _ = Nothing
  isInj1 (RhoInj1 _) = Just True
  isInj1 (RhoInj2 _) = Just False
  isInj1 _ = Nothing

instance Inj E where
  unInj (Inj1 a) = Just a
  unInj (Inj2 a) = Just a
  unInj _ = Nothing
  isInj1 (Inj1 _) = Just True
  isInj1 (Inj2 _) = Just False
  isInj1 _ = Nothing

-- | Match on Inj1 or Inj2
pattern InjK :: Inj a => a -> a
pattern InjK k <- 
  (unInj -> Just k)

-- | Map Inj1/Inj2 to arguments 1 and 2
ak :: Inj b => b -> a -> a -> a
ak (isInj1 -> Just True) a _ = a
ak (isInj1 -> Just False) _ b = b
ak _ _ _ = error "Non-injunction passed to ak function."

-- | Spines and non-empty spines
type S = [E]
data SPlus = SPlus E S

-- | Branches and branch lists
data SmallPi = [Rho] :=> E
type BigPi = [SmallPi]
pattern (:|:) :: a -> [a] -> [a]
pattern a :|: b = (a:b)

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

