module Syntax where

import Data.Text (Text)
import Data.Sequence (Seq)
import Data.Either (Either)

-- | = Algorithmic types and contexts, Fig. 11 =

-- | Universal variables: alpha/beta/gamma
type Alpha = Text
type Beta = Alpha
type Gamma = Alpha

-- | Existential variables: alpha/beta/gamma hat
type AlphaHat = Text
type BetaHat = AlphaHat
type GammaHat = AlphaHat

-- | Variables u
data U 
    = Univ Alpha 
    | Exis AlphaHat
    deriving (Eq)

-- | Types: A,B,C
data A 
    = AOne 
    | ABin A O B
    | AAlpha Alpha
    | AAlphaHat AlphaHat
    | AForall Alpha Kappa A
    | AExists Alpha Kappa A
    | P :>: A -- "implies" variant
    | A :/\: P -- "with" variant
    | AVec T A
    deriving (Eq)
type B = A
type C = A

-- | Propositions: P,Q
data P = T :=: T'
    deriving (Eq)
type Q = P
type T' = T

-- | Binary connectives (O looks like ⊕), an
-- can sort of be associated to Operation
data O
    = (:->:)
    | (:+:)
    | (:*:)
    deriving (Eq)

--  | Terms/monotypes: t, tau, sigma
data T
     = TNat Natural
     | TOne
     | TAlpha Alpha
     | TAlphaHat AlphaHat
     | TBin Tau O Sigma
     deriving (Eq)
type Tau = T
type Sigma = T
data Natural = Zero | Succ Natural
    deriving (Eq)

-- | Context: Big Gamma, Delta, or Theta
type BigGamma = Seq F
type BigDelta = BigGamma
type BigTheta = BigGamma
data F -- FACT of contextual knowlege
    = FuKappa U Kappa
    | FxAp X A SmallP
    | FAlphaHatKappaTau AlphaHat Kappa Tau
    | FAlphaT Alpha T
    | FMarkP P
    | FMarkAlphaHat AlphaHat
    | FMarkU U
    deriving (Eq)

-- | = Declarative syntax and types, Fig. 1 and Fig. 2 =

-- | Expressions: e
data E
    = EVar X
    | EUnit
    | ELam X E
    | EApp E S
    | ERec X V
    | EAnn E A
    | EPair E E
    | EInj I E
    | ECase E BigPi
    | EVec [E] -- covers cases [] and e2 of e1 :: e2
    | ECons E [E]

data I = Inj1 | Inj2

-- | Variables: x
type X = Text

-- | Values: v
data V
    = VVar X
    | VUnit
    | VLam X E
    | VRec X V
    | VAnn V A
    | VPair V V
    | VInj I V
    | VVec [V]
    | VCons V [V]

-- | Spines
type S = [E]

-- | Nonempty spines
data Splus = Splus E S

-- | Patterns: rho
data Rho
    = RhoX X
    | RhoPair Rho Rho
    | RhoInj I Rho
    | RhoVec [Rho]
    | RhoCons Rho [Rho]

-- | Branches: pi
data Pi = (Seq Rho) :=>: E

-- | Branch lists, big Pi
type BigPi = [Pi]

-- | Sorts: kappa
data Kappa = Star | N
    deriving (Eq)

-- | Principalities: little p,q
data SmallP = Bang | Slash
    deriving (Eq)
type SmallQ = SmallP



