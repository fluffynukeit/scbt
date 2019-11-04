module Types where

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
type U = Either Alpha AlphaHat

-- | Types: A,B,C
data A 
    = AOne 
    | ABin A O B
    | AAlpha Alpha
    | AAlphaHat AlphaHat
    | AForAll Alpha Kappa A
    | AExists Alpha Kappa A
    | P :>: A -- "implies" variant
    | A :/\: P -- "with" variant
    | Vec T A
type B = A
type C = A

-- | Propositions: P,Q
data P = T :=: T'
type Q = P
type T' = T

-- | Binary connectives (O looks like ⊕), an
-- can sort of be associated to Operation
data O
    = (:->:)
    | (:+:)
    | (:*:)

--  | Terms/monotypes: t, tau, sigma
data T
     = TNat Natural
     | TOne
     | TAlpha Alpha
     | TAlphaHat AlphaHat
     | TBin Tau O Sigma
type Tau = T
type Sigma = T
data Natural = Zero | Succ Natural

-- | Context: Big Gamma, Delta, or Theta
type BigGamma = Seq F
type BigDelta = BigGamma
type BigTheta = BigGamma
data F -- FACT of contextual knowlege
    = FKappa U Kappa
    | FA X A P
    | FAlphaHat AlphaHat Kappa Tau
    | FAlpha Alpha Tau
    | FMarkP P
    | FMarkAlphaHat AlphaHat
    | FMarkU U

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

-- | Principalities: little p,q
data SmallP = Bang | Slash
type SmallQ = SmallP



