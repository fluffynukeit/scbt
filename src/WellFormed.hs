-- | This module implements the well-formed rules in Figure 17.
module WellFormed where

import Judgments
import Syntax
import Context

instance Turnstile (Tau ::: Kappa) Bool where
    -- (|-) gamma (TNoHat a ::: kappa) = True -- TODO:: VarSort
    -- (|-) gamma (THat ahat ::: kappa) = True -- TODO: SolvedVarSort
    gamma |- Unit ::: Star = True -- UnitSort
    gamma |- Bin tau1 tau2 ::: Star = gamma |- tau1 ::: Star && gamma |- tau2 ::: Star -- BinSort
    gamma |- Zero ::: N = True -- ZeroSort
    gamma |- Succ t ::: N = gamma |- t ::: N -- SuccSort

instance Turnstile Prop Bool where
    gamma |- (Prop (t :=: t')) = gamma |- t ::: N && gamma |- t' ::: N -- EqProp

instance Turnstile Type Bool where
    -- TODO: VarWF
    -- TODO: SolvedVarWF
    gamma |- Type Unit = True -- UnitWF
    gamma |- Type (Bin a b) = gamma |- Type a && gamma |- Type b -- BinWF
    gamma |- Type (Vec t a) = gamma |- t ::: N && gamma |- (Type a) -- VecWF
    gamma |- Type (V (alpha ::: kappa) a) = gamma `Comma` (Kappa (alpha ::: kappa)) |- Type a -- ForallWF
    gamma |- Type (E (alpha :::kappa) a) = gamma `Comma` (Kappa (alpha ::: kappa)) |- Type a -- ExistsWF
    gamma |- Type (p :>: a) = gamma |- Prop p && gamma |- Type a -- ImpliesWF
    gamma |- Type (a :/\: p) = gamma |- Prop p && gamma |- Type a -- WithWF

instance Turnstile Ptype Bool where
    -- (|-) gamma (Ptype a Bang) = TODO: PrincipalWF
    gamma |- Ptype a Slash = gamma |- Type a -- NonPrincipalWF

instance Turnstile Types Bool where
    gamma |- Types as = all ((|-) gamma) as -- TypevecWF

instance Turnstile Ptypes Bool where
    gamma |- Ptypes p types = all (\(Type a)-> gamma |- Ptype a p) types -- PrincipalTypevecWF

ctx Empty = True -- EmptyCtx
--ctx (gamma `Comma` (FxAp x a Slash)) = ctx gamma && gamma |- Type a -- TODO dom(gamma) -- HypCtx
--ctx (gamma `Comma` (FxAp x a Bang)) = ctx gamma && gamma |- Type a -- TODO dom(gamma), etc -- Hyp!Ctx
-- TODO VarCtx, SolvedCtx, EqnVarCtx
ctx (gamma `Comma` mark@(Mark u)) = ctx gamma && mark `notElem` gamma

