-- | This module implements the well-formed rules in Figure 17.
module WellFormed where

import Judgments
import Syntax
import Context
import Search

instance Turnstile (Tau ::: Kappa) Bool where

    -- VarSort, but why match with hat when SolvedVarSort already does?
    gamma |- NoHat u ::: k = Kappa (u ::: k) `elem` gamma

    -- SolvedVarSort, solved for some tau we don't know.
    gamma |- Hat a ::: k = solvedHat a k gamma

    -- UnitSort
    gamma |- Unit ::: Star = True

    -- BinSort
    gamma |- Bin tau1 tau2 ::: Star = gamma |- tau1 ::: Star && gamma |- tau2 ::: Star

    -- ZeroSort
    gamma |- Zero ::: N = True

    -- SuccSort
    gamma |- Succ t ::: N = gamma |- t ::: N

instance Turnstile Prop Bool where

    -- EqProp
    gamma |- (Prop (t :=: t')) = gamma |- t ::: N && gamma |- t' ::: N

instance Turnstile Type Bool where

    -- VarWF, by why match with hat when SolvedVarWF already does?
    gamma |- Type (NoHat u) = Kappa (u ::: Star) `elem` gamma

    -- SolvedVarWF
    gamma |- Type (Hat a) = solvedHat a Star gamma

    -- UnitWF
    gamma |- Type Unit = True

    -- UnitWF
    gamma |- Type (Bin a b) = gamma |- Type a && gamma |- Type b

    -- VecWF
    gamma |- Type (Vec t a) = gamma |- t ::: N && gamma |- (Type a)

    -- ForallWF
    gamma |- Type (V (alpha ::: kappa :.: a)) = gamma `Comma` (Kappa (alpha ::: kappa)) |- Type a

    -- ExistsWF
    gamma |- Type (E (alpha ::: kappa :.: a)) = gamma `Comma` (Kappa (alpha ::: kappa)) |- Type a

    -- ImpliesWF
    gamma |- Type (p :>: a) = gamma |- Prop p && gamma |- Type a

    -- WithWF
    gamma |- Type (a :/\: p) = gamma |- Prop p && gamma |- Type a

instance Turnstile Ptype Bool where

    -- PrincipalWF
    gamma |- Ptype a Bang = gamma |- Type a && null (setFEV (gamsub gamma a))

    -- NonPrincipalWF
    gamma |- Ptype a Slash = gamma |- Type a

instance Turnstile Types Bool where

    -- TypevecWF
    gamma |- Types as = all ((|-) gamma) as

instance Turnstile Ptypes Bool where
    -- PrincipalTypevecWF
    gamma |- Ptypes p types = all (\(Type a)-> gamma |- Ptype a p) types

-- | Wellformedness of contexts. 

-- EmptyCtx
ctx Empty = True

-- HypCtx
ctx (gamma `Comma` XAp (x ::: a) Slash) = ctx gamma && not (domX x gamma) && gamma |- Type a

-- Hyp!Ctx
ctx (gamma `Comma` XAp (x ::: a) Bang) =
    ctx gamma && not (domX x gamma) && gamma |- Type a && null (setFEV (gamsub gamma a))

-- VarCtx
ctx (gamma `Comma` Kappa (u ::: k)) = ctx gamma && not (dom u gamma)
ctx (gamma `Comma` HatKappa (u ::: k)) = ctx gamma && not (dom u gamma)

-- SolvedCtx
ctx (gamma `Comma` HatEquals (a ::: k :=: t)) =
    ctx gamma && not (dom a gamma) && gamma |- t ::: k

-- EqnVarCtx
ctx (gamma `Comma` Equals (a :=: tau)) = 
    case find (problem a) gamma of -- search to find the sort kappa
        Nothing -> False
        Just (Kappa (_ ::: k)) ->
            ctx gamma && not (solved a gamma) && gamma |- tau ::: k
        _ -> False

-- MarkerCtx
ctx (gamma `Comma` Mark u) = ctx gamma && Mark u `notElem` gamma

