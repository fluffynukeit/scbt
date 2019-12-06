import Syntax
import Typing
import Judgments
import Test.Hspec
import Prelude hiding (id, map)

infer gamma e = (a,p) where (a,p,d) = runJudgment $ (gamma |- (e :=>:) :: Judgment ApDelta)
inferSRec gamma e = (a,p) where (a,p,d) = runJudgment $ (gamma |- (e :>>?:) :: Judgment ApDelta)
inferS gamma e = (a,p) where (a,p,d) = runJudgment $ (gamma |- (e :>>:) :: Judgment ApDelta)
check gamma (e :: E) a p = runJudgment $ (gamma |- e :<=: (a, p) :: Judgment Delta)

main :: IO ()
main = hspec $ do
    describe "paper example for id, section 5.1" $ do
        it "infers type of id function (Var)" $ do
            infer gamma id `shouldBe` (idSig, Bang)
        it "checks against Unit (1|alphaHat)" $ do
            check (gamma `Comma` (HatKappa $ "alHat" ::: Star)) unit (Hat $ "alHat") Slash `shouldBe`
                gamma `Comma` (HatEquals $ "alHat" ::: Star :=: Unit)
        it "infers empty spine (EmptySpine)" $ do
            inferS (gamma `Comma` (HatEquals $ "alHat" ::: Star :=: Unit)) ([] ::: Unit, Slash) `shouldBe` (Unit, Slash)
        it "infers arrow spine (ArrowSpine)" $ do
            inferS (gamma `Comma` (HatKappa $ "alHat" ::: Star)) ([unit] ::: Hat "alHat" :->: Hat "alHat", Slash) `shouldBe` (Unit, Slash)
        it "infers forall spine (VSpine)" $ do
            inferS gamma ([unit] ::: idSig, Bang) `shouldBe` (Unit, Slash)
        it "recovers spine call principality (SpineRecover)" $ do
            inferSRec gamma ([unit] ::: idSig, Bang) `shouldBe` (Unit, Bang)
        it "infers result type of id applied to Unit (ArrowE)" $ do
            infer gamma (id |$ (unit, [])) `shouldBe` (Unit, Bang)
    describe "paper example for map, section 3" $ do
        it "has correct inferred signature" $ do
            infer Empty (ann map |: mapSig) `shouldBe` (mapSig, Bang)
            

-- | Source expressions and type expressions for id example from 5.1
id = "id" :: E
idSig = forall "al" |: Star |. "al" |-> "al"
gamma = Empty `Comma` XAp ("id" ::: idSig) Bang

-- | Source and type annotations from map example in section 3
map :: E
map = rec "map" |. lam "f" |. lam "xs" |. caseOf ("xs", 
    [ [nil] :=> nil
    , ["y" |:: "ys"] :=> (("f" |$ ("y", [])) |:: ("map" |$ ("f", ["ys"])))
    ]
    )
mapSig 
    =  forall "n" |: N 
    |. forall "al" |: Star 
    |. forall "be" |: Star 
    |. ("al" |-> "be") |->  Vec "n" "al" |-> Vec "n" "be"
