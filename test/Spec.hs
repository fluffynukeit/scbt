import Syntax
import AlgoTyping
import Judgments
import Unbound.Generics.LocallyNameless
import Test.Hspec
import Prelude hiding (id)

infer gamma e = (a,p) where (a,p,d) = runApDelta $ (gamma |- (e :=>:) :: ApDelta)
inferSRec gamma e = (a,p) where (a,p,d) = runApDelta $ (gamma |- (e :>>?:) :: ApDelta)
inferS gamma e = (a,p) where (a,p,d) = runApDelta $ (gamma |- (e :>>:) :: ApDelta)
check gamma e a p = runDelta $ (gamma |- e :<=: (a, p) :: Delta)

al = s2n "al"
alHat = s2n "alHat"

main :: IO ()
main = hspec $ do
    describe "paper example for id context" $ do
        it "infers type of id function (Var)" $ do
            infer gamma id `shouldBe` (idSig, Bang)
        it "checks against Unit (1|alphaHat)" $ do
            check (gamma `Comma` (HatKappa $ alHat ::: Star)) Un (Hat $ s2n "alHat") Slash `shouldBe`
                gamma `Comma` (HatEquals $ alHat ::: Star :=: Unit)
        it "infers empty spine (EmptySpine)" $ do
            inferS (gamma `Comma` (HatEquals $ alHat ::: Star :=: Unit)) ([] ::: Unit, Slash) `shouldBe` (Unit, Slash)
        it "infers arrow spine (ArrowSpine)" $ do
            inferS (gamma `Comma` (HatKappa $ alHat ::: Star)) ([Un] ::: Hat alHat :->: Hat alHat, Slash) `shouldBe` (Unit, Slash)
        it "infers result type of id applied to Unit (ArrowE)" $ do
            infer gamma (call id $ with Un) `shouldBe` (Unit, Bang)
        it "recovers spine call principality (SpinRecover)" $ do
            inferSRec gamma ([Un] ::: idSig, Bang) `shouldBe` (Unit, Bang)
            

id = X (s2n "id")

idSig = V $ al ::: Star :.: (NoHat al :->: NoHat al)

gamma = Empty `Comma` XAp (s2n "id" ::: idSig) Bang


with a = SPlus a []
call f s = App f s

