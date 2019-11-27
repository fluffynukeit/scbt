import Syntax
import Typing
import Judgments
import Unbound.Generics.LocallyNameless
import Test.Hspec
import Prelude hiding (id)

infer gamma e = (a,p) where (a,p,d) = runJudgment $ (gamma |- (e :=>:) :: Judgment ApDelta)
inferSRec gamma e = (a,p) where (a,p,d) = runJudgment $ (gamma |- (e :>>?:) :: Judgment ApDelta)
inferS gamma e = (a,p) where (a,p,d) = runJudgment $ (gamma |- (e :>>:) :: Judgment ApDelta)
check gamma e a p = runJudgment $ (gamma |- e :<=: (a, p) :: Judgment Delta)

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
        it "infers forall spine (VSpine)" $ do
            inferS gamma ([Un] ::: idSig, Bang) `shouldBe` (Unit, Slash)
        it "recovers spine call principality (SpineRecover)" $ do
            inferSRec gamma ([Un] ::: idSig, Bang) `shouldBe` (Unit, Bang)
        it "infers result type of id applied to Unit (ArrowE)" $ do
            infer gamma (call id $ with Un) `shouldBe` (Unit, Bang)
            

id = X (s2n "id")

idSig = V $ al ::: Star :.: (NoHat al :->: NoHat al)

gamma = Empty `Comma` XAp (s2n "id" ::: idSig) Bang


with a = SPlus a []
call f s = App f s

