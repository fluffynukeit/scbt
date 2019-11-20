import Syntax
import AlgoTyping
import Judgments
import Unbound.Generics.LocallyNameless

infer gamma e = runApDelta $ (gamma |- (e :=>:) :: ApDelta)

main :: IO ()
main = 
    let (a,p,delta) = infer gamma idAppExp
    in do
        putStrLn $ show a
        putStrLn $ show p

gamma = 
    let a = s2n "a"
    in Empty `Comma` XAp (s2n "id" ::: V (a ::: Star :.: (NoHat a :->: NoHat a))) Bang

idAppExp = App (X (s2n "id")) (SPlus Un [])

