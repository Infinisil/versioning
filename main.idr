import Data.Vect
import Data.HVect

main : IO ()
main = do
  x <- getLine
  let foo = integerToFin (cast x) 3
  case foo of
    Nothing => putStrLn "Nothing"
    Just xx => putStrLn "Something"

CalcTrans : Vect (S k) Type -> Type
CalcTrans xs = HVect $ zipWith (\a, b => a -> b) (init xs) (tail xs)

data Transitions : Type -> Vect (S k) (Type, Type) -> Type -> Type where
  Single : (a -> b) -> Transitions a [(a, b)] b
  Chained : (a -> b) -> Transitions b ((b, c) :: lss) d -> Transitions a ((a, b) :: (b, c) :: lss) d

doIt : Transitions a ts b -> a -> b
doIt (Single f) y = f y
doIt (Chained f x) y = doIt x (f y)

fromIth : (n : Fin (S k)) -> Transitions {k=k} a ts b -> Prelude.Basics.fst (Data.Vect.index n ts) -> b
fromIth FZ (Single f) = f
fromIth (FS x) (Single f) impossible
fromIth FZ (Chained f x) = doIt (Chained f x)
fromIth (FS z) (Chained f x) = fromIth z x



Versions : Vect 3 Type
Versions = [ Int, String, Double ]

initial : head Versions
initial = 10

transitions : Transitions (head Versions) (zip (init Versions) (tail Versions)) (last Versions)
transitions = Chained (const "") (Single (\x => cast x))


