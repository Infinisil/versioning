import Data.Vect
import Data.HVect

main : IO ()
main = putStrLn "Hi"

data Versions : Vect (S k) Type -> Type -> Type where
  Nil : Versions [a] a
  (::) : (a -> b) -> Versions (b :: rest) d -> Versions (a :: b :: rest) d

transition : Versions (a :: rest) b -> a -> b
transition [] y = y
transition (f :: x) y = transition x (f y)

getIt : (versions : Versions ts b) -> (def : b) -> (existing : Maybe (f ** (f, Elem f ts))) -> b
getIt _ d Nothing = d -- No existing value, return default
getIt [] d (Just (_ ** (a, Here))) = a -- Already updated to latest state
getIt (trans :: x) d (Just (_ ** (a, Here))) = getIt x d (Just (_ ** (trans a, Here))) -- Not updated to latest state, recursing with migrated value
getIt (trans :: x) d (Just (_ ** (a, There elem))) = getIt x d (Just (_ ** (a, elem))) -- Maybe not updated to latest value, recursing through al subterms


g : (existing : Maybe (f ** (f, Elem f [String, Int, Double]))) -> Double
g = getIt [cast, cast] 30.0
