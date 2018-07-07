import Data.Vect
import Data.Vect.Quantifiers
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

decode : (n : Fin (S k)) -> (ts: Vect (S k) Type) -> All (\t => s -> t) ts -> s -> (f ** (f, Elem f ts))
decode FZ (z :: _) (x :: _) y = (z ** (x y, Here))
decode (FS z) (_ :: (s :: xs)) (_ :: t) y with (decode z (s :: xs) t y)
  decode (FS z) (_ :: (s :: xs)) (_ :: t) y | (f ** (str, elem)) = (f ** (str, There elem))

decode' : (ts : Vect (S k) Type) -> All (\t => s -> t) ts -> (versions : Versions ts b) -> (def : b) -> (n: Integer) -> s -> b
decode' {k=k} ts x versions def n s with (integerToFin n (S k))
  decode' ts x versions def n s | Nothing = getIt versions def Nothing
  decode' ts x versions def n s | (Just y) = getIt versions def (Just $ decode y ts x s)

myDecode : Integer -> String -> Int
myDecode = decode' [String, Double, Int] [id, cast, cast] [(+1.0) . cast, (+5) . cast] 1
