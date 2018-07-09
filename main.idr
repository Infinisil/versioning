import Data.Vect
import Data.Vect.Quantifiers
import Data.HVect

||| A migration takes a list of intermediate types, of which the first element represents 
|||
||| @ int Intermediate types, the first of which is our starting type
||| @ target The resulting type of the migration
data Migration : (int : Vect (S k) Type) -> (target : Type) -> Type where
  ||| A migration that's already done, no need to migrate anything
  Nil : Migration [a] a
  ||| A migration combining a function
  |||
  ||| @ trans Transition function
  ||| @ rest Rest of the migration to target type
  (::) : (trans: (a -> b)) -> (rest : Migration (b :: ms) c) -> Migration (a :: b :: ms) c

%name Migration mig

||| Get the value of the state through either a default value if there's no state already, 
||| or an existing value, applying the migration to update it
|||
||| @ mig Migration to use in case an older value was passed in
||| @ def Default value in case no value has been provided
||| @ existing Possibly an existing value, a dependent pair of a type and a value of that type and where to find it in the migration
getIt : (mig : Migration ts b) -> (def : b) -> (existing : Maybe (f ** (f, Elem f ts))) -> b
getIt _ d Nothing = d -- No existing value, return default
getIt [] d (Just (_ ** (a, Here))) = a -- Already updated to latest state
getIt (trans :: x) d (Just (_ ** (a, Here))) = getIt x d (Just (_ ** (trans a, Here))) -- Not updated to latest state, recursing with migrated value
getIt (trans :: x) d (Just (_ ** (a, There elem))) = getIt x d (Just (_ ** (a, elem))) -- Maybe not updated to latest value, recursing through al subterms




interface Decodable a where
  dec : String -> a

interface Encodable a where
  enc : a -> String

Decodable Int where
  dec = cast

Decodable String where
  dec = id


||| Decode a value of a type according to the given decoding functions for a list of types, return which type was used, the value of it, and a proof of it being present in the type list
|||
||| @ n Which type of the type list should be used to decode the input
||| @ ts The list of types
||| @ decs A way for decoding all types in the list from type s, this should be moved into an interface
decode : {ts: Vect (S k) Type}
       -> {decs : All Decodable ts}
       -> (n : Fin (S k))
       -> (input : String)
       -> (f ** (f, Elem f ts))
decode {decs = _ :: _} FZ input = (_ ** (dec input, Here))
decode {decs= _ :: restdec} (FS num) {k=S _} input with (decode {decs = restdec} num input)
  decode _ input | (_ ** (result, elem)) = (_ ** (result, There elem))

||| Combination of decode and getIt: Takes a list of types, decoding functions, a migration scheme, default value, a version number and an input. Tries to fit the version number into the types range, and returns the decoded value according to the migration or the default.
|||
||| @ ts The types of states, add to this when you change your state type
||| @ decode A way for decoding all types in the list from type s, this should be moved into an interface
||| @ mig Migration to use in case an older value was passed in
||| @ def Default value in case no state was already stored
||| @ n The old version number
||| @ input The old state, not decoded
decode' : (def : b) -> (ts : Vect (S k) Type) -> {auto decode : All Decodable ts} -> (mig : Migration ts b) -> (n: Integer) -> (input : String) -> b
decode' {decode=decs} {k=k} def _ mig n s with (integerToFin n (S k))
  decode' def _ mig _ _ | Nothing = getIt mig def Nothing
  decode' {decode=decs} def _ mig _ input | (Just ver) = getIt mig def (Just $ decode {decs=decs} ver input)


-- ############# Example ##############

-- Used for all versions: First line is the version number read from the state, second line is the state itself.
-- The dec function will handle migration from any old state to the new result type t, by going through all needed migration functions

mainWithDecode : Show t => (Integer -> String -> t) -> IO ()
mainWithDecode dec = do
  number <- cast <$> getLine
  input <- getLine
  let result = dec number input
  putStrLn (show result)
  mainWithDecode dec

-- Each function below represents a main : IO () in the specific version, they represent the evolution of a program
-- Note how the amount of code you need only linearly increases with the amount of versions
-- and changing the state type is trivial
-- All of this is fully type checked, you can't compile it unless you have provided everything it needs to do the migration correctly


-- Version 1 of our program uses an integer to store its state
-- First argument is the default value for the most recent state type
-- Second argument is the state types
-- Third argument is the migrations between the types, we don't need any now

v1 : IO ()
v1 = mainWithDecode $ decode' 0 [Int] []

-- Version 2 of our program changed its state representation from an integer to a string  
-- We add a migration function
v2 : IO ()
v2 = mainWithDecode $ decode' "" [Int, String]
  [ ("Your integer was :" ++) . show
  ]

-- Version 3 changes its state type again to an Int
-- We add another migration function

v3 : IO ()
v3 = mainWithDecode $ decode' 10 [Int, String, Int]
  [ ("Your integer was :" ++) . show
  , cast . length
  ]
