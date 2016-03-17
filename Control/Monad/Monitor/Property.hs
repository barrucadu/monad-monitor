-- | An implementation of Linear Temporal Logic (LTL) properties, for
-- monitoring program executions.
--
-- LTL is a logic for talking about time, in addition to the normal
-- true/false/and/or/not operations it has some expressing properties
-- of the future evolution of the system:
--
-- - @X φ@ (or 'Next') expresses that the formula @φ@ must hold in the
--   next time step. In the case of this library, that will be after
--   the next time the events or properties are modified.
--
-- - @φ U ψ@ (or 'Until') expresses that the formula @φ@ must hold at
--   least until @ψ@ does, and that @ψ@ must hold at some future
--   point.
--
-- - @φ R ψ@ (or 'Release') expresses that the formula @ψ@ must hold
--   up to and including the point where @φ@ does, but @φ@ does not
--   necessarily ever need to hold.
--
-- There are some derived operations provided as functions:
--
-- - @F φ@ (or 'finally') expresses that φ has to hold somewhere on
--   the subsequent path.
--
-- - @G φ@ (or 'globally') expresses that φ must hold in the entire
--   subsequent execution.
--
-- The implementation of this module draws heavily from \"Runtime
-- Verification of Haskell Programs\" [Solz & Huch, 2005].
module Control.Monad.Monitor.Property
  ( -- * Properties
    Property(..)
  , evaluateProp
  , normalise

  -- ** Derived operations
  , finally
  , globally
  ) where

-------------------------------------------------------------------------------

-- | The type of linear temporal logic formulae.
data Property event
  = Bool Bool
  -- ^ A literal true or false.
  | Event event
  -- ^ An event is currently active.
  | Not (Property event)
  -- ^ Negation
  | And (Property event) (Property event)
  -- ^ Conjunction
  | Or (Property event) (Property event)
  -- ^ Disjunction
  | Next (Property event)
  -- ^ @Next phi@ expresses that the formula @phi@ must hold in the
  -- next time step. In the case of this library, that will be after
  -- the next time the events or properties are modified.
  | Until (Property event) (Property event)
  -- ^ @Until phi psi@ expresses that the formula @phi@ must hold at
  -- least until @phi@ does, and that @psi@ must hold at some future
  -- point.
  | Release (Property event) (Property event)
  -- ^ @Release phi psi@ expresses that the formula @psi@ must hold up
  -- to and including the point where @phi@ does, but @phi@ does not
  -- necessarily ever need to hold.
  deriving (Eq, Read, Show)

-- | @finally phi@ expresses that @phi@ has to hold somewhere on
-- the subsequent path.
finally :: Property event -> Property event
finally = Until (Bool True)

-- | @globally phi@ expresses that @phi@ must hold in the entire
-- subsequent execution.
globally :: Property event -> Property event
globally = Not . finally . Not

-- | Normalise a given formula: push @Not@s in as far as possible;
-- convert between @Release@/@Until@ and @And@/@Or@, and normalise all
-- subexpressions.
normalise :: Property a -> Property a
normalise (Next phi) = Next (normalise phi)
normalise (phi `Until` psi) = normalise phi `Until` normalise psi
normalise (phi `Release` psi) = normalise phi `Release` normalise psi
normalise (phi `And` psi) = normalise phi `And` normalise psi
normalise (phi `Or` psi) = normalise phi `Or` normalise psi
normalise (Not (Bool b)) = Bool (not b)
normalise (Not (Next phi)) = Next (normalise (Not phi))
normalise (Not (Not phi)) = normalise phi
normalise (Not (phi `Until` psi)) = normalise (Not phi) `Release` normalise (Not psi)
normalise (Not (phi `Release` psi)) = normalise (Not phi) `Until` normalise (Not psi)
normalise (Not (phi `And` psi)) = normalise (Not phi) `Or` normalise (Not psi)
normalise (Not (phi `Or` psi)) = normalise (Not phi) `And` normalise (Not psi)
normalise f = f

-------------------------------------------------------------------------------

-- | Evaluate a formula, this can have one of three different results:
--
-- - @Right True@: proven true,
--
-- - @Right False@: proven false,
--
-- - @Left prop@: neither true nor false, the new formula should be
--   checked against the subsequent execution.
evaluateProp :: (Eq event, Foldable f)
  => Property event
  -> f event
  -> Either (Property event) Bool
evaluateProp prop events = eval (normalise prop) where
  eval (Bool b) = Right b

  eval (Event event) = Right (event `elem` events)

  eval (Not phi) = case eval phi of
    Right b -> Right (not b)
    Left phi' -> Left (Not phi')

  eval (phi `And` psi) = case (eval phi, eval psi) of
    (o, Right True)  -> o
    (_, Right False) -> Right False
    (Right True, o)  -> o
    (Right False, _) -> Right False
    (Left phi', Left psi') -> Left (phi' `And` psi')

  eval (phi `Or` psi) = case (eval phi, eval psi) of
    (_, Right True)  -> Right True
    (o, Right False) -> o
    (Right True, _)  -> Right True
    (Right False, o) -> o
    (Left phi', Left psi') -> Left (phi' `Or` psi')

  eval (Next phi) = Left phi

  eval u@(phi `Until` psi) = case eval psi of
    Right True -> Right True
    Right False -> case eval phi of
      Right True  -> Left u
      Right False -> Right False
      Left phi' -> Left (phi' `And` u)
    Left psi' -> case eval phi of
      Right True  -> Left (psi' `Or` u)
      Right False -> Left psi'
      Left phi' -> Left (psi' `Or` (phi' `And` u))

  eval r@(phi `Release` psi) = case eval psi of
    Right True -> case eval phi of
      Right True  -> Right True
      Right False -> Left r
      Left phi' -> Left (phi' `Or` (phi `Until` psi))
    Right False -> Right False
    Left psi' -> case eval phi of
      Right True  -> Left psi'
      Right False -> Left (psi' `And` r)
      Left phi' -> Left (psi' `And` (phi' `Or` (phi `Until` psi)))
