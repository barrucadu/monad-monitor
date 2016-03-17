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
-- The implementation of this module draws heavily from \"Runtime
-- Verification of Haskell Programs\" [Solz & Huch, 2005].
module Control.Monad.Monitor.LTL
  ( -- * Properties
    LTL(..)
  , normalise

  -- ** Derived operations
  , finally
  , globally

  -- * Evaluation
  , evaluateLTL
  , propFromLTL
  ) where

import Data.Set (Set)
import qualified Data.Set as S

-- local imports
import Control.Monad.Monitor (PropResult(..))

-------------------------------------------------------------------------------

-- | The type of linear temporal logic formulae.
data LTL event
  = Bool Bool
  -- ^ A literal true or false.
  | Event event
  -- ^ An event is currently active.
  | Not (LTL event)
  -- ^ Negation
  | And (LTL event) (LTL event)
  -- ^ Conjunction
  | Or (LTL event) (LTL event)
  -- ^ Disjunction
  | Next (LTL event)
  -- ^ A property holds in the next step.
  | Until (LTL event) (LTL event)
  -- ^ The first property has to hold until at least the second does,
  -- which holds at the current or some future position.
  | Release (LTL event) (LTL event)
  -- ^ The second property has to hold until and including the point
  -- where the first does, which does not necessarily ever hold.
  deriving (Eq, Read, Show)

-- | A property has to hold at some point in the subsequent execution.
finally :: LTL event -> LTL event
finally = Until (Bool True)

-- | The property has to hold in the entire subsequent execution.
globally :: LTL event -> LTL event
globally = Not . finally . Not

-- | Normalise a given LTL formula: push @Not@s in as far as possible;
-- convert between @Release@/@Until@ and @And@/@Or@, and normalise all
-- subexpressions.
normalise :: LTL a -> LTL a
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
-- - @Left ltl@: neither true nor false, the new formula should be
--   checked against the subsequent execution.
evaluateLTL :: Ord event => LTL event -> Set event -> Either (LTL event) Bool
evaluateLTL ltl events = eval (normalise ltl) where
  eval (Bool b) = Right b

  eval (Event event) = Right (event `S.member` events)

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

-- | Convert a formula into a property suitable for the transformers.
--
-- Note that 'PropResult' is strictly more expressive than what is
-- needed for LTL: LTL has no notion of \"true/false at the moment,
-- but might change later\", which is allowed in @PropResult@ by the
-- @CurrentlyTrue@ and @CurrentlyFalse@ constructors.
propFromLTL :: Ord event => LTL event -> Set event -> PropResult event
propFromLTL ltl events = case evaluateLTL ltl events of
  Right True  -> ProvenTrue
  Right False -> ProvenFalse
  Left ltl'   -> Neither (propFromLTL ltl')
