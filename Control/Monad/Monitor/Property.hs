{-# LANGUAGE DeriveFunctor #-}

-- | An (almost) implementation of CTL* properties, for monitoring
-- program executions.
--
-- CTL* is a logic for talking about time, both branching and linear,
-- in addition to the normal true, false, and, or, not operations it
-- has some expressing properties of the future evolution of the
-- system. These operations are divided into state formulae:
--
-- - @A φ@ (or 'All') expresses that the path formula @φ@ must hold in
--   all possible executions from this point onwards. It can also be
--   read as \"inevitably\". In general, it is not possible to prove
--   an @A@ predicate by observing a single execution, only disprove.
--
-- - @E φ@ (or 'Exists') expresses that the path formula @φ@ must hold
--   in at least one possible execution from this point onwards. It
--   can also be read as \"possibly\". In general, it is not possible
--   to disprove an @E@ predicate by observing a single execution,
--   only prove.
--
-- And path formulae:
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
-- There are some derived path operations provided as functions:
--
-- - @F φ@ (or 'finally') expresses that φ has to hold somewhere on
--   the subsequent path.
--
-- - @G φ@ (or 'globally') expresses that φ must hold in the entire
--   subsequent execution.
--
-- This module does not implement full CTL*, as CTL* in general allows
-- the @A@ and @E@ quantifiers to be nested, which is forbidden here
-- to simplify the implementation of evaluation. Hopefully a nice way
-- to support this will occur to me one day.
--
-- The implementation of this module draws heavily from \"Runtime
-- Verification of Haskell Programs\" [Solz & Huch, 2005].
module Control.Monad.Monitor.Property
  ( -- * Properties
    Property
  , StateProp(..)
  , PathProp(..)
  , finally
  , globally

  -- * Evaluation
  , Modal(..)
  , evaluate

  -- * Utilities
  , normalise
  , mnot
  , mand
  , mor
  , modal
  , modalBool
  ) where

import Control.DeepSeq (NFData(..))

-------------------------------------------------------------------------------
-- State and path formulae

-- | The type of CTL* formulae.
type Property = StateProp

-- | State formlae.
data StateProp event
  = SNot (StateProp event)
  -- ^ Negation
  | SAnd (StateProp event) (StateProp event)
  -- ^ Conjunction
  | SOr (StateProp event) (StateProp event)
  -- ^ Disjunction
  | All (PathProp event)
  -- ^ @All phi@ expresses that the path formula @phi@ must hold in
  -- all possible executions from this point onwards. It can also be
  -- read as \"inevitably\". In general, it is not possible to prove
  -- an @All@ predicate by observing a single execution, only
  -- disprove.
  | Exists (PathProp event)
  -- ^ @Exists phi@ expresses that the path formula @phi@ must hold in
  -- at least one possible execution from this point onwards. It can
  -- also be read as \"possibly\". In general, it is not possible to
  -- disprove an @E@ predicate by observing a single execution, only
  -- prove.
  deriving (Eq, Ord, Read, Show, Functor)

instance NFData event => NFData (StateProp event) where
  rnf (SAnd p1 p2) = rnf (p1, p2)
  rnf (SOr  p1 p2) = rnf (p1, p2)
  rnf (Exists p) = rnf p
  rnf (SNot p) = rnf p
  rnf (All  p) = rnf p

-- | Path formulae.
data PathProp event
  = TTrue
  -- ^ A literal true.
  | FFalse
  -- ^ A literal false.
  | Event event
  -- ^ An event is currently active.
  | PNot (PathProp event)
  -- ^ Negation
  | PAnd (PathProp event) (PathProp event)
  -- ^ Conjunction
  | POr (PathProp event) (PathProp event)
  -- ^ Disjunction
  | Next (PathProp event)
  -- ^ @Next phi@ expresses that the formula @phi@ must hold in the
  -- next time step. In the case of this library, that will be after
  -- the next time the events or properties are modified.
  | Until (PathProp event) (PathProp event)
  -- ^ @Until phi psi@ expresses that the formula @phi@ must hold at
  -- least until @phi@ does, and that @psi@ must hold at some future
  -- point.
  | Release (PathProp event) (PathProp event)
  -- ^ @Release phi psi@ expresses that the formula @psi@ must hold up
  -- to and including the point where @phi@ does, but @phi@ does not
  -- necessarily ever need to hold.
  deriving (Eq, Ord, Read, Show, Functor)

instance NFData event => NFData (PathProp event) where
  rnf (Release p1 p2) = rnf (p1, p2)
  rnf (Until   p1 p2) = rnf (p1, p2)
  rnf (PAnd p1 p2) = rnf (p1, p2)
  rnf (POr  p1 p2) = rnf (p1, p2)
  rnf (Event e) = rnf e
  rnf (Next  p) = rnf p
  rnf (PNot  p) = rnf p
  rnf x = x `seq` ()

-- | @finally phi@ expresses that @phi@ has to hold somewhere on
-- the subsequent path.
finally :: PathProp event -> PathProp event
finally = Until TTrue

-- | @globally phi@ expresses that @phi@ must hold in the entire
-- subsequent execution.
globally :: PathProp event -> PathProp event
globally = PNot . finally . PNot

-- | Convert a formula into negation normal form: push negationss in
-- as far as possible, converting between operators as necessary.
normalise :: Property a -> Property a
normalise = normaliseSP where
  normaliseSP (All    phi) = All    (normalisePP phi)
  normaliseSP (Exists phi) = Exists (normalisePP phi)
  normaliseSP (SAnd phi psi) = SAnd (normaliseSP phi) (normaliseSP psi)
  normaliseSP (SOr  phi psi) = SOr  (normaliseSP phi) (normaliseSP psi)
  normaliseSP (SNot (All    phi)) = Exists (normalisePP (PNot phi))
  normaliseSP (SNot (Exists phi)) = All    (normalisePP (PNot phi))
  normaliseSP (SNot (SAnd phi psi)) = SOr  (normaliseSP (SNot phi)) (normaliseSP (SNot psi))
  normaliseSP (SNot (SOr  phi psi)) = SAnd (normaliseSP (SNot phi)) (normaliseSP (SNot psi))
  normaliseSP (SNot (SNot phi)) = normaliseSP phi

  normalisePP (Next  phi) = Next  (normalisePP phi)
  normalisePP (Release phi psi) = Release (normalisePP phi) (normalisePP psi)
  normalisePP (Until   phi psi) = Until   (normalisePP phi) (normalisePP psi)
  normalisePP (PAnd phi psi) = PAnd (normalisePP phi) (normalisePP psi)
  normalisePP (POr  phi psi) = POr  (normalisePP phi) (normalisePP psi)
  normalisePP (PNot (Next  phi)) = Next  (normalisePP (PNot phi))
  normalisePP (PNot (PNot  phi)) = normalisePP phi
  normalisePP (PNot (Release phi psi)) = Until   (normalisePP (PNot phi)) (normalisePP (PNot psi))
  normalisePP (PNot (Until   phi psi)) = Release (normalisePP (PNot phi)) (normalisePP (PNot psi))
  normalisePP (PNot (PAnd phi psi)) = POr  (normalisePP (PNot phi)) (normalisePP (PNot psi))
  normalisePP (PNot (POr  phi psi)) = PAnd (normalisePP (PNot phi)) (normalisePP (PNot psi))
  normalisePP (PNot TTrue) = FFalse
  normalisePP (PNot FFalse) = TTrue
  normalisePP x = x

-------------------------------------------------------------------------------
-- Modal logic

-- | Values which may only possibly be the case.
--
-- Because of the quantifiers 'All' and 'Exists', it might be the case
-- that a property cannot be conclusively proven or disproven by
-- examining a single execution:
--
-- - @Possibly True@ can be produced by reducing a property to
--   @All TTrue@.
--
-- - @Possibly False@ can be produced by reducing a property to
--   @Exists FFalse@.
--
-- These are only \"possible\" values, because in a different
-- execution with a different sequence of events, the properties could
-- have evolved in a different way giving the other result. Only by
-- examining all results can a possibility become a certainty.
data Modal a = Certainly a | Possibly a
  deriving (Eq, Ord, Read, Show, Functor)

instance NFData a => NFData (Modal a) where
  rnf (Certainly b) = rnf b
  rnf (Possibly  b) = rnf b

-- | Logical negation.
mnot :: Modal Bool -> Modal Bool
mnot (Certainly b) = Possibly  (not b)
mnot (Possibly  b) = Certainly (not b)

-- | Logical conjunction.
mand :: Modal Bool -> Modal Bool -> Modal Bool
mand (Certainly b1) (Certainly b2) = Certainly (b1 && b2)
mand (Certainly b1) (Possibly  b2) = Possibly  (b1 && b2)
mand (Possibly  b1) (Certainly b2) = Possibly  (b1 && b2)
mand (Possibly  b1) (Possibly  b2) = Possibly  (b1 && b2)

-- | Logical disjunction
mor :: Modal Bool -> Modal Bool -> Modal Bool
mor (Certainly b1) (Certainly b2) = Certainly (b1 || b2)
mor (Certainly b1) (Possibly  b2) = Possibly  (b1 || b2)
mor (Possibly  b1) (Certainly b2) = Possibly  (b1 || b2)
mor (Possibly  b1) (Possibly  b2) = Possibly  (b1 || b2)

-- | Eliminate a @Modal@.
modal :: (a -> b) -> (a -> b) -> Modal a -> b
modal f _ (Certainly a) = f a
modal _ f (Possibly  a) = f a

-- | Eliminate a @Modal Bool@.
modalBool :: a -> a -> a -> a -> Modal Bool -> a
modalBool ct cf pt pf =
  modal (\b -> if b then ct else cf) (\b -> if b then pt else pf)

-------------------------------------------------------------------------------

-- | Evaluate a formula, this can have one of a number of different
-- results, depending on the use of quantifiers in the formula.
--
-- If @Left@, the new formula should replace the current one and be
-- checked against the subsequent execution.
evaluate :: (Eq event, Foldable f)
  => Property event
  -> f event
  -> Either (Property event) (Modal Bool)
evaluate prop events = evaluateSP (normalise prop) where
  evaluateSP (SNot phi) = either (Left . SNot) (Right . mnot) (evaluateSP phi)
  evaluateSP (SAnd phi psi) =
    let elim = modalBool
                 Left
                 (const (Right (Certainly False)))
                 (Left . SAnd (All TTrue))
                 (Left . SAnd (Exists FFalse))
    in case (evaluateSP phi, evaluateSP psi) of
         (Right mb1, Right mb2) -> Right (mand mb1 mb2)
         (Right mb1, Left psi') -> elim mb1 psi'
         (Left phi', Right mb2) -> elim mb2 phi'
         (Left phi', Left psi') -> Left (SAnd phi' psi')
  evaluateSP (SOr phi psi) =
    let elim = modalBool
                 (const (Right (Certainly True)))
                 Left
                 (Left . SOr (All TTrue))
                 (Left . SOr (Exists FFalse))
    in case (evaluateSP phi, evaluateSP psi) of
         (Right mb1, Right mb2) -> Right (mor mb1 mb2)
         (Right mb1, Left psi') -> elim mb1 psi'
         (Left phi', Right mb2) -> elim mb2 phi'
         (Left phi', Left psi') -> Left (SOr phi' psi')
  evaluateSP (All phi) = case evaluatePP phi of
    Right True  -> Right (Possibly True)
    Right False -> Right (Certainly False)
    Left phi' -> Left (All phi')
  evaluateSP (Exists phi) = case evaluatePP phi of
    Right True  -> Right (Certainly True)
    Right False -> Right (Possibly False)
    Left phi' -> Left (Exists phi')

  evaluatePP TTrue = Right True
  evaluatePP FFalse = Right False
  evaluatePP (Event event) = Right (event `elem` events)
  evaluatePP (Next phi) = Left phi
  evaluatePP (PNot phi) = either (Left . PNot) (Right . not) (evaluatePP phi)
  evaluatePP (PAnd phi psi) = case (evaluatePP phi, evaluatePP psi) of
    (o, Right True)  -> o
    (_, Right False) -> Right False
    (Right True, o)  -> o
    (Right False, _) -> Right False
    (Left phi', Left psi') -> Left (PAnd phi' psi')
  evaluatePP (POr phi psi) = case (evaluatePP phi, evaluatePP psi) of
    (_, Right True)  -> Right True
    (o, Right False) -> o
    (Right True, _)  -> Right True
    (Right False, o) -> o
    (Left phi', Left psi') -> Left (POr phi' psi')
  evaluatePP u@(Until phi psi) = case evaluatePP psi of
    Right True -> Right True
    Right False -> case evaluatePP phi of
      Right True  -> Left u
      Right False -> Right False
      Left phi' -> Left (PAnd phi' u)
    Left psi' -> case evaluatePP phi of
      Right True  -> Left (POr psi' u)
      Right False -> Left psi'
      Left phi' -> Left (POr psi' (PAnd phi' u))
  evaluatePP r@(Release phi psi) = case evaluatePP psi of
    Right True -> case evaluatePP phi of
      Right True  -> Right True
      Right False -> Left r
      Left phi' -> Left (POr phi' (Until phi psi))
    Right False -> Right False
    Left psi' -> case evaluatePP phi of
      Right True  -> Left psi'
      Right False -> Left (PAnd psi' r)
      Left phi' -> Left (PAnd psi' (POr phi' (Until phi psi)))
