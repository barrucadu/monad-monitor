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
  , evaluateEnd
  , evaluateTree

  -- * Utilities
  , normalise
  , mnot
  , mand
  , mor
  , modal
  , modalBool
  , combine
  ) where

import Control.DeepSeq (NFData(..))
import Data.List (foldl')
import Data.Semigroup(Semigroup(..))
import Data.Tree (Tree(..))

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
--
-- All of the operations which act on two @Modal@ values (such as
-- '<>', '<*>', and '>>=') downgrade the certainty if one argument is
-- @Possibly@.
data Modal a = Certainly a | Possibly a
  deriving (Eq, Ord, Read, Show, Functor)

instance NFData a => NFData (Modal a) where
  rnf (Certainly b) = rnf b
  rnf (Possibly  b) = rnf b

instance Semigroup a => Semigroup (Modal a) where
  (<>) = combine (Data.Semigroup.<>)

instance (Semigroup a, Monoid a) => Monoid (Modal a) where
  mappend = (Data.Semigroup.<>)
  mempty = Certainly mempty

instance Applicative Modal where
  pure = Certainly
  (<*>) = combine ($)

instance Monad Modal where
  return = pure
  Certainly a >>= f = f a
  Possibly a >>= f = case f a of
    Certainly x -> Possibly x
    x -> x

instance Foldable Modal where
  foldMap f = f . modal id id

instance Traversable Modal where
  traverse f (Certainly a) = Certainly <$> f a
  traverse f (Possibly  a) = Possibly  <$> f a

-- | Logical negation.
mnot :: Modal Bool -> Modal Bool
mnot (Certainly b) = Possibly  (not b)
mnot (Possibly  b) = Certainly (not b)

-- | Logical conjunction.
mand :: Modal Bool -> Modal Bool -> Modal Bool
mand = combine (&&)

-- | Logical disjunction
mor :: Modal Bool -> Modal Bool -> Modal Bool
mor = combine (||)

-- | Eliminate a @Modal@.
modal :: (a -> b) -> (a -> b) -> Modal a -> b
modal f _ (Certainly a) = f a
modal _ f (Possibly  a) = f a

-- | Eliminate a @Modal Bool@.
modalBool :: a -> a -> a -> a -> Modal Bool -> a
modalBool ct cf pt pf =
  modal (\b -> if b then ct else cf) (\b -> if b then pt else pf)

-- | Combine two @Modal@ values by downgrading the certainty to the
-- weakest of the two.
combine :: (a -> b -> c) -> Modal a -> Modal b -> Modal c
combine f (Certainly b1) (Certainly b2) = Certainly (f b1 b2)
combine f (Certainly b1) (Possibly  b2) = Possibly  (f b1 b2)
combine f (Possibly  b1) (Certainly b2) = Possibly  (f b1 b2)
combine f (Possibly  b1) (Possibly  b2) = Possibly  (f b1 b2)

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
evaluate = evaluateIsEndFail False

-- | Variant of 'evaluate' which has the knowledge that the
-- computation is over. This means that all @Until@ predicates with an
-- unproven right-hand side are actually false; and all @Release@
-- predicates with a proven left-hand side are actually true (unless
-- the right-hand side is now false).
--
-- This does not mean that the entire expression will evaluate to a
-- boolean, however. It might result in a formula which could neither
-- be proven nor disproven in this execution. A reasonable
-- interpretation of this depends on context, but \"true\" is probably
-- suitable for most cases.
evaluateEnd :: (Eq event, Foldable f)
  => Property event
  -> f event
  -> Either (Property event) (Modal Bool)
evaluateEnd = evaluateIsEndFail True

evaluateIsEndFail :: (Eq event, Foldable f)
  => Bool
  -> Property event
  -> f event
  -> Either (Property event) (Modal Bool)
evaluateIsEndFail isEnd prop events = evaluateSP (normalise prop) where
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
  evaluateSP (All phi) = case evaluatePPHere isEnd events phi of
    Right True  -> Right (Possibly True)
    Right False -> Right (Certainly False)
    Left phi' -> Left (All phi')
  evaluateSP (Exists phi) = case evaluatePPHere isEnd events phi of
    Right True  -> Right (Certainly True)
    Right False -> Right (Possibly False)
    Left phi' -> Left (Exists phi')

-- | Evaluate a formula against a complete execution tree.
--
-- If @Nothing@, the formula could not be fully evaluated: the
-- computation terminated before it reached a truth value. Note that
-- the tree is assumed to be complete, like 'evaluateEnd', so
-- 'Finally' and 'Until' will be evaluated more than just applying
-- 'evaluate' to all the paths.
evaluateTree :: (Eq event, Foldable f)
  => (f event -> a -> f event)
  -- ^ Add and remove events depending on the value at a node.
  -> f event
  -- ^ The initially active enabled.
  -> Property event
  -> Tree a
  -> Maybe Bool
evaluateTree estep initial prop = eitherToMaybe . eval initial (Right $ normalise prop) where
  -- Either PathProp StateProp
  eval es prop (Node a children) =
    let events = estep es a
    in either (evaluatePP children events) (evaluateSP children events) prop

  -- Evaluate a state formula against a tree.
  evaluateSP cs es (SNot phi) = case evaluateSP cs es phi of
    Right b    -> Right (not  b)
    Left  phi' -> Left  (SNot phi')
  evaluateSP cs es (SAnd phi psi) = case (evaluateSP cs es phi, evaluateSP cs es psi) of
    (Right b1,   Right b2)  -> Right (b1 && b2)
    (Left  phi', Right b2)  -> if b2 then Left phi' else Right False
    (Right b1,   Left psi') -> if b1 then Left psi' else Right False
    (Left  phi', Left psi') -> Left (SAnd phi' psi')
  evaluateSP cs es (SOr phi psi) = case (evaluateSP cs es phi, evaluateSP cs es psi) of
    (Right b1,   Right b2)  -> Right (b1 && b2)
    (Left  phi', Right b2)  -> if b2 then Right True else Left phi'
    (Right b1,   Left psi') -> if b1 then Right True else Left psi'
    (Left  phi', Left psi') -> Left (SAnd phi' psi')
  evaluateSP cs es (All    phi) = evalAll    cs es (Left phi)
  evaluateSP cs es (Exists phi) = evalExists cs es (Left phi)

  -- Evaluate a path formula against a tree.
  evaluatePP cs es phi =
    let isEnd = null cs
        evaluated = evaluatePPHere isEnd es phi
    in either (evalAll cs es . Left) Right evaluated

  -- Check a formula holds for every tree in a forest.
  evalAll cs es phi = foldl' go (Right True) cs where
    go (Right False) _ = Right False
    go (Right True) tree = eval es phi tree
    go (Left psi) tree = case eval es phi tree of
      Right True  -> Left psi
      Right False -> Right False
      Left phi'   -> Left (SAnd psi phi')

  -- Check a formula holds for at least one tree in a forest.
  evalExists cs es phi = foldl' go (Right False) cs where
    go (Right True) _ = Right True
    go (Right False) tree = eval es phi tree
    go (Left psi) tree = case eval es phi tree of
      Right True  -> Right True
      Right False -> Left psi
      Left phi'   -> Left (SOr psi phi')

-------------------------------------------------------------------------------

-- | Evaluate a normalised path formula against a collection of
-- events.
evaluatePPHere :: (Eq event, Foldable f)
  => Bool
  -> f event
  -> PathProp event
  -> Either (PathProp event) Bool
evaluatePPHere isEnd events = eval where
  eval TTrue = Right True
  eval FFalse = Right False
  eval (Event event) = Right (event `elem` events)
  eval (Next phi) = Left phi
  eval (PNot phi) = either (Left . PNot) (Right . not) (eval phi)
  eval  (PAnd phi psi) = case (eval phi, eval psi) of
    (o, Right True)  -> o
    (_, Right False) -> Right False
    (Right True, o)  -> o
    (Right False, _) -> Right False
    (Left phi', Left psi') -> Left (PAnd phi' psi')
  eval (POr phi psi) = case (eval phi, eval psi) of
    (_, Right True)  -> Right True
    (o, Right False) -> o
    (Right True, _)  -> Right True
    (Right False, o) -> o
    (Left phi', Left psi') -> Left (POr phi' psi')
  eval u@(Until phi psi)
    | isEnd = case eval psi of
      Right True -> Right True
      _ -> Right False
    | otherwise = case eval psi of
      Right True -> Right True
      Right False -> case eval phi of
        Right True  -> Left u
        Right False -> Right False
        Left phi' -> Left (PAnd phi' u)
      Left psi' -> case eval phi of
        Right True  -> Left (POr psi' u)
        Right False -> Left psi'
        Left phi' -> Left (POr psi' (PAnd phi' u))
  eval r@(Release phi psi) = case eval psi of
    Right True -> case eval phi of
      Right True  -> Right True
      Right False -> Left r
      Left phi'
        | isEnd && eval phi == Right True -> Right True
        | otherwise -> Left (POr phi' (Until phi psi))
    Right False -> Right False
    Left psi' -> case eval phi of
      Right True
        | isEnd -> Right True
        | otherwise -> Left psi'
      Right False -> Left (PAnd psi' r)
      Left phi' -> Left (PAnd psi' (POr phi' (Until phi psi)))

-- | Forget @Left@ values.
eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe = either (const Nothing) Just
