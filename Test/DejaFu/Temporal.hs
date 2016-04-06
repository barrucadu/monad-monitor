{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Systematic testing for temporal properties of concurrent
-- programs.
module Test.DejaFu.Temporal
  ( Falsified(..)
  , FailedProp(..)
  , testTemporal
  , testTemporalIO
  ) where

import Control.DeepSeq (NFData(..))
import Control.Monad.Conc.Class (MonadConc, atomically)
import Control.Monad.Monitor
import Control.Monad.Monitor.Property (Modal(..))
import Control.Monad.STM.Class (readCTVar)
import Data.List (partition)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import Test.DejaFu (defaultBounds, defaultMemType)
import Test.DejaFu.Deterministic (ConcIO, ConcST, Failure, Trace)
import Test.DejaFu.SCT (sctBound, sctBoundIO)

import Unsafe.Coerce (unsafeCoerce)

newtype Falsified event = Falsified (Map (Property event) (FailedProp event))
  deriving (Eq, Ord, Read, Show)

instance NFData event => NFData (Falsified event) where
  rnf (Falsified fs) = rnf fs

data FailedProp event = FailedProp
  { propMsg :: String
  , propSev :: Severity
  , failingTraces :: [([TraceItem event], Int)]
  -- ^ The traces leading to this failure, with the index of the
  -- failing start/stop action.
  }
  deriving (Eq, Ord, Read, Show, Functor)

instance NFData event => NFData (FailedProp event) where
  rnf fp = rnf (propMsg fp, propSev fp, failingTraces fp)

-- | Systematically test the temporal properties of a program.
--
-- The two modal results, @Possibly True@ and @Possibly False@ are
-- handled specially: if every result for a property is @Possibly
-- False@, the overall result is @False@; and similarly for @Possibly
-- True@. The same property can never evaluate to @Possibly True@ and
-- @Possibly False@ in different executions, as @Possibly True@ is
-- only introduced for @All@ and @Possibly False@ for @Exists@.
--
-- Properties which could not be proven true or false are discarded.
testTemporal :: forall event a. Ord event
  => (forall t. ConcurrentMonitoringT event (ConcST t) a)
  -- ^ The computation to test.
  -> Falsified event
testTemporal ma = processResults $ sctBound'
  (runConcurrentMonitoringT (\_ _ -> pure ()) $ ma >> getState)

  where
    -- Nasty. I need to expose a @sctBound@ function that keeps the
    -- result in @ST t@, which should solve these composability
    -- problems: do everything in @ST t@ then @runST@ at the very end.
    sctBound' :: ConcST t (MonitoringState event) -> [(Either Failure (MonitoringState event), Trace)]
    sctBound' = unsafeCoerce $ sctBound defaultMemType defaultBounds

-- | Variant of 'testTemporal' for computations which do @IO@.
--
-- The usual reservations of @IO@ with dejafu apply: it should be
-- deterministic when parameterised with a fixed set of scheduling
-- decisions; it should not be able to block on the action of another
-- thread; and it should not have any relaxed memory behaviour.
testTemporalIO :: Ord event
  => ConcurrentMonitoringT event ConcIO a
  -> IO (Falsified event)
testTemporalIO ma = processResults <$>
  sctBoundIO defaultMemType defaultBounds
  (runConcurrentMonitoringT (\_ _ -> pure ()) $ ma >> getState)

-------------------------------------------------------------------------------

-- | Turn the results of executing under dejafu into a @Falsified@.
processResults :: Ord event
  => [(Either f (MonitoringState event), t)]
  -> Falsified event
processResults results = Falsified $ M.fromList
  [ (prop, FailedProp msg sev failures)
  | (prop, (msg, sev, _)) <- concatMap (M.toList . properties) allStates
  , let failures = ordNub (collapse $ allResults prop)
  , not (null failures)
  ]

  where
    -- All states
    allStates = mapMaybe (either (const Nothing) Just . fst) results

    -- All results, + the trace, of a property.
    allResults prop = flip mapMaybe allStates $
      \state -> case M.lookup prop (properties state) of
        Just (_, _, res) -> Just (res, reverse $ evtrace state)
        _ -> Nothing

    -- Collapse all @Possibly@ results into a @Certainly@ (or throw
    -- away due to not enough information).
    collapse rs = case partition (isComputing . fst) rs of
      (computing, done) -> case partition (isCertain . fst) done of
        -- If there are some results still computing, we don't have
        -- enough information to certainly say what the \"possibly\"
        -- case should be.
        (certain, possible)
          | null computing -> pFails possible ++ cFails certain
          | otherwise -> cFails certain

    -- Check if a result is still computing or not.
    isComputing (Computing _)  = True
    isComputing _ = False

    -- Check if a result is certain or not.
    isCertain (Finished (Certainly _) _) = True
    isCertain _ = False

    -- Only keep certain failure cases.
    cFails rs = [ (trace, i - 1) | (Finished (Certainly False) i, trace) <- rs ]

    -- Only keep possible failure cases.
    pFails rs = [ (trace, i - 1) | (Finished (Possibly False) i, trace) <- rs ]

-------------------------------------------------------------------------------

-- | Get the monitoring state
getState :: MonadConc m => ConcurrentMonitoringT event m (MonitoringState event)
getState = ConcurrentMonitoringT $ \var _ -> atomically (readCTVar var)

-- | Sort and remove duplicates from a list
ordNub :: Ord a => [a] -> [a]
ordNub = S.toList . S.fromList
