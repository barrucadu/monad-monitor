{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Systematic testing for temporal properties of concurrent
-- programs.
module Test.DejaFu.Temporal
  ( -- * Testing
    Falsified(..)
  , FailedProp(..)
  , testTemporal
  , testTemporalIO
  -- * Computation trees
  , Comptree
  , comptreeOf
  , comptreeOfIO
  -- * Utilities
  , allOk
  , makeTreeFrom
  ) where

import Control.DeepSeq (NFData(..))
import Control.Monad.Conc.Class (MonadConc, atomically)
import Control.Monad.Monitor
import Control.Monad.Monitor.Property (evaluateTree)
import Control.Monad.STM.Class (readCTVar)
import Data.Function (on)
import Data.List (groupBy, sortBy)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import Data.Ord (comparing)
import qualified Data.Set as S
import Data.Tree (Tree(..))
import Test.DejaFu (defaultBounds, defaultMemType)
import Test.DejaFu.Deterministic (ConcIO, ConcST, Failure, Trace)
import Test.DejaFu.SCT (sctBound, sctBoundIO)

import Unsafe.Coerce (unsafeCoerce)

newtype Falsified event = Falsified (Map (Property event) (FailedProp event))
  deriving (Eq, Read, Show, NFData)

data FailedProp event = FailedProp
  { propMsg :: String
  , propSev :: Severity
  , failingTree :: Comptree event
  }
  deriving (Eq, Read, Show)

instance NFData event => NFData (FailedProp event) where
  rnf fp = rnf (propMsg fp, propSev fp, failingTree fp)

-- | Systematically test the temporal properties of a program.
--
-- Properties which could not be proven true or false are discarded.
testTemporal :: Ord event
  => (forall t. ConcurrentMonitoringT event (ConcST t) a)
  -- ^ The computation to test.
  -> Falsified event
testTemporal ma = maybe allOk checkTreeProps $ comptreeOf ma

-- | Variant of 'testTemporal' for computations which do @IO@.
--
-- The usual reservations of @IO@ with dejafu apply: it should be
-- deterministic when parameterised with a fixed set of scheduling
-- decisions; it should not be able to block on the action of another
-- thread; and it should not have any relaxed memory behaviour.
testTemporalIO :: Ord event
  => ConcurrentMonitoringT event ConcIO a
  -> IO (Falsified event)
testTemporalIO ma = maybe allOk checkTreeProps <$> comptreeOfIO ma

-------------------------------------------------------------------------------

-- | A tree representing all possible executions of a computation.
--
-- Each node in the tree contains: a new property that was registered;
-- a collection of events that were started; or a collection of events
-- that were stopped.
type Comptree event = Tree (Either (String, Severity, Property event) (TraceItem event))

-- | Produce the tree of a computation.
--
-- Returns @Nothing@ if the computation does not start any events or
-- monitor any properties.
comptreeOf :: forall event a. Ord event
  => (forall t. ConcurrentMonitoringT event (ConcST t) a)
  -- ^ The computation to run.
  -> Maybe (Comptree event)
comptreeOf ma = makeCTreeFrom $ sctBound'
  (runConcurrentMonitoringT (\_ _ -> pure ()) $ ma >> getState)

  where
    -- Nasty. I need to expose a @sctBound@ function that keeps the
    -- result in @ST t@, which should solve these composability
    -- problems: do everything in @ST t@ then @runST@ at the very end.
    sctBound' :: ConcST t (MonitoringState event) -> [(Either Failure (MonitoringState event), Trace)]
    sctBound' = unsafeCoerce $ sctBound defaultMemType defaultBounds

-- | Variant of 'comptreeOf' for computations which do @IO@.
comptreeOfIO :: Ord event
  => ConcurrentMonitoringT event ConcIO a
  -> IO (Maybe (Comptree event))
comptreeOfIO ma = makeCTreeFrom <$>
  sctBoundIO defaultMemType defaultBounds
  (runConcurrentMonitoringT (\_ _ -> pure ()) $ ma >> getState)

-------------------------------------------------------------------------------

-- | Wrapper around 'makeTreeFrom' to deal with the dejafu cruft.
--
-- Discards executions that end in failure.
makeCTreeFrom :: Ord event
  => [(Either failure (MonitoringState event), trace)]
  -> Maybe (Comptree event)
makeCTreeFrom traces = makeTreeFrom evtraces where
  evtraces = [ reverse (evtrace state) | (Right state, _) <- traces ]

-- | Construct a tree from a list of paths from the root to a leaf.
--
-- Returns @Nothing@ if the list of paths is empty.
--
-- This assumes that (1) every path has at least one initial element
-- in common; and that (2) no path is a prefix of another.
makeTreeFrom :: Ord a => [[a]] -> Maybe (Tree a)
makeTreeFrom [] = Nothing
makeTreeFrom ts = Just $ go (ordNub $ map tail ts) (head $ head ts) where
  -- Construct a tree node given the paths and the label.
  go paths label =
    Node label . mapMaybe makeTreeFrom . groupByHead . filter (not . null) $ paths

-- | Check properties over a computation tree.
checkTreeProps :: Ord event => Comptree event -> Falsified event
checkTreeProps ctree = Falsified failures where
  -- The failing cases
  failures = M.fromList
    [ (prop, failure) | ((msg, sev, prop), es, subtree) <- propTrees
    , evaluateTree step es prop subtree == Just False
    , let failure = FailedProp msg sev subtree
    ]

  -- All properties, the active events at that point, and the subtree
  -- in which to check the property.
  propTrees = go S.empty ctree where
    go es n@(Node (Left prop) cs) = (prop, es, n) : concatMap (go es) cs
    go es   (Node v cs) = concatMap (go $ step es v) cs

  -- Keep track of which events are active
  step es (Right (Start evs)) = es `S.union`      S.fromList evs
  step es (Right (Stop  evs)) = es `S.difference` S.fromList evs
  step es (Left _) = es

-------------------------------------------------------------------------------

-- | Nothing falsified.
allOk :: Falsified event
allOk = Falsified M.empty

-- | Get the monitoring state
getState :: MonadConc m => ConcurrentMonitoringT event m (MonitoringState event)
getState = ConcurrentMonitoringT $ \var _ -> atomically (readCTVar var)

-- | Sort and remove duplicates from a list
ordNub :: Ord a => [a] -> [a]
ordNub = S.toList . S.fromList

-- | Group based on initial element
--
-- Assumes that none of the sublists are empty.
groupByHead :: Ord a => [[a]] -> [[[a]]]
groupByHead = groupBy ((==) `on` head) . sortBy (comparing head)
