{-# LANGUAGE TypeFamilies #-}

module Control.Monad.Monitor
  ( -- * MonadMonitor
    MonadMonitor(..)

    -- * Helper transformer
  , MonitoringT(..)
  , PropResult(..)
  , runMonitoringT
  , runStdoutMonitoringT
  , runStderrMonitoringT
  , runHandleMonitoringT
  ) where

import Control.Arrow (first, second)
import Control.DeepSeq (NFData(..))
import Control.Monad.Catch (MonadThrow(..), MonadCatch(..), MonadMask(..))
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State.Strict (StateT, evalStateT, get, modify, put)
import Control.Monad.Trans (MonadTrans(..))
import Data.Maybe (catMaybes)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Void (Void)
import System.IO (Handle, hPutStrLn, stderr, stdout)

-- local imports
import Control.Monad.Monitor.Class

-------------------------------------------------------------------------------

-- | Monad transformer that adds monitoring functionality, based on a
-- set of active events.
--
-- The monitoring behaviour here is to check properties hold after all
-- the 'MonadMonitor' operations. A function is required to deal with
-- failed properties.
newtype MonitoringT event m a = MonitoringT
  { unMonitoringT
    :: (Severity -> String -> m ())
    -> StateT (Set event, [(String, Severity, Set event -> PropResult)]) m a
  }

-- | The result of checking a @MonitoringT@ property.
--
-- There are two types of results: proven results, and current
-- results. If a property evaluates to a proven result, this will
-- never change, and so it can be removed from the set that is
-- checked.
data PropResult
  = ProvenTrue
  | ProvenFalse
  | CurrentlyTrue
  | CurrentlyFalse
  deriving (Eq, Ord, Read, Show, Bounded, Enum)

instance NFData PropResult where
  rnf p = p `seq` ()

-- | Run a 'MonitoringT' action with the supplied logging function.
runMonitoringT :: Monad m
  => (Severity -> String -> m ())
  -> MonitoringT event m a
  -> m a
runMonitoringT logf (MonitoringT ma) = evalStateT (ma logf) (S.empty, [])

-- | Run a 'MonitoringT' action which prints messages to stdout.
runStdoutMonitoringT :: MonadIO m => MonitoringT event m a -> m a
runStdoutMonitoringT = runHandleMonitoringT stdout

-- | Run a 'MonitoringT' action which prints messages to stderr.
runStderrMonitoringT :: MonadIO m => MonitoringT event m a -> m a
runStderrMonitoringT = runHandleMonitoringT stderr

-- | Run a 'MonitoringT' action which prints messages to a handle.
runHandleMonitoringT :: MonadIO m => Handle -> MonitoringT event m a -> m a
runHandleMonitoringT handle = runMonitoringT $ \severity message ->
  case severity of
    Info  -> liftIO . hPutStrLn handle $ "[info] "  ++ message
    Warn  -> liftIO . hPutStrLn handle $ "[warn] "  ++ message
    Error -> liftIO . hPutStrLn handle $ "[error] " ++ message

instance Ord event => MonadTrans (MonitoringT event) where
  lift ma = MonitoringT $ \_ -> lift ma

instance (Monad m, Ord event) => Functor (MonitoringT event m) where
  fmap f (MonitoringT ma) = MonitoringT (fmap f . ma)

instance (Monad m, Ord event) => Applicative (MonitoringT event m) where
  pure a = MonitoringT $ \_ -> pure a

  MonitoringT mf <*> MonitoringT ma = MonitoringT $ \logf ->
    mf logf <*> ma logf

instance (Monad m, Ord event) => Monad (MonitoringT event m) where
  return = pure

  MonitoringT ma >>= f = MonitoringT $ \logf -> do
    a <- ma logf
    let MonitoringT f' = f a
    f' logf

instance (MonadThrow m, Ord event) => MonadThrow (MonitoringT event m) where
  throwM = lift . throwM

instance (MonadCatch m, Ord event) => MonadCatch (MonitoringT event m) where
  catch (MonitoringT ma) h = MonitoringT $ \logf -> ma logf `catch` \e -> unMonitoringT (h e) logf

instance (MonadMask m, Ord event) => MonadMask (MonitoringT event m) where
  mask a = MonitoringT $ \logf -> mask $ \u -> unMonitoringT (a $ q u) logf
    where q u (MonitoringT b) = MonitoringT (u . b)

  uninterruptibleMask a = MonitoringT $ \logf ->
    uninterruptibleMask $ \u -> unMonitoringT (a $ q u) logf
    where q u (MonitoringT b) = MonitoringT (u . b)

instance (Monad m, Ord event) => MonadMonitor (MonitoringT event m) where
  type Event (MonitoringT event m) = event
  type Property (MonitoringT event m) = (String, Set event -> PropResult)

  startEvents events = MonitoringT $ \logf -> do
    modify (first (S.union (S.fromList events)))
    checkAll (fst <$> get)
             (snd <$> get)
             (modify . second . const)
             (\sev msg -> lift (logf sev msg))

  stopEvents  events = MonitoringT $ \logf -> do
    modify (first (S.difference (S.fromList events)))
    checkAll (fst <$> get)
             (snd <$> get)
             (modify . second . const)
             (\sev msg -> lift (logf sev msg))

  addPropertyWithSeverity severity (name, checker) = MonitoringT $ \logf -> do
    modify (second ((name, severity, checker) :))
    checkAll (fst <$> get)
             (snd <$> get)
             (modify . second . const)
             (\sev msg -> lift (logf sev msg))

-- | Check the properties
checkAll :: Monad m
  => m (Set event)
  -> m [(String, Severity, Set event -> PropResult)]
  -> ([(String, Severity, Set event -> PropResult)] -> m ())
  -> (Severity -> String -> m ())
  -> m ()
checkAll getEvents getProps setProps logf = do
  es <- getEvents
  ps <- getProps
  ps' <- mapM (check es) ps
  setProps (catMaybes ps')

  where
    check events p@(name, severity, prop) = case prop events of
      ProvenTrue  -> pure Nothing
      ProvenFalse -> logf severity name >> pure Nothing
      CurrentlyTrue  -> pure (Just p)
      CurrentlyFalse -> logf severity name >> pure (Just p)
