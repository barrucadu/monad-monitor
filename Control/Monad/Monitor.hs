{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Monad.Monitor
  ( -- * @MonadMonitor@
    MonadMonitor(..)
  , Severity(..)

  -- * Properties
  , Property(..)
  , finally
  , globally

    -- * Helper transformers
  , MonitoringT(..)
  , runMonitoringT
  , runStdoutMonitoringT
  , runStderrMonitoringT
  , runHandleMonitoringT

  , ConcurrentMonitoringT(..)
  , runConcurrentMonitoringT
  , runTracedConcurrentMonitoringT
  , runStdoutConcurrentMonitoringT
  , runStderrConcurrentMonitoringT
  , runHandleConcurrentMonitoringT

  , NoMonitoringT(..)
  ) where

import Control.Arrow (first, second)
import Control.Concurrent.STM.CTVar (modifyCTVar')
import Control.Monad (join)
import Control.Monad.Catch (MonadThrow(..), MonadCatch(..), MonadMask(..))
import Control.Monad.Conc.Class (MonadConc(..))
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State.Strict (StateT, evalStateT, get, modify, put)
import Control.Monad.STM.Class (MonadSTM(..))
import Control.Monad.Trans (MonadTrans(..))
import Data.Maybe (catMaybes, fromMaybe)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable
import Data.Void (Void)
import System.IO (Handle, hPutStrLn, stderr, stdout)

-- local imports
import Control.Monad.Monitor.Class
import Control.Monad.Monitor.Property

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
    -> StateT (Set event, [(String, Severity, Property event)]) m a
  }

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

instance (Monad m, Ord event) => MonadMonitor event (MonitoringT event m) where
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

  addPropertyWithSeverity severity name checker = MonitoringT $ \logf -> do
    modify (second ((name, severity, checker) :))
    checkAll (fst <$> get)
             (snd <$> get)
             (modify . second . const)
             (\sev msg -> lift (logf sev msg))

-------------------------------------------------------------------------------

-- | Monad transformer that adds monitoring functionality to
-- concurrency monads, based on a shared mutable set of active events.
--
-- The monitoring behaviour here is to check properties hold after all
-- the 'MonadMonitor' operations. A function is required to deal with
-- failed properties.
newtype ConcurrentMonitoringT event m a = ConcurrentMonitoringT
  { unConcurrentMonitoringT
    :: ( CTVar (STMLike m) (Set event)
       , CTVar (STMLike m) [(String, Severity, Property event)]
       )
    -> (Severity -> String -> m ())
    -> m a
  }

-- | Run a 'ConcurrentMonitoringT' action with the supplied logging
-- function.
runConcurrentMonitoringT :: MonadConc m
  => (Severity -> String -> m ())
  -> ConcurrentMonitoringT event m a
  -> m a
runConcurrentMonitoringT logf (ConcurrentMonitoringT ma) = do
  evar <- atomically $ newCTVar S.empty
  pvar <- atomically $ newCTVar []
  ma (evar, pvar) logf

-- | The type of detected property violations, logged in the
-- computation trace.
data PropertyViolation event = PropertyViolation !Severity event
  deriving (Eq, Ord, Read, Show)

-- | Run a 'ConcurrentMonitoringT' which uses '_concMessage' to record
-- messages as a 'PropertyViolation'.
runTracedConcurrentMonitoringT :: (MonadConc m, Typeable event)
  => ConcurrentMonitoringT event m a
  -> m a
runTracedConcurrentMonitoringT = runConcurrentMonitoringT $ \sev msg ->
  _concMessage (PropertyViolation sev msg)

-- | Run a 'ConcurrentMonitoringT' action which prints messages to stdout.
runStdoutConcurrentMonitoringT :: (MonadConc m, MonadIO m)
  => ConcurrentMonitoringT event m a
  -> m a
runStdoutConcurrentMonitoringT = runHandleConcurrentMonitoringT stdout

-- | Run a 'ConcurrentMonitoringT' action which prints messages to stderr.
runStderrConcurrentMonitoringT :: (MonadConc m, MonadIO m)
  => ConcurrentMonitoringT event m a
  -> m a
runStderrConcurrentMonitoringT = runHandleConcurrentMonitoringT stderr

-- | Run a 'ConcurrentMonitoringT' action which prints messages to a handle.
runHandleConcurrentMonitoringT :: (MonadConc m, MonadIO m)
  => Handle
  -> ConcurrentMonitoringT event m a
  -> m a
runHandleConcurrentMonitoringT handle = runConcurrentMonitoringT $ \sev msg ->
  case sev of
    Info  -> liftIO . hPutStrLn handle $ "[info] "  ++ msg
    Warn  -> liftIO . hPutStrLn handle $ "[warn] "  ++ msg
    Error -> liftIO . hPutStrLn handle $ "[error] " ++ msg

instance Ord event => MonadTrans (ConcurrentMonitoringT event) where
  lift ma = ConcurrentMonitoringT $ \_ _ -> ma

instance (MonadConc m, Ord event) => Functor (ConcurrentMonitoringT event m) where
  fmap f (ConcurrentMonitoringT ma) = ConcurrentMonitoringT $
    \vars logf -> fmap f (ma vars logf)

instance (MonadConc m, Ord event) => Applicative (ConcurrentMonitoringT event m) where
  pure a = ConcurrentMonitoringT $ \_ _ -> pure a

  ConcurrentMonitoringT mf <*> ConcurrentMonitoringT ma = ConcurrentMonitoringT $
    \vars logf -> mf vars logf <*> ma vars logf

instance (MonadConc m, Ord event) => Monad (ConcurrentMonitoringT event m) where
  return = pure

  ConcurrentMonitoringT ma >>= f = ConcurrentMonitoringT $ \vars logf -> do
    a <- ma vars logf
    let ConcurrentMonitoringT f' = f a
    f' vars logf

instance (MonadConc m, Ord event) => MonadThrow (ConcurrentMonitoringT event m) where
  throwM = lift . throwM

instance (MonadConc m, Ord event) => MonadCatch (ConcurrentMonitoringT event m) where
  catch (ConcurrentMonitoringT ma) h = ConcurrentMonitoringT $
    \vars logf -> ma vars logf `catch`
      \e -> unConcurrentMonitoringT (h e) vars logf

instance (MonadConc m, Ord event) => MonadMask (ConcurrentMonitoringT event m) where
  mask a = ConcurrentMonitoringT $ \vars logf ->
    mask $ \u -> unConcurrentMonitoringT (a $ q u) vars logf
    where q u (ConcurrentMonitoringT b) = ConcurrentMonitoringT (\vars logf -> u $ b vars logf)

  uninterruptibleMask a = ConcurrentMonitoringT $ \vars logf ->
    uninterruptibleMask $ \u -> unConcurrentMonitoringT (a $ q u) vars logf
    where q u (ConcurrentMonitoringT b) = ConcurrentMonitoringT (\vars logf -> u $ b vars logf)

instance (MonadConc m, Ord event) => MonadConc (ConcurrentMonitoringT event m) where
  type STMLike  (ConcurrentMonitoringT event m) = STMLike m
  type CVar     (ConcurrentMonitoringT event m) = CVar m
  type CRef     (ConcurrentMonitoringT event m) = CRef m
  type Ticket   (ConcurrentMonitoringT event m) = Ticket m
  type ThreadId (ConcurrentMonitoringT event m) = ThreadId m

  fork   = concurrentt fork
  forkOn = concurrentt . forkOn

  forkWithUnmask        = concurrentt' forkWithUnmask
  forkWithUnmaskN   n   = concurrentt' (forkWithUnmaskN   n  )
  forkOnWithUnmask    i = concurrentt' (forkOnWithUnmask    i)
  forkOnWithUnmaskN n i = concurrentt' (forkOnWithUnmaskN n i)

  getNumCapabilities = lift getNumCapabilities
  setNumCapabilities = lift . setNumCapabilities
  myThreadId         = lift myThreadId
  yield              = lift yield
  throwTo t          = lift . throwTo t
  newEmptyCVar       = lift newEmptyCVar
  newEmptyCVarN      = lift . newEmptyCVarN
  readCVar           = lift . readCVar
  putCVar v          = lift . putCVar v
  tryPutCVar v       = lift . tryPutCVar v
  takeCVar           = lift . takeCVar
  tryTakeCVar        = lift . tryTakeCVar
  newCRef            = lift . newCRef
  newCRefN n         = lift . newCRefN n
  readCRef           = lift . readCRef
  modifyCRef r       = lift . modifyCRef r
  writeCRef r        = lift . writeCRef r
  atomicWriteCRef r  = lift . atomicWriteCRef r
  readForCAS         = lift . readForCAS
  peekTicket         = lift . peekTicket
  casCRef r t        = lift . casCRef r t
  modifyCRefCAS r    = lift . modifyCRefCAS r
  atomically         = lift . atomically

  _concKnowsAbout = lift . _concKnowsAbout
  _concForgets    = lift . _concForgets
  _concAllKnown   = lift _concAllKnown
  _concMessage    = lift . _concMessage

concurrentt :: MonadConc m
  => (m a -> m b)
  -> ConcurrentMonitoringT e m a
  -> ConcurrentMonitoringT e m b
concurrentt f ma = ConcurrentMonitoringT $ \vars logf ->
  f (unConcurrentMonitoringT ma vars logf)

concurrentt' :: MonadConc m
  => (((forall x. m x -> m x) -> m a) -> m b)
  -> ((forall x. ConcurrentMonitoringT e m x -> ConcurrentMonitoringT e m x)
    -> ConcurrentMonitoringT e m a)
  -> ConcurrentMonitoringT e m b
concurrentt' f ma = ConcurrentMonitoringT $ \vars logf ->
  f (\g -> unConcurrentMonitoringT (ma $ concurrentt g) vars logf)

instance (MonadConc m, Ord event) => MonadMonitor event (ConcurrentMonitoringT event m) where
  startEvents events = ConcurrentMonitoringT $ \(evar, pvar) logf ->
    join . atomically $ do
      modifyCTVar' evar (\es -> S.union es (S.fromList events))
      stmCheckAll evar pvar logf

  stopEvents events = ConcurrentMonitoringT $ \(evar, pvar) logf ->
    join . atomically $ do
      modifyCTVar' evar (\es -> S.difference es (S.fromList events))
      stmCheckAll evar pvar logf

  addPropertyWithSeverity severity name checker = ConcurrentMonitoringT $ \(evar, pvar) logf ->
    join . atomically $ do
      modifyCTVar' pvar ((name, severity, checker) :)
      stmCheckAll evar pvar logf

-- | Specialisation of 'checkAll' for STM.
stmCheckAll :: (MonadSTM m, Monad n, Eq event)
  => CTVar m (Set event)
  -> CTVar m [(String, Severity, Property event)]
  -> (Severity -> String -> n ())
  -> m (n ())
stmCheckAll evar pvar logf = do
  -- Construct a new logging function which writes property violations
  -- to a CTVar, then return the combination of all violations at
  -- once, which is then executed by the join.
  logvar <- newCTVar (pure ())
  let stmlogf sev msg = modifyCTVar' logvar (>> logf sev msg)
  checkAll (readCTVar evar) (readCTVar pvar) (writeCTVar pvar) stmlogf
  readCTVar logvar

-------------------------------------------------------------------------------

-- | Monad transformer that disabled monitoring functionality.
newtype NoMonitoringT m a = NoMonitoringT { runNoMonitoringT :: m a }

instance MonadTrans NoMonitoringT where
  lift = NoMonitoringT

instance Functor f => Functor (NoMonitoringT f) where
  fmap f (NoMonitoringT ma) = NoMonitoringT (fmap f ma)

instance Applicative f => Applicative (NoMonitoringT f) where
  pure = NoMonitoringT . pure

  NoMonitoringT mf <*> NoMonitoringT ma = NoMonitoringT $ mf <*> ma

instance Monad m => Monad (NoMonitoringT m) where
  return = pure

  NoMonitoringT ma >>= f = NoMonitoringT (ma >>= runNoMonitoringT . f)

instance MonadThrow m => MonadThrow (NoMonitoringT m) where
  throwM = lift . throwM

instance MonadCatch m => MonadCatch (NoMonitoringT m) where
  catch (NoMonitoringT ma) h = NoMonitoringT $ ma `catch` (runNoMonitoringT . h)

instance MonadMask m => MonadMask (NoMonitoringT m) where
  mask a = NoMonitoringT $ mask $ \u -> runNoMonitoringT (a $ q u)
    where q u = NoMonitoringT . u . runNoMonitoringT

  uninterruptibleMask a = NoMonitoringT $ uninterruptibleMask $
    \u -> runNoMonitoringT (a $ q u)
    where q u = NoMonitoringT . u . runNoMonitoringT

instance Monad f => MonadMonitor Void (NoMonitoringT f) where
  startEvents _ = pure ()
  stopEvents  _ = pure ()
  addPropertyWithSeverity _ _ _ = pure ()

-------------------------------------------------------------------------------

-- | Check the properties
checkAll :: (Monad m, Eq event)
  => m (Set event)
  -> m [(String, Severity, Property event)]
  -> ([(String, Severity, Property event)] -> m ())
  -> (Severity -> String -> m ())
  -> m ()
checkAll getEvents getProps setProps logf = do
  es <- getEvents
  ps <- getProps
  ps' <- mapM (check es) ps
  setProps (catMaybes ps')

  where
    check events (name, severity, prop) = case evaluateProp prop events of
      Right True  -> pure Nothing
      Right False -> logf severity name >> pure Nothing
      Left  prop' -> pure (Just (name, severity, prop'))
