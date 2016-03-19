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
  , Template
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

  -- * Utilities
  , MonitoringState(..)
  , initialMonitoringState
  , instantiateTemplates
  , instantiateTemplate
  , addstantiateTemplate
  , checkProperties
  ) where

import Control.Concurrent.STM.CTVar (readCTVar, modifyCTVar, writeCTVar)
import Control.Monad (join)
import Control.Monad.Catch (MonadThrow(..), MonadCatch(..), MonadMask(..))
import Control.Monad.Conc.Class (MonadConc(..))
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State.Strict (StateT, evalStateT, get, modify, put)
import Control.Monad.STM.Class (MonadSTM(..))
import Control.Monad.Trans (MonadTrans(..))
import Data.Either (lefts, rights)
import Data.Foldable (sequenceA_)
import Data.List (foldl')
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
newtype MonitoringT event m a = MonitoringT
  { unMonitoringT
    :: (Severity -> String -> MonitoringT event m ())
    -> StateT (MonitoringState event) m a
  }

-- | Run a 'MonitoringT' action with the supplied logging function.
runMonitoringT :: (Monad m, Ord event)
  => (Severity -> String -> MonitoringT event m ())
  -> MonitoringT event m a
  -> m a
runMonitoringT logf (MonitoringT ma) =
  evalStateT (ma logf) initialMonitoringState

-- | Run a 'MonitoringT' action which prints messages to stdout.
runStdoutMonitoringT :: (MonadIO m, Ord event) => MonitoringT event m a -> m a
runStdoutMonitoringT = runHandleMonitoringT stdout

-- | Run a 'MonitoringT' action which prints messages to stderr.
runStderrMonitoringT :: (MonadIO m, Ord event) => MonitoringT event m a -> m a
runStderrMonitoringT = runHandleMonitoringT stderr

-- | Run a 'MonitoringT' action which prints messages to a handle.
runHandleMonitoringT :: (MonadIO m, Ord event) => Handle -> MonitoringT event m a -> m a
runHandleMonitoringT handle = runMonitoringT $ \severity message ->
  liftIO . hPutStrLn handle $ case severity of
    Info  -> "[info] "  ++ message
    Warn  -> "[warn] "  ++ message
    Error -> "[error] " ++ message

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

instance (MonadIO m, Ord event) => MonadIO (MonitoringT event m) where
  liftIO = lift . liftIO

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
  startEvents es = join . MonitoringT $ \logf -> do
    s <- get
    let s' = s { events  = S.union (events  s) (S.fromList es)
               , allseen = S.union (allseen s) (S.fromList es)
               }
    put $ if any (`S.notMember` allseen s') es
          then instantiateTemplates s'
          else s'
    stateCheckProps logf

  stopEvents es = join . MonitoringT $ \logf -> do
    modify (\s -> s { events = S.difference (events s) (S.fromList es) })
    stateCheckProps logf

  addPropertyWithSeverity severity name checker = join . MonitoringT $
    \logf -> do
      modify (\s -> s { properties = (name, severity, checker) : properties s })
      stateCheckProps logf

  addTemplate template = MonitoringT $ \_ ->
    modify (addstantiateTemplate template)

-- | Check properties and do logging.
stateCheckProps :: (Monad m, Ord event)
  => (Severity -> String -> MonitoringT event m ())
  -> StateT (MonitoringState event) m (MonitoringT event m ())
stateCheckProps logf = do
  state <- get
  let (props, loga) = checkProperties state logf
  put (state { properties = props })
  pure loga

-------------------------------------------------------------------------------

-- | Monad transformer that adds monitoring functionality to
-- concurrency monads, based on a shared mutable set of active events.
newtype ConcurrentMonitoringT event m a = ConcurrentMonitoringT
  { unConcurrentMonitoringT
    :: CTVar (STMLike m) (MonitoringState event)
    -> (Severity -> String -> ConcurrentMonitoringT event m ())
    -> m a
  }

-- | Run a 'ConcurrentMonitoringT' action with the supplied logging
-- function.
runConcurrentMonitoringT :: (MonadConc m, Ord event)
  => (Severity -> String -> ConcurrentMonitoringT event m ())
  -> ConcurrentMonitoringT event m a
  -> m a
runConcurrentMonitoringT logf (ConcurrentMonitoringT ma) = do
  var <- atomically (newCTVar initialMonitoringState)
  ma var logf

-- | The type of detected property violations, logged in the
-- computation trace.
data PropertyViolation event = PropertyViolation !Severity event
  deriving (Eq, Ord, Read, Show)

-- | Run a 'ConcurrentMonitoringT' which uses '_concMessage' to record
-- messages as a 'PropertyViolation'.
runTracedConcurrentMonitoringT :: (MonadConc m, Typeable event, Ord event)
  => ConcurrentMonitoringT event m a
  -> m a
runTracedConcurrentMonitoringT = runConcurrentMonitoringT $ \sev msg ->
  _concMessage (PropertyViolation sev msg)

-- | Run a 'ConcurrentMonitoringT' action which prints messages to stdout.
runStdoutConcurrentMonitoringT :: (MonadConc m, MonadIO m, Ord event)
  => ConcurrentMonitoringT event m a
  -> m a
runStdoutConcurrentMonitoringT = runHandleConcurrentMonitoringT stdout

-- | Run a 'ConcurrentMonitoringT' action which prints messages to stderr.
runStderrConcurrentMonitoringT :: (MonadConc m, MonadIO m, Ord event)
  => ConcurrentMonitoringT event m a
  -> m a
runStderrConcurrentMonitoringT = runHandleConcurrentMonitoringT stderr

-- | Run a 'ConcurrentMonitoringT' action which prints messages to a handle.
runHandleConcurrentMonitoringT :: (MonadConc m, MonadIO m, Ord event)
  => Handle
  -> ConcurrentMonitoringT event m a
  -> m a
runHandleConcurrentMonitoringT handle = runConcurrentMonitoringT $ \sev msg ->
  liftIO . hPutStrLn handle $ case sev of
    Info  -> "[info] "  ++ msg
    Warn  -> "[warn] "  ++ msg
    Error -> "[error] " ++ msg

instance Ord event => MonadTrans (ConcurrentMonitoringT event) where
  lift ma = ConcurrentMonitoringT $ \_ _ -> ma

instance (MonadConc m, Ord event) => Functor (ConcurrentMonitoringT event m) where
  fmap f (ConcurrentMonitoringT ma) = ConcurrentMonitoringT $
    \var logf -> fmap f (ma var logf)

instance (MonadConc m, Ord event) => Applicative (ConcurrentMonitoringT event m) where
  pure a = ConcurrentMonitoringT $ \_ _ -> pure a

  ConcurrentMonitoringT mf <*> ConcurrentMonitoringT ma = ConcurrentMonitoringT $
    \var logf -> mf var logf <*> ma var logf

instance (MonadConc m, Ord event) => Monad (ConcurrentMonitoringT event m) where
  return = pure

  ConcurrentMonitoringT ma >>= f = ConcurrentMonitoringT $ \var logf -> do
    a <- ma var logf
    let ConcurrentMonitoringT f' = f a
    f' var logf

instance (MonadIO m, MonadConc m, Ord event) => MonadIO (ConcurrentMonitoringT event m) where
  liftIO = lift . liftIO

instance (MonadConc m, Ord event) => MonadThrow (ConcurrentMonitoringT event m) where
  throwM = lift . throwM

instance (MonadConc m, Ord event) => MonadCatch (ConcurrentMonitoringT event m) where
  catch (ConcurrentMonitoringT ma) h = ConcurrentMonitoringT $
    \var logf -> ma var logf `catch`
      \e -> unConcurrentMonitoringT (h e) var logf

instance (MonadConc m, Ord event) => MonadMask (ConcurrentMonitoringT event m) where
  mask a = ConcurrentMonitoringT $ \var logf ->
    mask $ \u -> unConcurrentMonitoringT (a $ q u) var logf
    where q u (ConcurrentMonitoringT b) = ConcurrentMonitoringT (\var logf -> u $ b var logf)

  uninterruptibleMask a = ConcurrentMonitoringT $ \var logf ->
    uninterruptibleMask $ \u -> unConcurrentMonitoringT (a $ q u) var logf
    where q u (ConcurrentMonitoringT b) = ConcurrentMonitoringT (\var logf -> u $ b var logf)

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
concurrentt f ma = ConcurrentMonitoringT $ \var logf ->
  f (unConcurrentMonitoringT ma var logf)

concurrentt' :: MonadConc m
  => (((forall x. m x -> m x) -> m a) -> m b)
  -> ((forall x. ConcurrentMonitoringT e m x -> ConcurrentMonitoringT e m x)
    -> ConcurrentMonitoringT e m a)
  -> ConcurrentMonitoringT e m b
concurrentt' f ma = ConcurrentMonitoringT $ \var logf ->
  f (\g -> unConcurrentMonitoringT (ma $ concurrentt g) var logf)

instance (MonadConc m, Ord event) => MonadMonitor event (ConcurrentMonitoringT event m) where
  startEvents es = join . ConcurrentMonitoringT $
    \var logf -> atomically $ do
      s <- readCTVar var
      let s' = s { events  = S.union (events  s) (S.fromList es)
                 , allseen = S.union (allseen s) (S.fromList es)
                 }
      writeCTVar var $ if any (`S.notMember` allseen s') es
                       then instantiateTemplates s'
                       else s'
      stmCheckProps var logf

  stopEvents es = join . ConcurrentMonitoringT $
    \var logf -> atomically $ do
      modifyCTVar var (\s -> s { events = S.difference (events s) (S.fromList es) })
      stmCheckProps var logf

  addPropertyWithSeverity severity name checker = join . ConcurrentMonitoringT $
    \var logf -> atomically $ do
      modifyCTVar var (\s -> s { properties = (name, severity, checker) : properties s })
      stmCheckProps var logf

  addTemplate template = ConcurrentMonitoringT $ \var _ -> atomically $
    modifyCTVar var (addstantiateTemplate template)

-- | Check properties and do logging.
stmCheckProps :: (MonadConc m, Ord event)
  => CTVar (STMLike m) (MonitoringState event)
  -> (Severity -> String -> ConcurrentMonitoringT event m ())
  -> STMLike m (ConcurrentMonitoringT event m ())
stmCheckProps var logf = do
  state <- readCTVar var
  let (props, loga) = checkProperties state logf
  writeCTVar var (state { properties = props })
  pure loga

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

instance MonadIO m => MonadIO (NoMonitoringT m) where
  liftIO = lift . liftIO

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

-- | State for the 'MonitoringT' and 'ConcurrentMonitoringT'
-- transformers.
data MonitoringState event = MonitoringState
  { events :: Set event
  -- ^ The active events.
  , allseen :: Set event
  -- ^ All events that have been seen.
  , properties :: [(String, Severity, Property event)]
  -- ^ The properties.
  , templates :: [Template event]
  -- ^ The templates.
  , genprops :: Set (Property event)
  -- ^ All properties that have been generated from a template.
  }

-- | Initial state for a monitor.
initialMonitoringState :: MonitoringState event
initialMonitoringState = MonitoringState
  { events = S.empty
  , allseen = S.empty
  , properties = []
  , templates = []
  , genprops = S.empty
  }

-- | Instantiate all the templates, and register the new properties.
instantiateTemplates :: Ord event
  => MonitoringState event
  -> MonitoringState event
instantiateTemplates = foldl' instantiateTemplate <*> templates

-- | Instantiate a single template, and register the new properties.
instantiateTemplate :: Ord event
  => MonitoringState event
  -> Template event
  -> MonitoringState event
instantiateTemplate state template
  | S.null newprops = state
  | otherwise = state
    { genprops   = genprops state `S.union` S.map thd newprops
    , properties = properties state ++ S.toList newprops
    }

  where
    newprops = S.filter ((`S.notMember` genprops state) . thd) allprops
    allprops = template (allseen state)

    thd (_, _, p) = p

-- | Add a template to the state and instantiate it.
addstantiateTemplate :: Ord event
  => Template event
  -> MonitoringState event
  -> MonitoringState event
addstantiateTemplate template state = instantiateTemplate state' template where
  state' = state { templates = template : templates state }

-- | Check the properties, returning a new collection of properties
-- and an action to log the failures.
checkProperties :: (Applicative f, Eq event)
  => MonitoringState event
  -> (Severity -> String -> f ())
  -> ([(String, Severity, Property event)], f ())
checkProperties state logf = (newProps, logAct) where
  newProps = lefts checked
  logAct   = (sequenceA_ . catMaybes . rights) checked

  -- Check all properties against the events
  checked = map (check (events state)) (properties state)

  -- Check a single property against the events
  --
  -- For now, just drop properties which evaluate to a \"possibly\"
  -- result.
  check es (name, severity, prop) = case evaluate prop es of
    Right (Certainly True)  -> Right Nothing
    Right (Certainly False) -> Right (Just (logf severity name))
    Right (Possibly _) -> Right Nothing
    Left  prop' -> Left (name, severity, prop')
