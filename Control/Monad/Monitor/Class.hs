{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- All the mtl instances need some hairy extensions. Lovely.
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module captures in a typeclass the interface of monads which
-- allow monitoring some sort of properties.
module Control.Monad.Monitor.Class
  ( MonadMonitor(..)
  -- * Properties

  -- | See Control.Monad.Monitor.Property for fuller documentation.

  , Property
  , StateProp(..)
  , PathProp(..)
  , Severity(..)

  -- * Templates
  , Template
  , subsetTemplate
  , powersetTemplate
  ) where

import Control.DeepSeq (NFData(..))
import Control.Monad (filterM)
import Data.Set (Set)
import qualified Data.Set as S

-- for the transformer instances
import Control.Monad.Trans (lift)
import Control.Monad.Trans.List (ListT)
import Control.Monad.Trans.Identity (IdentityT)
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Reader (ReaderT)
import qualified Control.Monad.RWS.Lazy as RL (RWST)
import qualified Control.Monad.RWS.Strict as RS (RWST)
import qualified Control.Monad.State.Lazy as SL (StateT)
import qualified Control.Monad.State.Strict as SS (StateT)
import qualified Control.Monad.Writer.Lazy as WL (WriterT)
import qualified Control.Monad.Writer.Strict as WS (WriterT)

-- local imports
import Control.Monad.Monitor.Property

-------------------------------------------------------------------------------

-- | A @Monad@ which has the ability to monitor properties and signal
-- violations in some manner. For example: printing a message, or
-- performing some recovery behaviour.
--
-- Whilst there is no specification for how the events and properties
-- are implemented, if we posit the existence of some
-- \"@isEventActive@\" function, we require the following behaviours:
--
-- > startEvent foo >> isEventActive foo = startEvent foo >> pure True
-- > stopEvent  foo >> isEventActive foo = stopEvent  foo >> pure False
-- > startEvents foos = mapM_ startEvent foos
-- > stopEvents foos = mapM_ stopEvent foos
--
-- With the exception that the actual @startEvents@ and @stopEvents@
-- functions may be implemented differently for efficiency, or
-- properties are not checked until the entire list has been
-- processed.
class (Monad m, Ord event) => MonadMonitor event m | m -> event where
  {-# MINIMAL
        (startEvent  | startEvents)
      , (stopEvent   | stopEvents)
      , (addProperty | addPropertyWithSeverity)
      , addTemplate
    #-}

  -- | Signal than an event has begun.
  --
  -- > startEvent event = startEvents [event]
  startEvent :: event -> m ()
  startEvent event = startEvents [event]

  -- | Signal that a collection of events have begun. This may be atomic.
  --
  -- > startEvents = mapM_ startEvent
  startEvents :: [event] -> m ()
  startEvents = mapM_ startEvent

  -- | Signal that an event has stopped.
  --
  -- > stopEvent event = stopEvents [event]
  stopEvent :: event -> m ()
  stopEvent event = stopEvents [event]

  -- | Signal that a collection of events have stopped. This may be
  -- atomic.
  --
  -- > stopEvents = mapM_ stopEvent
  stopEvents :: [event] -> m ()
  stopEvents = mapM_ stopEvent

  -- | Add a new property to the collection being monitored. Properties
  -- are checked after event(s) are started or stopped.
  --
  -- > addProperty = addPropertyWithSeverity Warn
  addProperty :: String -> Property event -> m ()
  addProperty = addPropertyWithSeverity Warn

  -- | Add a new property to the collection being monitored, with a
  -- given severity which may influence the behaviour of the monitor
  -- on violation. Properties are checked after event(s) are started
  -- or stopped.
  --
  -- > addPropertyWithSeverity _ = addProperty
  addPropertyWithSeverity :: Severity -> String -> Property event -> m ()
  addPropertyWithSeverity _ = addProperty

  -- | Add a new property template. Property templates are called with
  -- the set of currently-known events when first installed, and when
  -- a new event is started for the first time, and may generate new
  -- properties based on this information.
  --
  -- Properties which have been generated are recorded, and not added
  -- to the pool if generated again.
  addTemplate :: Template event -> m ()

-------------------------------------------------------------------------------

-- | Severities for property violations. No specific meaning is
-- attached to these here, beyond the obvious intuitive ordering of
-- \"badness\".
data Severity = Info | Warn | Error
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

instance NFData Severity where
  rnf s = s `seq` ()

-------------------------------------------------------------------------------

-- | Templates for generating more properties. A template is called
-- with the set of currently known events (1) after it is initially
-- installed, and (2) after a new event is seen for the first time.
type Template event = Set event -> Set (String, Severity, Property event)

-- | Lift a template over a small set to a template over a larger set,
-- by filtering the types of events we care about, and checking all
-- subsets.
subsetTemplate :: Ord event
  => (event -> Bool)
  -> Template event
  -> Template event
subsetTemplate eventp template = powersetTemplate template . S.filter eventp

-- | Apply a template to all subsets of a set.
powersetTemplate :: Ord event => Template event -> Template event
powersetTemplate template = instantiate . powerset where
  powerset = map S.fromAscList . filterM (const [False,True]) . S.toList
  instantiate = S.unions . map template

-------------------------------------------------------------------------------

instance MonadMonitor event m => MonadMonitor event (IdentityT m) where
  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

  addTemplate = lift . addTemplate

instance MonadMonitor event m => MonadMonitor event (MaybeT m) where
  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

  addTemplate = lift . addTemplate

instance MonadMonitor event m => MonadMonitor event (ListT m) where
  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

  addTemplate = lift . addTemplate

instance MonadMonitor event m => MonadMonitor event (ReaderT r m) where
  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

  addTemplate = lift . addTemplate

instance (MonadMonitor event m, Monoid w) => MonadMonitor event (WL.WriterT w m) where
  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

  addTemplate = lift . addTemplate

instance (MonadMonitor event m, Monoid w) => MonadMonitor event (WS.WriterT w m) where
  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

  addTemplate = lift . addTemplate

instance MonadMonitor event m => MonadMonitor event (SL.StateT s m) where
  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

  addTemplate = lift . addTemplate

instance MonadMonitor event m => MonadMonitor event (SS.StateT s m) where
  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

  addTemplate = lift . addTemplate

instance (MonadMonitor event m, Monoid w) => MonadMonitor event (RL.RWST r w s m) where
  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

  addTemplate = lift . addTemplate

instance (MonadMonitor event m, Monoid w) => MonadMonitor event (RS.RWST r w s m) where
  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

  addTemplate = lift . addTemplate
