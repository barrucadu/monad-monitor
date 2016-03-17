{-# LANGUAGE TypeFamilies #-}

-- | This module captures in a typeclass the interface of monads which
-- allow monitoring some sort of properties.
module Control.Monad.Monitor.Class where

import Control.DeepSeq (NFData(..))

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
-- functions may be implemented differently for efficiency, or not
-- properties are not checked until the entire list has been
-- processed.

class Monad m => MonadMonitor m where
  {-# MINIMAL
        (startEvent  | startEvents)
      , (stopEvent   | stopEvents)
      , (addProperty | addPropertyWithSeverity)
    #-}

  -- | The type of events. An event is some situation which is
  -- currently happening.
  type Event m :: *

  -- | Signal than an event has begun.
  --
  -- > startEvent event = startEvents [event]
  startEvent :: Event m -> m ()
  startEvent event = startEvents [event]

  -- | Signal that a collection of events have begun. This may be atomic.
  --
  -- > startEvents = mapM_ startEvent
  startEvents :: [Event m] -> m ()
  startEvents = mapM_ startEvent

  -- | Signal that an event has stopped.
  --
  -- > stopEvent event = stopEvents [event]
  stopEvent :: Event m -> m ()
  stopEvent event = stopEvents [event]

  -- | Signal that a collection of events have stopped. This may be
  -- atomic.
  --
  -- > stopEvents = mapM_ stopEvent
  stopEvents :: [Event m] -> m ()
  stopEvents = mapM_ stopEvent

  -- | Add a new property to the collection being monitored.
  --
  -- > addProperty = addPropertyWithSeverity Warn
  addProperty :: String -> Property (Event m) -> m ()
  addProperty = addPropertyWithSeverity Warn

  -- | Add a new property to the collection being monitored, with a
  -- given severity which may influence the behaviour of the monitor
  -- on violation.
  --
  -- > addPropertyWithSeverity _ = addProperty
  addPropertyWithSeverity :: Severity -> String -> Property (Event m) -> m ()
  addPropertyWithSeverity _ = addProperty

-------------------------------------------------------------------------------

-- | A property is a function which takes all the currently active
-- events and decides whether the property has been proven
-- conclusively, is temporarily true or false, or there is not enough
-- information.
type Property event = [event] -> PropResult event

-- | The result of checking a property.
--
-- There are two types of results: proven results, and current
-- results. If a property evaluates to a proven result, this will
-- never change, and so it can be removed from the set that is
-- checked.
--
-- A current result contains a property to replace the current
-- one. This allows properties to evolve with the system being
-- monitored.
data PropResult event
  = ProvenTrue
  | ProvenFalse
  | CurrentlyTrue  (Property event)
  | CurrentlyFalse (Property event)
  | Neither (Property event)

-------------------------------------------------------------------------------

-- | Severities for property violations. No specific meaning is
-- attached to these here, beyond the obvious intuitive ordering of
-- \"badness\".
data Severity = Info | Warn | Error
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

instance NFData Severity where
  rnf s = s `seq` ()

-------------------------------------------------------------------------------

instance MonadMonitor m => MonadMonitor (MaybeT m) where
  type Event (MaybeT m) = Event m

  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

instance MonadMonitor m => MonadMonitor (ListT m) where
  type Event (ListT m) = Event m

  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

instance MonadMonitor m => MonadMonitor (ReaderT r m) where
  type Event (ReaderT r m) = Event   m

  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

instance (MonadMonitor m, Monoid w) => MonadMonitor (WL.WriterT w m) where
  type Event (WL.WriterT w m) = Event m

  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

instance (MonadMonitor m, Monoid w) => MonadMonitor (WS.WriterT w m) where
  type Event (WS.WriterT w m) = Event m

  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

instance MonadMonitor m => MonadMonitor (SL.StateT s m) where
  type Event (SL.StateT s m) = Event m

  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

instance MonadMonitor m => MonadMonitor (SS.StateT s m) where
  type Event (SS.StateT s m) = Event m

  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

instance (MonadMonitor m, Monoid w) => MonadMonitor (RL.RWST r w s m) where
  type Event (RL.RWST r w s m) = Event m

  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg

instance (MonadMonitor m, Monoid w) => MonadMonitor (RS.RWST r w s m) where
  type Event (RS.RWST r w s m) = Event m

  startEvent = lift . startEvent
  stopEvent  = lift . stopEvent

  startEvents = lift . startEvents
  stopEvents  = lift . stopEvents

  addProperty msg = lift . addProperty msg
  addPropertyWithSeverity sev msg = lift . addPropertyWithSeverity sev msg
