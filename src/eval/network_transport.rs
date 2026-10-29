//! Private copied transport. It does not establish worker or processing completion.
use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, MutexGuard};
use triomphe::Arc;

// A finite limit makes each readiness update bounded. Refusal publishes no watch.
pub(super) const MAX_WATCHES: usize = 64;
static NEXT_ACTIVATION: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Side {
    A,
    B,
}
impl Side {
    fn index(self) -> usize {
        match self {
            Self::A => 0,
            Self::B => 1,
        }
    }
    fn opposite(self) -> Self {
        match self {
            Self::A => Self::B,
            Self::B => Self::A,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum EnvelopeKind {
    Application,
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the checked protocol driver supplies control envelopes in a later milestone"
        )
    )]
    Control,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Failure {
    Refused,
    WorkerFailed,
    IncompleteTeardown,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Send {
    Sent,
    Full,
    Closed,
    Failed(Failure),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Interest {
    Readable,
    Writable,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Registration {
    activation: u64,
    side: Side,
    generation: u64,
}
struct Envelope {
    kind: EnvelopeKind,
    bytes: Vec<u8>,
}
#[cfg(test)]
struct DropProbe(std::sync::Arc<std::sync::atomic::AtomicUsize>);
#[cfg(test)]
impl Drop for DropProbe {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}
struct Direction {
    queue: VecDeque<Envelope>,
    #[cfg(test)]
    drop_probe: Option<DropProbe>,
    sealed: bool,
    reserved: bool,
    sending: bool,
}
struct Watch {
    registration: Registration,
    interest: Interest,
    pending: bool,
    published: bool,
}
struct State {
    directions: [Direction; 2],
    watches: Vec<Watch>,
    receive_finished: [bool; 2],
    next_generation: u64,
    failed: bool,
    settled: bool,
    cursor: usize,
}
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct TransportUsers {
    pub(super) sends: usize,
    pub(super) receives: usize,
    pub(super) queued: usize,
    pub(super) registrations: usize,
    pub(super) pending_wakes: usize,
}
struct Shared {
    activation: u64,
    capacity: usize,
    state: Mutex<State>,
}
#[derive(Clone)]
pub(super) struct NetworkTransport {
    shared: Arc<Shared>,
}
pub(super) enum Receive {
    Message(ReceiveGuard),
    Empty,
    End,
    Busy,
    Failed(Failure),
}
struct SendGuard {
    transport: NetworkTransport,
    side: Side,
}
pub(super) struct ReceiveGuard {
    transport: NetworkTransport,
    sender: Side,
    kind: EnvelopeKind,
    bytes: Option<Vec<u8>>,
    original: Option<Envelope>,
    active: bool,
}
impl NetworkTransport {
    pub(super) fn same_activation(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.shared, &other.shared)
    }

    pub(super) fn prepare(capacity: usize) -> Result<Self, Failure> {
        Self::prepare_with(capacity, |shared| {
            Arc::try_new(shared).map_err(|_| Failure::Refused)
        })
    }
    fn prepare_with(
        capacity: usize,
        allocate: impl FnOnce(Shared) -> Result<Arc<Shared>, Failure>,
    ) -> Result<Self, Failure> {
        if capacity == 0 {
            return Err(Failure::Refused);
        }
        let mut a = VecDeque::new();
        let mut b = VecDeque::new();
        a.try_reserve_exact(capacity)
            .map_err(|_| Failure::Refused)?;
        b.try_reserve_exact(capacity)
            .map_err(|_| Failure::Refused)?;
        let activation = NEXT_ACTIVATION
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |x| x.checked_add(1))
            .map_err(|_| Failure::Refused)?;
        Ok(Self {
            shared: allocate(Shared {
                activation,
                capacity,
                state: Mutex::new(State {
                    directions: [
                        Direction {
                            #[cfg(test)]
                            drop_probe: None,
                            queue: a,
                            sealed: false,
                            reserved: false,
                            sending: false,
                        },
                        Direction {
                            #[cfg(test)]
                            drop_probe: None,
                            queue: b,
                            sealed: false,
                            reserved: false,
                            sending: false,
                        },
                    ],
                    watches: Vec::new(),
                    receive_finished: [false; 2],
                    next_generation: 0,
                    failed: false,
                    settled: false,
                    cursor: 0,
                }),
            })?,
        })
    }
    fn lock(&self) -> Result<MutexGuard<'_, State>, Failure> {
        self.shared
            .state
            .lock()
            .map_err(|_| Failure::IncompleteTeardown)
    }
    fn send_status(&self, state: &State, side: Side) -> Option<Send> {
        if state.settled {
            return Some(Send::Failed(Failure::IncompleteTeardown));
        }
        if state.failed {
            return Some(Send::Failed(Failure::WorkerFailed));
        }
        let direction = &state.directions[side.index()];
        if direction.sealed {
            Some(Send::Closed)
        } else if direction.queue.len() + usize::from(direction.reserved) >= self.shared.capacity {
            Some(Send::Full)
        } else {
            None
        }
    }
    fn reserve_send(&self, side: Side) -> Result<SendGuard, Send> {
        let mut state = self.lock().map_err(Send::Failed)?;
        if let Some(result) = self.send_status(&state, side) {
            return Err(result);
        }
        if state.directions[side.index()].sending {
            return Err(Send::Failed(Failure::Refused));
        }
        state.directions[side.index()].sending = true;
        Ok(SendGuard {
            transport: self.clone(),
            side,
        })
    }
    pub(super) fn try_send(&self, side: Side, kind: EnvelopeKind, bytes: &[u8]) -> Send {
        let _reservation = match self.reserve_send(side) {
            Ok(guard) => guard,
            Err(result) => return result,
        };
        let mut copy = Vec::new();
        if copy.try_reserve_exact(bytes.len()).is_err() {
            return Send::Failed(Failure::Refused);
        }
        copy.extend_from_slice(bytes);
        let mut state = match self.lock() {
            Ok(s) => s,
            Err(e) => return Send::Failed(e),
        };
        if let Some(result) = self.send_status(&state, side) {
            return result;
        }
        state.directions[side.index()]
            .queue
            .push_back(Envelope { kind, bytes: copy });
        self.refresh(&mut state);
        Send::Sent
    }
    pub(super) fn reserve_receive(&self, side: Side) -> Receive {
        let mut state = match self.lock() {
            Ok(s) => s,
            Err(e) => return Receive::Failed(e),
        };
        if state.settled {
            return Receive::Failed(Failure::IncompleteTeardown);
        }
        if state.failed {
            return Receive::Failed(Failure::WorkerFailed);
        }
        if state.receive_finished[side.index()] {
            return Receive::Failed(Failure::Refused);
        }
        let sender = side.opposite();
        let direction = &mut state.directions[sender.index()];
        if direction.reserved {
            return Receive::Busy;
        }
        let Some(head) = direction.queue.pop_front() else {
            return if direction.sealed {
                Receive::End
            } else {
                Receive::Empty
            };
        };
        direction.reserved = true;
        Receive::Message(ReceiveGuard {
            transport: self.clone(),
            sender,
            kind: head.kind,
            bytes: None,
            original: Some(head),
            active: true,
        })
    }

    pub(super) fn finish_send(&self, side: Side) -> Result<(), Failure> {
        let mut state = self.lock()?;
        if state.settled {
            return Err(Failure::IncompleteTeardown);
        }
        if state.failed {
            return Err(Failure::WorkerFailed);
        }
        if state.directions[side.index()].sending {
            return Err(Failure::Refused);
        }
        state.directions[side.index()].sealed = true;
        self.refresh(&mut state);
        Ok(())
    }
    // The caller must first authenticate genuine End and local completion.
    // This lock serializes that checked worker's terminal receive transition
    // against the peer's queue and send operations.
    pub(super) fn finish_receive(&self, side: Side) -> Result<(), Failure> {
        let mut state = self.lock()?;
        if state.settled {
            return Err(Failure::IncompleteTeardown);
        }
        if state.failed {
            return Err(Failure::WorkerFailed);
        }
        let incoming = &state.directions[side.opposite().index()];
        if state.receive_finished[side.index()]
            || !incoming.sealed
            || incoming.reserved
            || incoming.sending
            || !incoming.queue.is_empty()
        {
            return Err(Failure::Refused);
        }
        state.receive_finished[side.index()] = true;
        Ok(())
    }

    // This remains a transport predicate, not worker teardown authority.
    pub(super) fn ready_for_settlement(&self) -> Result<(), Failure> {
        let state = self.lock()?;
        if state.settled
            || state.failed
            || !state.receive_finished.iter().all(|finished| *finished)
            || !state.watches.is_empty()
            || state.directions.iter().any(|direction| {
                !direction.sealed
                    || direction.reserved
                    || direction.sending
                    || !direction.queue.is_empty()
            })
        {
            return Err(Failure::IncompleteTeardown);
        }
        Ok(())
    }

    fn ready(&self, state: &State, side: Side, interest: Interest) -> bool {
        if state.failed {
            return true;
        }
        match interest {
            Interest::Readable => {
                let d = &state.directions[side.opposite().index()];
                !d.queue.is_empty() || d.reserved || d.sealed
            }
            Interest::Writable => {
                let d = &state.directions[side.index()];
                d.sealed || d.queue.len() + usize::from(d.reserved) < self.shared.capacity
            }
        }
    }
    fn refresh(&self, state: &mut State) {
        for index in 0..state.watches.len() {
            let watch = &state.watches[index];
            if self.ready(state, watch.registration.side, watch.interest) {
                state.watches[index].pending = true;
            }
        }
    }
    #[cfg(test)]
    pub(super) fn watch(&self, side: Side, interest: Interest) -> Result<Registration, Failure> {
        self.register_watch(side, interest, true)
    }
    pub(super) fn watch_pending(
        &self,
        side: Side,
        interest: Interest,
    ) -> Result<Registration, Failure> {
        self.register_watch(side, interest, false)
    }
    fn register_watch(
        &self,
        side: Side,
        interest: Interest,
        published: bool,
    ) -> Result<Registration, Failure> {
        let mut state = self.lock()?;
        if state.settled {
            return Err(Failure::IncompleteTeardown);
        }
        if state.watches.len() == MAX_WATCHES {
            return Err(Failure::Refused);
        }
        let next = state
            .next_generation
            .checked_add(1)
            .ok_or(Failure::Refused)?;
        state.watches.try_reserve(1).map_err(|_| Failure::Refused)?;
        let registration = Registration {
            activation: self.shared.activation,
            side,
            generation: next,
        };
        let pending = self.ready(&state, side, interest);
        state.watches.push(Watch {
            registration,
            interest,
            pending,
            published,
        });
        state.next_generation = next;
        Ok(registration)
    }
    pub(super) fn publish_watch(
        &self,
        side: Side,
        registration: Registration,
    ) -> Result<(), Failure> {
        let mut state = self.lock()?;
        if state.settled {
            return Err(Failure::IncompleteTeardown);
        }
        if state.failed {
            return Err(Failure::WorkerFailed);
        }
        if registration.activation != self.shared.activation || registration.side != side {
            return Err(Failure::Refused);
        }
        let watch = state
            .watches
            .iter_mut()
            .find(|watch| watch.registration == registration)
            .ok_or(Failure::Refused)?;
        if watch.published {
            return Err(Failure::Refused);
        }
        watch.published = true;
        Ok(())
    }
    pub(super) fn cancel_unpublished(&self, side: Side) -> Result<(), Failure> {
        let mut state = self.lock()?;
        if state.settled {
            return Err(Failure::IncompleteTeardown);
        }
        state
            .watches
            .retain(|watch| watch.registration.side != side || watch.published);
        Ok(())
    }
    pub(super) fn cancel_watch(
        &self,
        side: Side,
        registration: Registration,
    ) -> Result<(), Failure> {
        let mut state = self.lock()?;
        if state.settled {
            return Err(Failure::IncompleteTeardown);
        }
        if registration.activation != self.shared.activation || registration.side != side {
            return Err(Failure::Refused);
        }
        let Some(index) = state
            .watches
            .iter()
            .position(|w| w.registration == registration)
        else {
            return Err(Failure::Refused);
        };
        state.watches.swap_remove(index);
        Ok(())
    }
    pub(super) fn poll_wake(&self, side: Side) -> Result<Option<Registration>, Failure> {
        let mut state = self.lock()?;
        if state.settled {
            return Err(Failure::IncompleteTeardown);
        }
        self.refresh(&mut state);
        let n = state.watches.len();
        for offset in 0..n {
            let index = (state.cursor + offset) % n;
            if state.watches[index].registration.side == side
                && state.watches[index].published
                && state.watches[index].pending
            {
                state.watches[index].pending = false;
                let registration = state.watches[index].registration;
                state.cursor = (index + 1) % n;
                return Ok(Some(registration));
            }
        }
        Ok(None)
    }
    pub(super) fn fail(&self) {
        if let Ok(mut state) = self.lock() {
            if !state.settled {
                state.failed = true;
                self.refresh(&mut state);
            }
        }
    }
    /// A synchronized observation, not permission to release worker-owned state.
    #[cfg(test)]
    pub(super) fn users(&self) -> Result<TransportUsers, Failure> {
        let state = self.lock()?;
        Ok(TransportUsers {
            sends: state.directions.iter().filter(|d| d.sending).count(),
            receives: state.directions.iter().filter(|d| d.reserved).count(),
            queued: state
                .directions
                .iter()
                .map(|d| d.queue.len() + usize::from(d.reserved))
                .sum(),
            registrations: state.watches.len(),
            pending_wakes: state.watches.iter().filter(|w| w.pending).count(),
        })
    }
    // This checks transport users only, not worker or receiver processing completion.
    pub(super) fn settle(&self) -> Result<(), Failure> {
        let mut state = self.lock()?;
        if state.settled
            || state.failed
            || !state.receive_finished.iter().all(|finished| *finished)
            || !state.watches.is_empty()
            || state
                .directions
                .iter()
                .any(|d| !d.sealed || d.reserved || d.sending || !d.queue.is_empty())
        {
            return Err(Failure::IncompleteTeardown);
        }
        state.settled = true;
        Ok(())
    }
}
impl Drop for SendGuard {
    fn drop(&mut self) {
        let mut state = self
            .transport
            .shared
            .state
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        state.directions[self.side.index()].sending = false;
    }
}
impl ReceiveGuard {
    pub(super) fn sender(&self) -> Side {
        self.sender
    }
    pub(super) fn kind(&self) -> EnvelopeKind {
        self.kind
    }
    pub(super) fn byte_len(&self) -> usize {
        self.original.as_ref().map_or(0, |head| head.bytes.len())
    }
    // Caller charges byte_len before invoking this fallible host copy.
    pub(super) fn snapshot(&mut self) -> Result<&[u8], Failure> {
        if self.bytes.is_none() {
            let head = self.original.as_ref().ok_or(Failure::IncompleteTeardown)?;
            let mut bytes = Vec::new();
            bytes
                .try_reserve_exact(head.bytes.len())
                .map_err(|_| Failure::Refused)?;
            bytes.extend_from_slice(&head.bytes);
            self.bytes = Some(bytes);
        }
        self.bytes.as_deref().ok_or(Failure::IncompleteTeardown)
    }
    pub(super) fn commit(mut self) -> Result<(), Failure> {
        let mut state = self.transport.lock()?;
        if state.settled {
            return Err(Failure::IncompleteTeardown);
        }
        if state.failed {
            return Err(Failure::WorkerFailed);
        }
        let direction = &mut state.directions[self.sender.index()];
        if !direction.reserved || self.original.is_none() || self.bytes.is_none() {
            return Err(Failure::IncompleteTeardown);
        }
        self.original = None;
        direction.reserved = false;
        self.active = false;
        self.transport.refresh(&mut state);
        Ok(())
    }
}
impl Drop for ReceiveGuard {
    fn drop(&mut self) {
        if self.active {
            // A poisoned lock cannot authorize receipt; leave the original queued.
            let mut state = self
                .transport
                .shared
                .state
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            let direction = &mut state.directions[self.sender.index()];
            if let Some(head) = self.original.take() {
                direction.queue.push_front(head);
            }
            direction.reserved = false;
            self.transport.refresh(&mut state);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounded_fifo_copy_and_end() {
        let t = NetworkTransport::prepare(1).unwrap();
        let mut bytes = vec![1, 2];
        assert_eq!(
            t.try_send(Side::A, EnvelopeKind::Application, &bytes),
            Send::Sent
        );
        bytes[0] = 9;
        assert_eq!(t.try_send(Side::A, EnvelopeKind::Control, &[3]), Send::Full);
        let Receive::Message(mut g) = t.reserve_receive(Side::B) else {
            panic!("message")
        };
        assert_eq!(
            (g.sender(), g.kind(), g.snapshot().unwrap()),
            (Side::A, EnvelopeKind::Application, &[1, 2][..])
        );
        assert_eq!(t.try_send(Side::A, EnvelopeKind::Control, &[3]), Send::Full);
        drop(g); // failed receiver copy leaves the original head
        let Receive::Message(mut g) = t.reserve_receive(Side::B) else {
            panic!("retry")
        };
        assert_eq!(g.snapshot().unwrap(), &[1, 2]);
        g.snapshot().unwrap();
        g.commit().unwrap();
        assert_eq!(t.try_send(Side::A, EnvelopeKind::Control, &[3]), Send::Sent);
        t.finish_send(Side::A).unwrap();
        let Receive::Message(mut g) = t.reserve_receive(Side::B) else {
            panic!("control")
        };
        assert_eq!(g.kind(), EnvelopeKind::Control);
        g.snapshot().unwrap();
        g.commit().unwrap();
        assert!(matches!(t.reserve_receive(Side::B), Receive::End));
        assert_eq!(
            t.try_send(Side::A, EnvelopeKind::Application, &[]),
            Send::Closed
        );
    }

    #[test]
    fn watchers_recheck_level_cancel_and_terminal() {
        let t = NetworkTransport::prepare(1).unwrap();
        let read = t.watch(Side::B, Interest::Readable).unwrap();
        assert_eq!(t.poll_wake(Side::B).unwrap(), None);
        assert_eq!(
            t.try_send(Side::A, EnvelopeKind::Application, &[1]),
            Send::Sent
        );
        assert_eq!(t.poll_wake(Side::B).unwrap(), Some(read));
        assert_eq!(t.poll_wake(Side::B).unwrap(), Some(read));
        t.cancel_watch(Side::B, read).unwrap();
        assert_eq!(t.poll_wake(Side::B).unwrap(), None);
        let write = t.watch(Side::A, Interest::Writable).unwrap();
        assert_eq!(t.poll_wake(Side::A).unwrap(), None);
        let Receive::Message(mut g) = t.reserve_receive(Side::B) else {
            panic!("message")
        };
        g.snapshot().unwrap();
        g.commit().unwrap();
        assert_eq!(t.poll_wake(Side::A).unwrap(), Some(write));
        t.cancel_watch(Side::A, write).unwrap();
        t.finish_send(Side::A).unwrap();
        let end = t.watch(Side::B, Interest::Readable).unwrap();
        let closed = t.watch(Side::A, Interest::Writable).unwrap();
        assert_eq!(t.poll_wake(Side::B).unwrap(), Some(end));
        assert_eq!(t.poll_wake(Side::A).unwrap(), Some(closed));
        t.cancel_watch(Side::A, closed).unwrap();
        t.cancel_watch(Side::B, end).unwrap();
        t.fail();
        let read_failure = t.watch(Side::A, Interest::Readable).unwrap();
        let write_failure = t.watch(Side::B, Interest::Writable).unwrap();
        assert_eq!(t.poll_wake(Side::A).unwrap(), Some(read_failure));
        assert_eq!(t.poll_wake(Side::B).unwrap(), Some(write_failure));
    }

    #[test]
    fn settlement_needs_drained_channels_and_cancelled_watches() {
        assert!(NetworkTransport::prepare(0).is_err());
        assert!(NetworkTransport::prepare(usize::MAX).is_err());
        let t = NetworkTransport::prepare(1).unwrap();
        t.finish_send(Side::A).unwrap();
        t.finish_send(Side::B).unwrap();
        let watch = t.watch(Side::A, Interest::Readable).unwrap();
        assert!(t.settle().is_err());
        t.cancel_watch(Side::A, watch).unwrap();
        t.finish_receive(Side::A).unwrap();
        t.finish_receive(Side::B).unwrap();
        t.settle().unwrap();
        assert!(t.watch(Side::A, Interest::Readable).is_err());
    }
    #[test]
    fn settlement_requires_both_finished_receivers() {
        let t = NetworkTransport::prepare(1).unwrap();
        t.finish_send(Side::A).unwrap();
        t.finish_send(Side::B).unwrap();
        assert!(matches!(t.reserve_receive(Side::A), Receive::End));
        assert!(matches!(t.reserve_receive(Side::B), Receive::End));
        assert_eq!(t.settle(), Err(Failure::IncompleteTeardown));
        t.finish_receive(Side::A).unwrap();
        assert_eq!(t.settle(), Err(Failure::IncompleteTeardown));
        assert!(matches!(
            t.reserve_receive(Side::A),
            Receive::Failed(Failure::Refused)
        ));
        t.finish_receive(Side::B).unwrap();
        t.settle().unwrap();
    }

    #[test]
    fn pending_send_blocks_seal_and_settlement() {
        let t = NetworkTransport::prepare(1).unwrap();
        let guard = t.reserve_send(Side::A).unwrap();
        assert_eq!(t.finish_send(Side::A), Err(Failure::Refused));
        assert_eq!(
            t.try_send(Side::A, EnvelopeKind::Application, &[]),
            Send::Failed(Failure::Refused)
        );
        assert!(t.settle().is_err());
        drop(guard);
        t.finish_send(Side::A).unwrap();
        t.finish_send(Side::B).unwrap();
        t.finish_receive(Side::A).unwrap();
        t.finish_receive(Side::B).unwrap();
        t.settle().unwrap();
    }

    #[test]
    fn reservations_keep_fifo_and_block_settlement() {
        let t = NetworkTransport::prepare(2).unwrap();
        assert_eq!(
            t.try_send(Side::A, EnvelopeKind::Application, &[1]),
            Send::Sent
        );
        let Receive::Message(first) = t.reserve_receive(Side::B) else {
            panic!("first")
        };
        assert!(matches!(t.reserve_receive(Side::B), Receive::Busy));
        assert_eq!(t.try_send(Side::A, EnvelopeKind::Control, &[2]), Send::Sent);
        t.finish_send(Side::A).unwrap();
        t.finish_send(Side::B).unwrap();
        assert!(t.settle().is_err());
        drop(first);
        let Receive::Message(mut first) = t.reserve_receive(Side::B) else {
            panic!("restored")
        };
        assert_eq!(first.snapshot().unwrap(), &[1]);
        first.snapshot().unwrap();
        first.commit().unwrap();
        let Receive::Message(mut second) = t.reserve_receive(Side::B) else {
            panic!("second")
        };
        assert_eq!(second.snapshot().unwrap(), &[2]);
        second.snapshot().unwrap();
        second.commit().unwrap();
        t.finish_receive(Side::A).unwrap();
        t.finish_receive(Side::B).unwrap();
        t.settle().unwrap();
    }

    #[test]
    fn pending_wake_survives_readiness_reversal_and_stale_tokens_are_rejected() {
        let t = NetworkTransport::prepare(1).unwrap();
        let other = NetworkTransport::prepare(1).unwrap();
        let wake = t.watch(Side::B, Interest::Readable).unwrap();
        assert!(other.cancel_watch(Side::B, wake).is_err());
        assert!(t.cancel_watch(Side::A, wake).is_err());
        assert_eq!(
            t.try_send(Side::A, EnvelopeKind::Application, &[1]),
            Send::Sent
        );
        let Receive::Message(mut g) = t.reserve_receive(Side::B) else {
            panic!("message")
        };
        g.snapshot().unwrap();
        g.commit().unwrap();
        assert_eq!(t.poll_wake(Side::B).unwrap(), Some(wake));
        assert_eq!(t.poll_wake(Side::B).unwrap(), None);
        t.cancel_watch(Side::B, wake).unwrap();
        let next = t.watch(Side::B, Interest::Readable).unwrap();
        assert_ne!(wake, next);
        assert!(t.cancel_watch(Side::B, wake).is_err());
        t.cancel_watch(Side::B, next).unwrap();
    }

    #[test]
    fn terminal_failure_preserves_reserved_delivery() {
        let t = NetworkTransport::prepare(1).unwrap();
        assert_eq!(
            t.try_send(Side::A, EnvelopeKind::Application, &[4]),
            Send::Sent
        );
        let Receive::Message(g) = t.reserve_receive(Side::B) else {
            panic!("message")
        };
        t.fail();
        assert_eq!(g.commit(), Err(Failure::WorkerFailed));
        let state = t.lock().unwrap();
        assert_eq!(state.directions[0].queue.front().unwrap().bytes, [4]);
        assert!(!state.directions[0].reserved);
        drop(state);
        assert!(matches!(
            t.reserve_receive(Side::B),
            Receive::Failed(Failure::WorkerFailed)
        ));
        assert!(t.settle().is_err());
    }

    #[test]
    fn watch_refusal_and_generation_exhaustion_publish_nothing() {
        let t = NetworkTransport::prepare(1).unwrap();
        let mut registrations = Vec::new();
        for _ in 0..MAX_WATCHES {
            registrations.push(t.watch(Side::A, Interest::Writable).unwrap());
        }
        assert_eq!(t.watch(Side::A, Interest::Writable), Err(Failure::Refused));
        for r in registrations {
            t.cancel_watch(Side::A, r).unwrap();
        }
        t.lock().unwrap().next_generation = u64::MAX;
        assert_eq!(t.watch(Side::A, Interest::Writable), Err(Failure::Refused));
        assert_eq!(t.poll_wake(Side::A).unwrap(), None);
    }

    #[test]
    fn peer_publish_and_cancel_are_serialized() {
        let t = NetworkTransport::prepare(1).unwrap();
        let watch = t.watch(Side::B, Interest::Readable).unwrap();
        std::thread::scope(|scope| {
            scope.spawn(|| {
                assert_eq!(
                    t.try_send(Side::A, EnvelopeKind::Application, &[7]),
                    Send::Sent
                );
            });
            t.cancel_watch(Side::B, watch).unwrap();
        });
        assert_eq!(t.poll_wake(Side::B).unwrap(), None);
        let Receive::Message(mut g) = t.reserve_receive(Side::B) else {
            panic!("message")
        };
        assert_eq!(g.snapshot().unwrap(), &[7]);
        g.snapshot().unwrap();
        g.commit().unwrap();
    }
    #[test]
    fn late_watch_rechecks_both_directions_and_users() {
        let t = NetworkTransport::prepare(1).unwrap();
        assert_eq!(
            t.try_send(Side::B, EnvelopeKind::Application, &[8]),
            Send::Sent
        );
        let readable = t.watch(Side::A, Interest::Readable).unwrap();
        let writable = t.watch(Side::A, Interest::Writable).unwrap();
        assert_eq!(t.poll_wake(Side::A).unwrap(), Some(readable));
        assert_eq!(t.poll_wake(Side::A).unwrap(), Some(writable));
        let Receive::Message(g) = t.reserve_receive(Side::A) else {
            panic!("message")
        };
        let users = t.users().unwrap();
        assert_eq!(
            (users.receives, users.queued, users.registrations),
            (1, 1, 2)
        );
        drop(g);
        t.cancel_watch(Side::A, readable).unwrap();
        t.cancel_watch(Side::A, writable).unwrap();
    }
    #[test]
    fn unprepared_receipt_restores_head() {
        let t = NetworkTransport::prepare(1).unwrap();
        assert_eq!(
            t.try_send(Side::A, EnvelopeKind::Application, &[1, 2]),
            Send::Sent
        );
        let Receive::Message(g) = t.reserve_receive(Side::B) else {
            panic!("message")
        };
        assert_eq!(g.byte_len(), 2);
        assert_eq!(g.commit(), Err(Failure::IncompleteTeardown));
        let Receive::Message(mut retry) = t.reserve_receive(Side::B) else {
            panic!("retry")
        };
        assert_eq!(retry.snapshot().unwrap(), &[1, 2]);
        retry.commit().unwrap();
    }
    #[test]
    fn receive_guard_keeps_backing_after_wrapper_drop_and_commits() {
        let t = NetworkTransport::prepare(1).unwrap();
        let observer = t.clone();
        assert_eq!(
            t.try_send(Side::A, EnvelopeKind::Application, &[1, 2]),
            Send::Sent
        );
        t.finish_send(Side::A).unwrap();
        t.finish_send(Side::B).unwrap();
        let Receive::Message(mut guard) = t.reserve_receive(Side::B) else {
            panic!("message")
        };
        drop(t);
        assert_eq!(Arc::strong_count(&observer.shared), 2);
        assert_eq!(observer.users().unwrap().receives, 1);
        assert_eq!(observer.settle(), Err(Failure::IncompleteTeardown));
        assert_eq!(guard.byte_len(), 2);
        assert_eq!(guard.snapshot().unwrap(), &[1, 2]);
        guard.commit().unwrap();
        observer.finish_receive(Side::A).unwrap();
        observer.finish_receive(Side::B).unwrap();
        observer.settle().unwrap();
        assert_eq!(Arc::strong_count(&observer.shared), 1);
    }

    #[test]
    fn receive_guard_drop_after_wrapper_drop_restores_head() {
        let t = NetworkTransport::prepare(1).unwrap();
        let observer = t.clone();
        assert_eq!(t.try_send(Side::A, EnvelopeKind::Control, &[5]), Send::Sent);
        let Receive::Message(guard) = t.reserve_receive(Side::B) else {
            panic!("message")
        };
        drop(t);
        assert_eq!(Arc::strong_count(&observer.shared), 2);
        assert_eq!(observer.users().unwrap().queued, 1);
        drop(guard);
        let Receive::Message(mut retry) = observer.reserve_receive(Side::B) else {
            panic!("retry")
        };
        assert_eq!(retry.kind(), EnvelopeKind::Control);
        assert_eq!(retry.snapshot().unwrap(), &[5]);
        retry.commit().unwrap();
    }

    #[test]
    fn send_guard_keeps_backing_after_wrapper_drop() {
        let t = NetworkTransport::prepare(1).unwrap();
        let observer = t.clone();
        let guard = t.reserve_send(Side::A).unwrap();
        drop(t);
        assert_eq!(Arc::strong_count(&observer.shared), 2);
        assert_eq!(observer.users().unwrap().sends, 1);
        assert_eq!(observer.finish_send(Side::A), Err(Failure::Refused));
        drop(guard);
        observer.finish_send(Side::A).unwrap();
        observer.finish_send(Side::B).unwrap();
        observer.finish_receive(Side::A).unwrap();
        observer.finish_receive(Side::B).unwrap();
        observer.settle().unwrap();
    }
    #[test]
    fn injected_shared_owner_refusal_retires_prepared_directions() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let retired = std::sync::Arc::new(AtomicUsize::new(0));
        let result = NetworkTransport::prepare_with(2, |mut shared| {
            let state = shared.state.get_mut().unwrap();
            assert!(
                state
                    .directions
                    .iter()
                    .all(|direction| direction.queue.capacity() >= 2)
            );
            for direction in &mut state.directions {
                direction.drop_probe = Some(DropProbe(retired.clone()));
            }
            Err(Failure::Refused)
        });
        assert!(matches!(result, Err(Failure::Refused)));
        assert_eq!(retired.load(Ordering::SeqCst), 2);
    }
}
