//! Typed tuple, constructor, pattern, and structured-match Core payloads.

use super::{NodeId, TypedBinder};
use crate::{
    source::{Origin, discard_origin_iteratively},
    types::{ConstructorId, Type, discard_type_iteratively, replace_type_iteratively},
};

/// A strict structural tuple construction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TupleNode {
    elements: Box<[NodeId]>,
}

impl TupleNode {
    pub(crate) fn new(elements: Vec<NodeId>) -> Self {
        Self {
            elements: elements.into_boxed_slice(),
        }
    }

    /// Returns tuple elements in evaluation order.
    #[must_use]
    pub fn elements(&self) -> &[NodeId] {
        &self.elements
    }
}

/// A nullary constructor value or unary payload-constructor function.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ConstructorNode {
    constructor: ConstructorId,
}

impl ConstructorNode {
    pub(crate) const fn new(constructor: ConstructorId) -> Self {
        Self { constructor }
    }

    /// Returns the stable constructor identity.
    #[must_use]
    pub const fn constructor(self) -> ConstructorId {
        self.constructor
    }
}

/// A typed structured pattern retained in Core.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CorePattern {
    /// Expected scrutinee type.
    pub ty: Type,
    /// Causal pattern provenance.
    pub origin: Origin,
    /// Structured pattern payload.
    pub kind: CorePatternKind,
}

impl CorePattern {
    /// Constructs an unchecked typed pattern for independent validation.
    #[must_use]
    pub const fn new(ty: Type, origin: Origin, kind: CorePatternKind) -> Self {
        Self { ty, origin, kind }
    }

    /// Visits every binder definition in deterministic left-to-right order.
    pub(crate) fn binders<'a>(&'a self, output: &mut Vec<&'a TypedBinder>) {
        for binder in self.binder_iter() {
            output.push(binder);
        }
    }

    pub(crate) fn binder_iter(&self) -> CorePatternBinderIter<'_> {
        CorePatternBinderIter {
            work: vec![BinderTraversalTask::Visit(self)],
        }
    }

    pub(super) fn rewrite_types<F>(&mut self, rewrite: &mut F) -> Result<(), super::BuildError>
    where
        F: FnMut(&Type) -> Result<Type, super::BuildError>,
    {
        let mut work = vec![self];
        while let Some(pattern) = work.pop() {
            let rewritten = rewrite(&pattern.ty)?;
            replace_type_iteratively(&mut pattern.ty, rewritten);
            match &mut pattern.kind {
                CorePatternKind::Binder(binder) => binder.rewrite_type(rewrite)?,
                CorePatternKind::Tuple(elements) => work.extend(elements.iter_mut()),
                CorePatternKind::Constructor { payload, .. } => {
                    if let Some(payload) = payload.as_deref_mut() {
                        work.push(payload);
                    }
                }
                CorePatternKind::Wildcard | CorePatternKind::Boolean(_) | CorePatternKind::Unit => {
                }
            }
        }
        Ok(())
    }

    /// Consumes this unchecked pattern and dismantles all metadata without
    /// following host-language recursion.
    ///
    /// Use this public disposal path for a potentially deep pattern that has
    /// not been transferred into a Core builder.
    pub fn discard_iteratively(self) {
        enum Task {
            Visit(CorePattern),
            Sequence(std::vec::IntoIter<CorePattern>),
        }

        let mut work = vec![Task::Visit(self)];
        while let Some(task) = work.pop() {
            match task {
                Task::Visit(pattern) => {
                    discard_type_iteratively(pattern.ty);
                    discard_origin_iteratively(pattern.origin);
                    match pattern.kind {
                        CorePatternKind::Binder(binder) => binder.discard_metadata(),
                        CorePatternKind::Tuple(elements) => {
                            work.push(Task::Sequence(elements.into_vec().into_iter()));
                        }
                        CorePatternKind::Constructor { payload, .. } => {
                            if let Some(payload) = payload {
                                work.push(Task::Visit(*payload));
                            }
                        }
                        CorePatternKind::Wildcard
                        | CorePatternKind::Boolean(_)
                        | CorePatternKind::Unit => {}
                    }
                }
                Task::Sequence(mut remaining) => {
                    if let Some(pattern) = remaining.next() {
                        work.push(Task::Sequence(remaining));
                        work.push(Task::Visit(pattern));
                    }
                }
            }
        }
    }
}

enum BinderTraversalTask<'a> {
    Visit(&'a CorePattern),
    Sequence(std::slice::Iter<'a, CorePattern>),
}

#[cfg(test)]
std::thread_local! {
    static BINDER_TRAVERSAL_PENDING_PEAK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(super) fn reset_binder_traversal_pending_peak() {
    BINDER_TRAVERSAL_PENDING_PEAK.with(|peak| peak.set(0));
}

#[cfg(test)]
pub(super) fn binder_traversal_pending_peak() -> usize {
    BINDER_TRAVERSAL_PENDING_PEAK.with(std::cell::Cell::get)
}

#[cfg(test)]
fn record_binder_traversal_pending(pending: usize) {
    BINDER_TRAVERSAL_PENDING_PEAK.with(|peak| peak.set(peak.get().max(pending)));
}

pub(crate) struct CorePatternBinderIter<'a> {
    work: Vec<BinderTraversalTask<'a>>,
}

impl<'a> Iterator for CorePatternBinderIter<'a> {
    type Item = &'a TypedBinder;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(task) = self.work.pop() {
            match task {
                BinderTraversalTask::Visit(pattern) => match &pattern.kind {
                    CorePatternKind::Binder(binder) => return Some(binder),
                    CorePatternKind::Tuple(elements) => {
                        self.work
                            .push(BinderTraversalTask::Sequence(elements.iter()));
                    }
                    CorePatternKind::Constructor { payload, .. } => {
                        if let Some(payload) = payload.as_deref() {
                            self.work.push(BinderTraversalTask::Visit(payload));
                        }
                    }
                    CorePatternKind::Wildcard
                    | CorePatternKind::Boolean(_)
                    | CorePatternKind::Unit => {}
                },
                BinderTraversalTask::Sequence(mut remaining) => {
                    if let Some(pattern) = remaining.next() {
                        self.work.push(BinderTraversalTask::Sequence(remaining));
                        self.work.push(BinderTraversalTask::Visit(pattern));
                    }
                }
            }
            #[cfg(test)]
            record_binder_traversal_pending(self.work.len());
        }
        None
    }
}

/// The closed typed-pattern family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CorePatternKind {
    /// A stable binder definition.
    Binder(TypedBinder),
    /// A nonbinding wildcard.
    Wildcard,
    /// A Boolean literal pattern.
    Boolean(bool),
    /// Unit.
    Unit,
    /// A structural tuple pattern.
    Tuple(Box<[CorePattern]>),
    /// A nominal constructor and optional payload pattern.
    Constructor {
        /// Stable constructor identity.
        constructor: ConstructorId,
        /// Optional semantic payload pattern.
        payload: Option<Box<CorePattern>>,
    },
}

/// One source-ordered structured-match arm.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoreMatchArm {
    pattern: Option<CorePattern>,
    body: NodeId,
    origin: Option<Origin>,
}

impl CoreMatchArm {
    /// Constructs one unchecked match arm.
    #[must_use]
    pub const fn new(pattern: CorePattern, body: NodeId, origin: Origin) -> Self {
        Self {
            pattern: Some(pattern),
            body,
            origin: Some(origin),
        }
    }

    /// Returns the arm pattern.
    #[must_use]
    pub const fn pattern(&self) -> &CorePattern {
        self.pattern
            .as_ref()
            .expect("a live Core match arm retains its pattern")
    }

    /// Returns the selected body handle.
    #[must_use]
    pub const fn body(&self) -> NodeId {
        self.body
    }

    /// Returns arm provenance.
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        self.origin
            .as_ref()
            .expect("a live Core match arm retains its origin")
    }

    pub(super) fn into_parts(mut self) -> (CorePattern, NodeId, Origin) {
        (
            self.pattern
                .take()
                .expect("a live Core match arm retains its pattern"),
            self.body,
            self.origin
                .take()
                .expect("a live Core match arm retains its origin"),
        )
    }

    pub(super) fn pattern_mut(&mut self) -> &mut CorePattern {
        self.pattern
            .as_mut()
            .expect("a live Core match arm retains its pattern")
    }

    fn discard_contents(&mut self) {
        if let Some(pattern) = self.pattern.take() {
            pattern.discard_iteratively();
        }
        if let Some(origin) = self.origin.take() {
            discard_origin_iteratively(origin);
        }
    }
}

impl Drop for CoreMatchArm {
    fn drop(&mut self) {
        self.discard_contents();
    }
}

/// A structured match whose scrutinee is evaluated once.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MatchNode {
    scrutinee: NodeId,
    arms: Box<[CoreMatchArm]>,
}

impl MatchNode {
    pub(crate) fn new(scrutinee: NodeId, arms: Vec<CoreMatchArm>) -> Self {
        Self {
            scrutinee,
            arms: arms.into_boxed_slice(),
        }
    }

    /// Returns the scrutinee handle.
    #[must_use]
    pub const fn scrutinee(&self) -> NodeId {
        self.scrutinee
    }

    /// Returns arms in selection order.
    #[must_use]
    pub fn arms(&self) -> &[CoreMatchArm] {
        &self.arms
    }

    pub(super) fn arms_mut(&mut self) -> &mut [CoreMatchArm] {
        &mut self.arms
    }

    pub(super) fn discard_metadata(self) {
        for arm in self.arms.into_vec() {
            let (pattern, _, origin) = arm.into_parts();
            pattern.discard_iteratively();
            discard_origin_iteratively(origin);
        }
    }
}
