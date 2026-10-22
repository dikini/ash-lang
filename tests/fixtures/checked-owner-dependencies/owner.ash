import @builtin.foreign as Foreign

foreign checked library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = opaque
    assumption Callee "the admitted parent and child native owner contracts hold"
    owner ParentState<H, C> {
        representation Address
        owned C
        host H
        teardown ParentFree
    }
    owner ChildState<H, C, S> {
        representation Address
        owned S
        host H
        retains C
        teardown ChildFree
    }
    symbol ParentAllocate<H, C> : Int -> Foreign.CheckedCall<Foreign.Output<Foreign.Nullable<ParentState<H, C>>>> {
        name "ash_parent_acquire"
        abi (Size) -> pointer(Address)
        host H
        assumes { Callee }
        operand 0 from 0 scalar
        output result as owner(ParentState<H, C>)
        outcome result nonnull { readable result }
        outcome otherwise { readable result }
    }
    symbol ParentFree<H, C> : ParentState<H, C> -> Foreign.CheckedCall<Foreign.Disposition<Unit>> {
        name "ash_parent_release"
        abi (pointer(Address)) -> void
        host H
        assumes { Callee }
        operand 0 from 0 current
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
    symbol ChildAllocate<H, C, S> : (ParentState<H, C>, Int) -> Foreign.CheckedCall<Foreign.Output<Foreign.Nullable<ChildState<H, C, S>>>> {
        name "ash_child_acquire"
        abi (pointer(Address), Size) -> pointer(Address)
        host H
        assumes { Callee }
        operand 0 from 0 enclosing
        operand 1 from 1 scalar
        output result as owner(ChildState<H, C, S>)
        outcome result nonnull { readable result }
        outcome otherwise { readable result }
    }
    symbol ChildFree<H, C, S> : (ChildState<H, C, S>, ParentState<H, C>) -> Foreign.CheckedCall<Foreign.Disposition<Unit>> {
        name "ash_child_release"
        abi (pointer(Address), pointer(Address)) -> void
        host H
        assumes { Callee }
        operand 0 from 0 current
        operand 1 from 1 enclosing
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
}

pub type Acquire<S, D, I> = Acquired(S, D)
    | Refused(I)

interface ParentProvider<Access, State> {
    borrow : Access -> State ! {ParentOps<Access, State>}
}
effect ParentOps<Access, State> {
    borrow : Access -> State
}
resource Parent<H, C> {
    owned C
    host H
    input Int
    state ParentState<H, C>
    data Unit
    acquisition Acquire<ParentState<H, C>, Unit, Unit>
    completion Foreign.CheckedFinish<ParentState<H, C>, Unit>
    result Foreign.CheckedScope<Answer, Unit, Unit> for <Answer>
    codec checked_scope
    provider ParentProvider<Parent<H, C>, ParentState<H, C>>
    effect ParentOps<Parent<H, C>, ParentState<H, C>>
    interpret ParentAllocate<H, C>, ParentFree<H, C>
    acquire size => match perform ParentAllocate<H, C>.call size {
        Foreign.CheckedReturned(Foreign.Readable(Foreign.NonNull(state))) => Acquired(state, ())
        Foreign.CheckedReturned(Foreign.Readable(Foreign.Null)) => Refused ()
        Foreign.CheckedReturned(Foreign.Unreadable) => Refused ()
        Foreign.CheckedConversionFailed(_) => Refused ()
        Foreign.BoundaryFailed(_) => Refused ()
    }
    finish (state, data) => match perform ParentFree<H, C>.call state {
        Foreign.CheckedReturned(Foreign.Consumed(())) => Foreign.FinishedConsumed Foreign.FinishOk
        Foreign.CheckedReturned(Foreign.Retained(())) => Foreign.FinishedRetained(state, ())
        Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason
        Foreign.CheckedReturned(Foreign.BlockedDependent) => Foreign.FinishedConsumed Foreign.FinishOk
        Foreign.CheckedConversionFailed(_) => Foreign.FinishedConsumed Foreign.FinishOk
    }
    handlers (state, data) {
        borrow access => resume state
    }
}

interface ChildProvider<Access> {
    read : Access -> Int ! {ChildOps<Access>}
}
effect ChildOps<Access> {
    read : Access -> Int
}
resource Child<H, C, S> {
    owned S
    host H
    input (Parent<H, C>, Int)
    state ChildState<H, C, S>
    data (Parent<H, C>, Int)
    acquisition Acquire<ChildState<H, C, S>, (Parent<H, C>, Int), Unit>
    completion Foreign.CheckedFinish<ChildState<H, C, S>, Unit>
    result Foreign.CheckedScope<Answer, Unit, Unit> for <Answer>
    codec checked_scope
    provider ChildProvider<Child<H, C, S>>
    effect ChildOps<Child<H, C, S>>
    interpret ChildAllocate<H, C, S>, ChildFree<H, C, S>
    acquire (parent, label) => {
        let dependency = perform ParentOps<Parent<H, C>, ParentState<H, C>>.borrow parent
        match perform ChildAllocate<H, C, S>.call (dependency, label) {
            Foreign.CheckedReturned(Foreign.Readable(Foreign.NonNull(state))) => Acquired(state, (parent, label))
            Foreign.CheckedReturned(Foreign.Readable(Foreign.Null)) => Refused ()
            Foreign.CheckedReturned(Foreign.Unreadable) => Refused ()
            Foreign.CheckedConversionFailed(_) => Refused ()
            Foreign.BoundaryFailed(_) => Refused ()
        }
    }
    finish (state, (parent, label)) => {
        let dependency = perform ParentOps<Parent<H, C>, ParentState<H, C>>.borrow parent
        match perform ChildFree<H, C, S>.call (state, dependency) {
            Foreign.CheckedReturned(Foreign.Consumed(())) => Foreign.FinishedConsumed Foreign.FinishOk
            Foreign.CheckedReturned(Foreign.Retained(())) => Foreign.FinishedRetained(state, ())
            Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason
            Foreign.CheckedReturned(Foreign.BlockedDependent) => Foreign.FinishedConsumed Foreign.FinishOk
            Foreign.CheckedConversionFailed(_) => Foreign.FinishedConsumed Foreign.FinishOk
        }
    }
    handlers (state, (parent, label)) {
        read access => resume label
    }
}

pub run : Unit -> Foreign.CheckedScope<Foreign.CheckedScope<Int, Unit, Unit>, Unit, Unit>
run () = foreign host H {
    resource Parent<H, C> parent = 64 {
        resource Child<H, C, S> child = (parent, 4) {
            read child
        }
    }
}
