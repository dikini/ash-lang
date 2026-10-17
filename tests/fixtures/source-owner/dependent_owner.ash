import @builtin.foreign as Foreign

pub foreign library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = opaque
    repr ParentBytes = bytes
    owner ParentState<P> {
        representation ParentBytes
        owned P
        teardown ParentFree
    }
    owner ChildState<P, R> {
        representation Address
        owned R
        retains P
        teardown ChildFree
    }
    symbol ParentAllocate<P> : Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<ParentState<P>>>> {
        name "ash_parent_acquire"
        abi (Size) -> pointer(ParentBytes)
        operand 0 from 0 scalar
        output result as owner(ParentState<P>)
        outcome result nonnull { readable result, initialized_bytes result from 0 }
        outcome otherwise { readable result }
    }
    symbol ParentFree<P> : ParentState<P> -> Foreign.Call<Foreign.Disposition<Unit>> {
        name "ash_parent_release"
        abi (pointer(ParentBytes)) -> void
        operand 0 from 0 current
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
    symbol ChildAllocate<P, R> : (ParentState<P>, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<ChildState<P, R>>>> {
        name "ash_child_acquire"
        abi (pointer(ParentBytes), Size) -> pointer(Address)
        operand 0 from 0 enclosing
        operand 1 from 1 scalar
        output result as owner(ChildState<P, R>)
        outcome result nonnull { readable result }
        outcome otherwise { readable result }
    }
    symbol ChildFree<P, R> : (ChildState<P, R>, ParentState<P>) -> Foreign.Call<Foreign.Disposition<Unit>> {
        name "ash_child_release"
        abi (pointer(Address), pointer(ParentBytes)) -> void
        operand 0 from 0 current
        operand 1 from 1 enclosing
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
    symbol ChildHold<P, R> : (ChildState<P, R>, ParentState<P>) -> Foreign.Call<Foreign.Disposition<Unit>> {
        name "ash_child_hold"
        abi (pointer(Address), pointer(ParentBytes)) -> void
        operand 0 from 0 current
        operand 1 from 1 enclosing
        retained_dependents block
        outcome otherwise { retained 0 }
    }
}

pub type Acquire<S, D, I> = Acquired(S, D)
    | Refused(I)
pub type Finish<S, E> = Consumed
    | ConsumedFailure(E)
    | Retained(S, E)
pub type Completion<E> = Closed
    | ConsumedError(E)
    | RetainedError(E)
pub type Scope<I, E, T> = NotAcquired(I)
    | Completed(T, Completion<E>)

pub interface ParentProvider<Access, State> {
    read : Access -> Int ! {ParentOps<Access, State>}
    borrow : Access -> State ! {ParentOps<Access, State>}
}
pub effect ParentOps<Access, State> {
    borrow : Access -> State
    read : Access -> Int
}
pub resource Parent<P> {
    owned P
    input Int
    state ParentState<P>
    data Int
    acquisition Acquire<ParentState<P>, Int, Unit>
    completion Finish<ParentState<P>, Unit>
    result Scope<Unit, Unit, Answer> for <Answer>
    codec scope
    provider ParentProvider<Parent<P>, ParentState<P>>
    effect ParentOps<Parent<P>, ParentState<P>>
    interpret ParentAllocate<P>, ParentFree<P>
    acquire label => match perform ParentAllocate<P>.call label {
        Foreign.Returned(Foreign.Readable(Foreign.NonNull(state))) => Acquired(state, label)
        Foreign.Returned(Foreign.Readable(Foreign.Null)) => Refused ()
        Foreign.Returned(Foreign.Unreadable) => Refused ()
        Foreign.ConversionFailed(_) => Refused ()
    }
    finish (state, data) => {
        let marked = Foreign.byte_write (state, 0, 99)
        match perform ParentFree<P>.call state {
            Foreign.Returned(Foreign.Consumed(())) => Consumed
            Foreign.Returned(Foreign.Retained(())) => Retained(state, ())
            Foreign.Returned(Foreign.BlockedDependent) => Retained(state, ())
            Foreign.ConversionFailed(_) => Retained(state, ())
        }
    }
    handlers (state, data) {
        borrow access => resume state
        read access => resume data
    }
}
pub interface ChildProvider<Access> {
    child_read : Access -> Int ! {ChildOps<Access>}
}
pub effect ChildOps<Access> {
    child_read : Access -> Int
}
pub resource Child<P, R> {
    owned R
    input (Parent<P>, Int)
    state ChildState<P, R>
    data (Parent<P>, Int)
    acquisition Acquire<ChildState<P, R>, (Parent<P>, Int), Unit>
    completion Finish<ChildState<P, R>, Unit>
    result Scope<Unit, Unit, Answer> for <Answer>
    codec scope
    provider ChildProvider<Child<P, R>>
    effect ChildOps<Child<P, R>>
    interpret ChildAllocate<P, R>, ChildHold<P, R>
    acquire (parent, label) => {
        let dependency = perform ParentOps<Parent<P>, ParentState<P>>.borrow parent
        match perform ChildAllocate<P, R>.call (dependency, label) {
            Foreign.Returned(Foreign.Readable(Foreign.NonNull(state))) => Acquired(state, (parent, label))
            Foreign.Returned(Foreign.Readable(Foreign.Null)) => Refused ()
            Foreign.Returned(Foreign.Unreadable) => Refused ()
            Foreign.ConversionFailed(_) => Refused ()
        }
    }
    finish (state, (parent, label)) => {
        let dependency = perform ParentOps<Parent<P>, ParentState<P>>.borrow parent
        match perform ChildHold<P, R>.call (state, dependency) {
            Foreign.Returned(Foreign.Consumed(())) => Consumed
            Foreign.Returned(Foreign.Retained(())) => Retained(state, ())
            Foreign.Returned(Foreign.BlockedDependent) => Retained(state, ())
            Foreign.ConversionFailed(_) => Retained(state, ())
        }
    }
    handlers (state, (parent, label)) {
        child_read access => resume label
    }
}
