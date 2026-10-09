pub import @foreign.provider (StateAccess, state_of)

pub type Completion<E> = Closed
    | ConsumedError(E)
    | RetainedError(E)

pub type Scope<I, E, T> = NotAcquired(I)
    | Completed(T, Completion<E>)
