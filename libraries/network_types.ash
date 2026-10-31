pub type Identity = Root
    | Work(Int, Int)
pub type Parent = NoParent
    | Parent(Int, Identity)
pub type Envelope = WorkOut(Identity, Parent, Int, Bytes)
    | AckOut(Parent, Identity)
