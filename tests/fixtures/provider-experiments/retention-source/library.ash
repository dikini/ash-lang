import @foreign.retention as Native
import provider as Provider

pub effect ParentOps<R> {
parent_read : Parent<R> -> Int
}
pub interface ParentProvider<R> {
parent_read : Parent<R> -> Int ! {ParentOps<R>}
}
pub resource Parent<R> {
input Int
state Native.ParentState<R>
result Provider.Scope<Native.InitError, Native.FinishError, T> for <T>
provider ParentProvider<R>
effect ParentOps<R>
interpret Native.Parent<R>
acquire value => perform Native.Parent<R>.acquire value
finish state => perform Native.Parent<R>.finish state
handlers state {
parent_read parent => resume (perform Native.Parent<R>.read state)
}
}

pub effect ChildOps<S, R> {
child_read : Child<S, R> -> Int
}
pub interface ChildProvider<S, R> {
child_read : Child<S, R> -> Int ! {ChildOps<S, R>}
}
pub resource Child<S, R> {
input (Parent<R>, Int)
state Native.ChildState<S, R>
result Provider.Scope<Native.InitError, Native.FinishError, T> for <T>
provider ChildProvider<S, R>
effect ChildOps<S, R>
interpret Native.Child<S, R>
acquire input => match input {
(parent, value) => perform Native.Child<S, R>.acquire (Provider.state_of parent, value)
}
finish state => perform Native.Child<S, R>.finish state
handlers state {
child_read child => resume (perform Native.Child<S, R>.read state)
}
}
