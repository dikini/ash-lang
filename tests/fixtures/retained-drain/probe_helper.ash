import @builtin.retained_control as Control
pub observe<N> : Unit -> Bool ! {Control.Probe<N>}
observe ignored = perform Control.Probe<N>.quiescent ()
