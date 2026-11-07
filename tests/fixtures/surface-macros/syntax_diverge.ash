import @builtin.compiler.syntax as Syntax

pub syntax never $value:expr => using diverge

diverge : Syntax.Input -> Syntax.MacroResult
diverge input = diverge input
