import @builtin.compiler.syntax as Syntax

pub first : Syntax.ExpressionFragment -> Syntax.ExpressionFragment ! {Syntax.Ops}
first fragment = syntax { $fragment }

pub second : Syntax.ExpressionFragment -> Syntax.ExpressionFragment ! {Syntax.Ops}
second fragment = syntax { $fragment }
