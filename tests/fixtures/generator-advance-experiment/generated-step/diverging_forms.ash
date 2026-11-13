import @builtin.compiler.syntax as Syntax
import stepdefs as Helpers

pub syntax declaration: (diverging) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = $number
    )+
} with {
    $number from 0 step Helpers.actual_step
}
