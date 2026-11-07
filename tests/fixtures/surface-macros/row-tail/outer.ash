import forms (syntax wrap)

pub syntax captured $name:ident in $body:expr => {
    wrap $name in $body
}

pub syntax introduced $body:expr => {
    wrap R in $body
}
