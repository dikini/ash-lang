pub syntax sequence $first:ident = $initial:expr then $second:ident = $next:expr in $body:expr => {
    let $first = $initial
    let $second = $next
    $body
}
