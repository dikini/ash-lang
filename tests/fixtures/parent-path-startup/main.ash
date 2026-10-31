import @buffers.buffer as Buffer
import @builtin.generic_cell as Scoped

type Lookup = Root(Int, Int, Int)

effect Parents {
    read : Int -> Buffer.Outcome<Int>
    write : (Int, Int) -> Buffer.Outcome<Unit>
}

record_root : (Int, Bool, Lookup) -> Buffer.Outcome<Lookup> ! {Parents}
record_root (node, false, Root(root, reads, writes)) = Buffer.Success(Root(root, reads + 1, writes))
record_root (node, true, Root(root, reads, writes)) = {
    match perform Parents.write (node, root) {
        Buffer.Failure(error) => Buffer.Failure(error)
        Buffer.Success(()) => Buffer.Success(Root(root, reads + 1, writes + 1))
    }
}

find_root : (Int, Bool) -> Buffer.Outcome<Lookup> ! {Parents}
find_root (node, compress) = match perform Parents.read node {
    Buffer.Failure(error) => Buffer.Failure(error)
    Buffer.Success(parent) => match parent == node {
        true => Buffer.Success(Root(node, 1, 0))
        false => match find_root (parent, compress) {
            Buffer.Failure(error) => Buffer.Failure(error)
            Buffer.Success(result) => record_root (node, compress, result)
        }
    }
}

repeat_lookup : Bool -> Buffer.Outcome<(Lookup, Lookup)> ! {Parents}
repeat_lookup compress = match find_root (3, compress) {
    Buffer.Failure(error) => Buffer.Failure(error)
    Buffer.Success(first) => match find_root (3, compress) {
        Buffer.Failure(error) => Buffer.Failure(error)
        Buffer.Success(second) => Buffer.Success((first, second))
    }
}

run_with_parents<R> : (
    (Scoped.Cell<R, Bytes>, Bool) -> Buffer.Outcome<(Lookup, Lookup)>
    ! {Scoped.Ops<R, Bytes>}
) where Scoped.Provider<R, Bytes>
run_with_parents (parents, compress) = match Buffer.write (parents, 2, 1) {
    Buffer.Failure(error) => Buffer.Failure error
    Buffer.Success(()) => match Buffer.write (parents, 3, 2) {
        Buffer.Failure(error) => Buffer.Failure error
        Buffer.Success(()) => handle (repeat_lookup compress) with Parents {
            read index => resume (Buffer.read (parents, index))
            write pair => {
                let (index, parent) = pair
                resume (Buffer.write (parents, index, parent))
            }
        }
    }
}

run : Bool -> Buffer.Outcome<Buffer.Outcome<(Lookup, Lookup)>>
run compress = match Buffer.create 4 {
    Buffer.Failure(error) => Buffer.Failure error
    Buffer.Success(initial_bytes) => Buffer.Success (
        resource Scoped.Cell<R, Bytes> parents = initial_bytes {
            run_with_parents (parents, compress)
        }
    )
}

main : Unit -> (Buffer.Outcome<Buffer.Outcome<(Lookup, Lookup)>>,
    Buffer.Outcome<Buffer.Outcome<(Lookup, Lookup)>>)
main () = (run false, run true)
