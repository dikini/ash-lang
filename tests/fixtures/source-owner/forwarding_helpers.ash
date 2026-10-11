import owner as Owner

pub pair<Access> : (Access, Int) -> (Int, Int) ! {Owner.ProbeOps<Access>} where Owner.ProbeProvider<Access>
pair (access, delta) = {
    let value = Owner.read access
    let offset = Owner.offset (access, delta)
    (value, offset)
}

pub relay<Access> : (Access, Int) -> (Int, Int) ! {Owner.ProbeOps<Access>} where Owner.ProbeProvider<Access>
relay (access, delta) = pair (access, delta)
