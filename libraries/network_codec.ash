import @builtin.bytes as B
import @builtin.integer as Integer

import network_types as Network

pub type EncodeResult = Encoded(Bytes)
    | EncodeFailed
pub type DecodeResult = WorkDecoded(Network.Identity, Network.Parent, Bytes)
    | AckDecoded(Network.Parent, Network.Identity)
    | InvalidFrame

type NatRead = Nat(Int, Int)
    | InvalidNat
type IdentityRead = ReadIdentity(Network.Identity, Int)
    | InvalidIdentity
type AddressRead = ReadAddress(Network.Parent, Int)
    | InvalidAddress
type PayloadRead = ReadPayload(Bytes, Int)
    | InvalidPayload

append : (Bytes, Int) -> EncodeResult
append (buffer, byte) = match B.append_byte (buffer, byte) {
    B.BytesAppended(next) => Encoded(next)
    B.InvalidByte => EncodeFailed
}

write_digits : (Bytes, Int, Int) -> EncodeResult
write_digits (buffer, quotient, remainder) = match append (buffer, 1) {
    EncodeFailed => EncodeFailed
    Encoded(marked) => match append (marked, remainder) {
        EncodeFailed => EncodeFailed
        Encoded(next) => write_nat (next, quotient)
    }
}

write_nat : (Bytes, Int) -> EncodeResult
write_nat (buffer, value) = match value == 0 {
    true => append (buffer, 0)
    false => match Integer.split_base256 value {
        Integer.Negative => EncodeFailed
        Integer.Parts((quotient, remainder)) => write_digits (buffer, quotient, remainder)
    }
}

write_identity : (Bytes, Network.Identity) -> EncodeResult
write_identity (buffer, identity) = match identity {
    Network.Root => append (buffer, 16)
    Network.Work(owner, serial) => match append (buffer, 17) {
        EncodeFailed => EncodeFailed
        Encoded(tagged) => match write_nat (tagged, owner) {
            EncodeFailed => EncodeFailed
            Encoded(with_owner) => write_nat (with_owner, serial)
        }
    }
}

write_address : (Bytes, Network.Parent) -> EncodeResult
write_address (buffer, address) = match address {
    Network.NoParent => EncodeFailed
    Network.Parent(owner, identity) => match write_nat (buffer, owner) {
        EncodeFailed => EncodeFailed
        Encoded(with_owner) => write_identity (with_owner, identity)
    }
}

copy_bytes : (Bytes, Bytes, Int, Int) -> EncodeResult
copy_bytes (source, buffer, cursor, length) = match cursor == length {
    true => Encoded(buffer)
    false => match B.at (source, cursor) {
        B.InvalidIndex => EncodeFailed
        B.ByteAt(byte) => match append (buffer, byte) {
            EncodeFailed => EncodeFailed
            Encoded(next) => copy_bytes (source, next, cursor + 1, length)
        }
    }
}

encode_work_payload : (Bytes, Bytes) -> EncodeResult
encode_work_payload (buffer, payload) = match write_nat (buffer, B.length payload) {
    EncodeFailed => EncodeFailed
    Encoded(header) => copy_bytes (payload, header, 0, B.length payload)
}

encode_work_parent : (Bytes, Network.Parent, Bytes) -> EncodeResult
encode_work_parent (buffer, parent, payload) = match write_address (buffer, parent) {
    EncodeFailed => EncodeFailed
    Encoded(with_parent) => encode_work_payload (with_parent, payload)
}

encode_work : (Network.Identity, Network.Parent, Bytes) -> EncodeResult
encode_work (child, parent, payload) = match append (B.empty (), 32) {
    EncodeFailed => EncodeFailed
    Encoded(tagged) => match write_identity (tagged, child) {
        EncodeFailed => EncodeFailed
        Encoded(with_child) => encode_work_parent (with_child, parent, payload)
    }
}

encode_ack : (Network.Parent, Network.Identity) -> EncodeResult
encode_ack (parent, child) = match append (B.empty (), 33) {
    EncodeFailed => EncodeFailed
    Encoded(tagged) => match write_address (tagged, parent) {
        EncodeFailed => EncodeFailed
        Encoded(with_parent) => write_identity (with_parent, child)
    }
}

pub encode : Network.Envelope -> EncodeResult
encode frame = match frame {
    Network.WorkOut(child, parent, destination, payload) => encode_work (child, parent, payload)
    Network.AckOut(parent, child) => encode_ack (parent, child)
}

read_nat_end : (Int, Int, Bool, Int) -> NatRead
read_nat_end (cursor, value, has_digit, last) = match has_digit {
    false => Nat(value, cursor + 1)
    true => match last == 0 {
        true => InvalidNat
        false => Nat(value, cursor + 1)
    }
}

read_nat_digit : (Bytes, Int, Int, Int) -> NatRead
read_nat_digit (buffer, cursor, value, power) = match B.at (buffer, cursor + 1) {
    B.InvalidIndex => InvalidNat
    B.ByteAt(digit) => read_nat_step (buffer, cursor + 2, value + digit * power, power * 256, true, digit)
}

read_nat_step : (Bytes, Int, Int, Int, Bool, Int) -> NatRead
read_nat_step (buffer, cursor, value, power, has_digit, last) = match B.at (buffer, cursor) {
    B.InvalidIndex => InvalidNat
    B.ByteAt(marker) => match marker == 0 {
        true => read_nat_end (cursor, value, has_digit, last)
        false => match marker == 1 {
            false => InvalidNat
            true => read_nat_digit (buffer, cursor, value, power)
        }
    }
}

read_nat : (Bytes, Int) -> NatRead
read_nat (buffer, cursor) = read_nat_step (buffer, cursor, 0, 1, false, 0)

read_work_identity : (Bytes, Int) -> IdentityRead
read_work_identity (buffer, cursor) = match read_nat (buffer, cursor) {
    InvalidNat => InvalidIdentity
    Nat(owner, after_owner) => match read_nat (buffer, after_owner) {
        InvalidNat => InvalidIdentity
        Nat(serial, after_serial) => ReadIdentity(Network.Work(owner, serial), after_serial)
    }
}

read_identity : (Bytes, Int) -> IdentityRead
read_identity (buffer, cursor) = match B.at (buffer, cursor) {
    B.InvalidIndex => InvalidIdentity
    B.ByteAt(tag) => match tag == 16 {
        true => ReadIdentity(Network.Root, cursor + 1)
        false => match tag == 17 {
            false => InvalidIdentity
            true => read_work_identity (buffer, cursor + 1)
        }
    }
}

read_address : (Bytes, Int) -> AddressRead
read_address (buffer, cursor) = match read_nat (buffer, cursor) {
    InvalidNat => InvalidAddress
    Nat(owner, after_owner) => match read_identity (buffer, after_owner) {
        InvalidIdentity => InvalidAddress
        ReadIdentity(identity, after_identity) => ReadAddress(Network.Parent(owner, identity), after_identity)
    }
}

read_payload : (Bytes, Int, Int, Int, Bytes) -> PayloadRead
read_payload (source, cursor, copied, length, destination) = match copied == length {
    true => ReadPayload(destination, cursor)
    false => match B.at (source, cursor) {
        B.InvalidIndex => InvalidPayload
        B.ByteAt(byte) => match append (destination, byte) {
            EncodeFailed => InvalidPayload
            Encoded(next) => read_payload (source, cursor + 1, copied + 1, length, next)
        }
    }
}

finish_work : (Bytes, Network.Identity, Network.Parent, Int, Int) -> DecodeResult
finish_work (buffer, child, parent, length, cursor) = match read_payload (buffer, cursor, 0, length, B.empty ()) {
    InvalidPayload => InvalidFrame
    ReadPayload(payload, after_payload) => match after_payload == B.length buffer {
        true => WorkDecoded(child, parent, payload)
        false => InvalidFrame
    }
}

read_work : (Bytes, Int) -> DecodeResult
read_work (buffer, cursor) = match read_identity (buffer, cursor) {
    InvalidIdentity => InvalidFrame
    ReadIdentity(child, after_child) => match read_address (buffer, after_child) {
        InvalidAddress => InvalidFrame
        ReadAddress(parent, after_parent) => match read_nat (buffer, after_parent) {
            InvalidNat => InvalidFrame
            Nat(length, after_length) => finish_work (buffer, child, parent, length, after_length)
        }
    }
}

read_ack : (Bytes, Int) -> DecodeResult
read_ack (buffer, cursor) = match read_address (buffer, cursor) {
    InvalidAddress => InvalidFrame
    ReadAddress(parent, after_parent) => match read_identity (buffer, after_parent) {
        InvalidIdentity => InvalidFrame
        ReadIdentity(child, after_child) => match after_child == B.length buffer {
            true => AckDecoded(parent, child)
            false => InvalidFrame
        }
    }
}

pub decode : Bytes -> DecodeResult
decode buffer = match B.at (buffer, 0) {
    B.InvalidIndex => InvalidFrame
    B.ByteAt(tag) => match tag == 32 {
        true => read_work (buffer, 1)
        false => match tag == 33 {
            true => read_ack (buffer, 1)
            false => InvalidFrame
        }
    }
}
