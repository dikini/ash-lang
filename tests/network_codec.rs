use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
};
use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

fn run(body: &str) -> String {
    let directory = std::env::temp_dir().join(format!(
        "ash-network-codec-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    fs::write(
        directory.join("network_types.ash"),
        include_str!("../libraries/network_types.ash"),
    )
    .unwrap();
    fs::write(
        directory.join("network_codec.ash"),
        include_str!("../libraries/network_codec.ash"),
    )
    .unwrap();
    fs::write(
        directory.join("entry.ash"),
        format!(
            r#"import network_types as Network
import network_codec as Codec
import @builtin.bytes as B
add : (Bytes, Int) -> Bytes
add (buffer, byte) = match B.append_byte (buffer, byte) {{
    B.BytesAppended(next) => next
    B.InvalidByte => B.empty ()
}}
{body}
"#
        ),
    )
    .unwrap();
    let result = run_path(RunConfiguration {
        entry: directory.join("entry.ash"),
        roots: ModuleRoots::empty(),
    });
    fs::remove_dir_all(directory).unwrap();
    result
        .unwrap_or_else(|error| panic!("{error:?}"))
        .value_display()
        .to_owned()
}

fn build(bytes: &[u8], variable: &str) -> String {
    let mut code = format!("let {variable}0 = B.empty ()\n");
    for (index, byte) in bytes.iter().enumerate() {
        code.push_str(&format!(
            "let {variable}{} = add ({variable}{index}, {byte})\n",
            index + 1
        ));
    }
    code
}

#[test]
fn work_and_ack_encode_the_exact_canonical_bytes() {
    for (envelope, expected) in [
        (
            "Network.WorkOut(Network.Work(256, 255), Network.Parent(0, Network.Root), 9, payload3)",
            vec![32, 17, 1, 0, 1, 1, 0, 1, 255, 0, 0, 16, 1, 3, 0, 0, 255, 1],
        ),
        (
            "Network.AckOut(Network.Parent(256, Network.Work(1, 0)), Network.Root)",
            vec![33, 1, 0, 1, 1, 0, 17, 1, 1, 0, 0, 16],
        ),
    ] {
        let prefix = build(&[0, 255, 1], "payload") + &build(&expected, "expected");
        let source = format!(
            "main : Unit -> Bool\nmain () = {{\n{prefix}\nmatch Codec.encode ({envelope}) {{\nCodec.EncodeFailed => false\nCodec.Encoded(actual) => B.equal (actual, expected{})\n}}\n}}\n",
            expected.len()
        );
        assert_eq!(run(&source), "true");
    }
}

#[test]
fn decode_returns_ordered_fields_and_exact_payload() {
    let wire = [32, 17, 1, 0, 1, 1, 0, 1, 255, 0, 0, 16, 1, 3, 0, 0, 255, 1];
    let source = format!(
        r#"identity : Network.Identity -> (Int, Int, Int)
identity value = match value {{
    Network.Root => (0, 0, 0)
    Network.Work(owner, serial) => (1, owner, serial)
}}
parent : Network.Parent -> (Int, (Int, Int, Int))
parent value = match value {{
    Network.NoParent => (999, (999, 999, 999))
    Network.Parent(owner, id) => (owner, identity id)
}}
main : Unit -> ((Int, Int, Int), (Int, (Int, Int, Int)), Bool)
main () = {{
{prefix}
{payload}
match Codec.decode wire{n} {{
    Codec.InvalidFrame => ((999, 999, 999), (999, (999, 999, 999)), false)
    Codec.AckDecoded(address, child) => ((998, 998, 998), (998, (998, 998, 998)), false)
    Codec.WorkDecoded(child, address, bytes) => (identity child, parent address, B.equal (bytes, payload3))
}}
}}
"#,
        prefix = build(&wire, "wire"),
        payload = build(&[0, 255, 1], "payload"),
        n = wire.len()
    );
    assert_eq!(run(&source), "((1, 256, 255), (0, (0, 0, 0)), true)");
}

#[test]
fn decoder_rejects_bad_tags_scalars_lengths_and_suffixes() {
    let cases: &[&[u8]] = &[
        &[],
        &[34],
        &[33],
        &[33, 2],
        &[33, 1],
        &[33, 1, 0, 0, 16, 16],
        &[33, 0, 18, 16],
        &[33, 0, 16],
        &[33, 0, 16, 16, 0],
        &[32, 16, 0, 16, 1, 2, 0, 42],
    ];
    for wire in cases {
        let source = format!(
            "main : Unit -> Bool\nmain () = {{\n{}\nmatch Codec.decode wire{} {{\nCodec.InvalidFrame => true\nCodec.WorkDecoded(child, parent, payload) => false\nCodec.AckDecoded(parent, child) => false\n}}\n}}\n",
            build(wire, "wire"),
            wire.len()
        );
        assert_eq!(run(&source), "true", "wire {wire:?}");
    }
}

#[test]
fn zero_root_ack_and_empty_work_payload_decode() {
    for wire in [vec![33, 0, 16, 16], vec![32, 16, 0, 16, 0]] {
        let source = format!(
            "main : Unit -> Int\nmain () = {{\n{}\nmatch Codec.decode wire{} {{\nCodec.InvalidFrame => 0\nCodec.WorkDecoded(child, parent, payload) => B.length payload + 1\nCodec.AckDecoded(parent, child) => 2\n}}\n}}\n",
            build(&wire, "wire"),
            wire.len()
        );
        let expected = if wire[0] == 33 { "2" } else { "1" };
        assert_eq!(run(&source), expected);
    }
}

#[test]
fn encoding_rejects_absent_parent() {
    assert_eq!(
        run(r#"main : Unit -> Bool
main () = match Codec.encode (Network.AckOut(Network.NoParent, Network.Root)) {
    Codec.EncodeFailed => true
    Codec.Encoded(bytes) => false
}
"#),
        "true"
    );
}

#[test]
fn integer_fields_are_not_limited_to_host_word_size() {
    let mut expected = vec![33];
    for _ in 0..32 {
        expected.extend([1, 0]);
    }
    expected.extend([1, 1, 0, 16, 16]);
    let source = format!(
        "main : Unit -> Bool\nmain () = {{\n{}\nmatch Codec.encode (Network.AckOut(Network.Parent(115792089237316195423570985008687907853269984665640564039457584007913129639936, Network.Root), Network.Root)) {{\nCodec.EncodeFailed => false\nCodec.Encoded(actual) => B.equal (actual, expected{})\n}}\n}}\n",
        build(&expected, "expected"),
        expected.len()
    );
    assert_eq!(run(&source), "true");
}

#[test]
fn decoding_preserves_integer_fields_beyond_host_word_size() {
    let mut wire = vec![33];
    for _ in 0..32 {
        wire.extend([1, 0]);
    }
    wire.extend([1, 1, 0, 16, 16]);
    let source = format!(
        "main : Unit -> Bool\nmain () = {{\n{}\nmatch Codec.decode wire{} {{\nCodec.InvalidFrame => false\nCodec.WorkDecoded(child, parent, payload) => false\nCodec.AckDecoded(parent, child) => match (parent, child) {{\n(Network.Parent(owner, Network.Root), Network.Root) => owner == 115792089237316195423570985008687907853269984665640564039457584007913129639936\n_ => false\n}}\n}}\n}}\n",
        build(&wire, "wire"),
        wire.len()
    );
    assert_eq!(run(&source), "true");
}
