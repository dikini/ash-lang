use ash::integer::Integer;

#[test]
fn parses_zero() {
    let integer = Integer::parse_decimal("0").unwrap();

    assert_eq!(integer.to_string(), "0");
}

#[test]
fn parses_a_decimal_beyond_machine_width() {
    let integer = Integer::parse_decimal("18446744073709551616").unwrap();

    assert_eq!(integer.to_string(), "18446744073709551616");
}

#[test]
fn adds_integers_beyond_machine_width() {
    let left = Integer::parse_decimal("18446744073709551616").unwrap();
    let right = Integer::parse_decimal("18446744073709551616").unwrap();

    let sum = &left + &right;

    assert_eq!(sum.to_string(), "36893488147419103232");
}

#[test]
fn multiplies_integers_beyond_machine_width() {
    let left = Integer::parse_decimal("18446744073709551616").unwrap();
    let right = Integer::parse_decimal("18446744073709551616").unwrap();

    let product = &left * &right;

    assert_eq!(
        product.to_string(),
        "340282366920938463463374607431768211456"
    );
}

#[test]
fn rejects_a_negative_literal() {
    assert!(Integer::parse_decimal("-1").is_err());
}

#[test]
fn rejects_a_leading_zero() {
    assert!(Integer::parse_decimal("01").is_err());
}

#[test]
fn rejects_a_digit_separator() {
    assert!(Integer::parse_decimal("1_000").is_err());
}

#[test]
fn rejects_empty_input() {
    assert!(Integer::parse_decimal("").is_err());
}
