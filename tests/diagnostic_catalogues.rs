use ash::message::{Catalogue, Locale, Message};

#[test]
fn binding_messages_have_precise_english_and_bulgarian_text() {
    let message = Message::BindingInitializer {
        expected: "Bool",
        found: "Int",
    };
    assert_eq!(
        Catalogue::new(Locale::English)
            .unwrap()
            .format(message)
            .unwrap(),
        "This binding needs a value of type `Bool`, but its initializer has type `Int`."
    );
    assert_eq!(
        Catalogue::new(Locale::Bulgarian)
            .unwrap()
            .format(message)
            .unwrap(),
        "Тази променлива изисква стойност от тип `Bool`, но началният израз има тип `Int`."
    );
}

#[test]
fn label_messages_use_the_same_formatter_without_renderer_mappings() {
    for (message, expected) in [
        (
            Message::Initializer { found: "Int" },
            "This initializer has type `Int`.",
        ),
        (
            Message::BindingAnnotation { expected: "Bool" },
            "This annotation requires type `Bool`.",
        ),
    ] {
        assert_eq!(
            Catalogue::new(Locale::English)
                .unwrap()
                .format(message)
                .unwrap(),
            expected
        );
    }
}

#[test]
fn locale_names_normalize_and_fall_back_without_affecting_ash_spellings() {
    for name in ["bg", "bg-BG", "bg_BG.UTF-8"] {
        assert_eq!(Locale::from_name(name), Locale::Bulgarian);
    }
    for name in ["", "C", "POSIX", "C.UTF-8", "en-GB", "zz", "not a locale"] {
        assert_eq!(Locale::from_name(name), Locale::English);
    }
    let value = "Модул.Type<A -> B>";
    let text = Catalogue::new(Locale::Bulgarian)
        .unwrap()
        .format(Message::Initializer { found: value })
        .unwrap();
    assert!(text.contains(value));
}
