use std::fmt::Write as _;

pub fn quote(value: &str) -> String {
    let mut output = String::with_capacity(value.len() + 2);
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\u{08}' => output.push_str("\\b"),
            '\u{0c}' => output.push_str("\\f"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character <= '\u{1f}' => {
                write!(output, "\\u{:04x}", u32::from(character)).expect("writing to String");
            }
            character => output.push(character),
        }
    }
    output.push('"');
    output
}

pub fn string_array<'a, I>(values: I) -> String
where
    I: IntoIterator<Item = &'a str>,
{
    let mut output = String::from("[");
    for (index, value) in values.into_iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        output.push_str(&quote(value));
    }
    output.push(']');
    output
}

#[cfg(test)]
mod tests {
    use super::{quote, string_array};

    #[test]
    fn json_strings_escape_all_control_boundaries() {
        assert_eq!(quote("a\n\"\\\u{0001}"), "\"a\\n\\\"\\\\\\u0001\"");
        assert_eq!(string_array(["a", "b"]), "[\"a\",\"b\"]");
    }
}
