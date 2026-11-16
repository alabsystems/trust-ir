//! Test-only original compiler bounded parsing entrypoint (Root54b).
#![allow(dead_code)]
pub const MAX_DEEP_NESTING: usize = 4096;
const DEEP_PARSE_STACK_BYTES: usize = 256 * 1024 * 1024;
fn is_recursion_limit_error(error: &serde_json::Error) -> bool {
    error.classify() == serde_json::error::Category::Syntax
        && error.to_string().contains("recursion limit exceeded")
}

/// Measure the maximum `[`/`{` nesting depth of `json` in one linear scan,
/// ignoring structural characters inside string literals (escape-aware).
#[must_use]

pub fn json_nesting_depth(json: &str) -> usize {
    let mut depth = 0usize;
    let mut max_depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    for byte in json.bytes() {
        if in_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
            }
            continue;
        }
        match byte {
            b'"' => in_string = true,
            b'[' | b'{' => {
                depth += 1;
                max_depth = max_depth.max(depth);
            }
            b']' | b'}' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    max_depth
}

/// `serde_json::from_str` with a bounded deep-recursion fallback.
///
/// See the module docs for the exact bounds and failure behavior.

pub fn from_str_deep<T>(json: &str) -> Result<T, serde_json::Error>
where
    T: serde::de::DeserializeOwned + Send + 'static,
{
    match serde_json::from_str::<T>(json) {
        Ok(value) => Ok(value),
        Err(error)
            if is_recursion_limit_error(&error) && json_nesting_depth(json) <= MAX_DEEP_NESTING =>
        {
            deep_parse_on_dedicated_stack::<T>(json)
                .map_err(|deep_error| deep_error.unwrap_or(error))
        }
        Err(error) => Err(error),
    }
}

/// [`from_str_deep`] over bytes: `serde_json::from_slice`, and on its recursion-limit error
/// the same bounded re-parse (T3 L4, C09d). Bytes that are not UTF-8 keep the original error,
/// as `from_slice` would have refused them anyway.

fn deep_parse_on_dedicated_stack<T>(json: &str) -> Result<T, Option<serde_json::Error>>
where
    T: serde::de::DeserializeOwned + Send + 'static,
{
    let owned = json.to_string();
    let handle = std::thread::Builder::new()
        .name("trust-deep-json".to_string())
        .stack_size(DEEP_PARSE_STACK_BYTES)
        .spawn(move || -> Result<T, serde_json::Error> {
            let mut deserializer = serde_json::Deserializer::from_str(&owned);
            deserializer.disable_recursion_limit();
            let value = T::deserialize(&mut deserializer)?;
            deserializer.end()?;
            Ok(value)
        })
        .map_err(|_| None)?;
    match handle.join() {
        Ok(Ok(value)) => Ok(value),
        Ok(Err(parse_error)) => Err(Some(parse_error)),
        // A panicked parse thread (should be unreachable given the depth bound)
        // degrades to the original error — never poisons the caller.
        Err(_) => Err(None),
    }
}
