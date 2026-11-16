//! Test-only original native260 parsing policy with the shared visitor.
use serde::Deserialize;
use serde_json::Value;
use trust_ir_contract::proof_json::UniqueJsonValue;
pub fn parse(payload: &str) -> Result<Value, String> {
    check_json_nesting(payload).map_err(str::to_owned)?;
    let mut d = serde_json::Deserializer::from_str(payload);
    d.disable_recursion_limit();
    let value = UniqueJsonValue::deserialize(&mut d).map_err(|e| e.to_string())?;
    d.end().map_err(|e| e.to_string())?;
    Ok(value.into_value())
}
fn check_json_nesting(payload: &str) -> Result<(), &'static str> {
    const MAX_JSON_DEPTH: usize = 260;
    let mut depth = 0_usize;
    let mut quoted = false;
    let mut escaped = false;
    for byte in payload.bytes() {
        if quoted {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                quoted = false;
            }
        } else {
            match byte {
                b'"' => quoted = true,
                b'{' | b'[' => {
                    depth = depth.checked_add(1).ok_or("JSON nesting overflow")?;
                    if depth > MAX_JSON_DEPTH {
                        return Err("JSON nesting exceeds native formula depth budget");
                    }
                }
                b'}' | b']' => depth = depth.checked_sub(1).ok_or("unbalanced JSON nesting")?,
                _ => {}
            }
        }
    }
    Ok(())
}
