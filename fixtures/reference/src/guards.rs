fn checked(bytes: &[u8], index: usize) -> u8 {
    if index < bytes.len() { bytes[index] } else { 0 }
}

pub fn established(bytes: &[u8], index: usize) -> Option<u8> {
    if index < bytes.len() {
        Some(checked(bytes, index))
    } else {
        None
    }
}

pub fn unknown(bytes: &[u8], index: usize) -> u8 {
    checked(bytes, index)
}
