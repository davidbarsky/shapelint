pub fn invalidated(bytes: &mut Vec<u8>, index: usize) -> Option<u8> {
    if index < bytes.len() {
        bytes.clear();
        Some(bytes[index])
    } else {
        None
    }
}

pub fn rechecked(bytes: &mut Vec<u8>, index: usize) -> Option<u8> {
    bytes.clear();
    if index < bytes.len() {
        Some(bytes[index])
    } else {
        None
    }
}
