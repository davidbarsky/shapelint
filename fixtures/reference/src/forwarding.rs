fn byte(bytes: &[u8], index: usize) -> u8 {
    bytes[index]
}

fn relay(bytes: &[u8], index: usize) -> u8 {
    byte(bytes, index)
}

pub fn unchecked(bytes: &[u8], index: usize) -> u8 {
    relay(bytes, index)
}

pub fn guarded(bytes: &[u8], index: usize) -> Option<u8> {
    if index < bytes.len() {
        Some(relay(bytes, index))
    } else {
        None
    }
}

fn reversed(index: usize, bytes: &[u8]) -> u8 {
    byte(bytes, index)
}

pub fn swapped(bytes: &[u8], index: usize) -> u8 {
    reversed(index, bytes)
}

pub enum Route {
    Direct,
    Reversed,
}

pub fn diamond(bytes: &[u8], index: usize, route: Route) -> u8 {
    match route {
        Route::Direct => relay(bytes, index),
        Route::Reversed => reversed(index, bytes),
    }
}
