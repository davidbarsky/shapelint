struct DomainState {
    enabled: bool,
    result: Result<bool, String>,
    values: Vec<bool>,
}

struct TupleState(bool, (bool, u8));

#[repr(C)]
struct FfiState {
    enabled: bool,
}

struct NonStateTypes {
    value: /* bool */ String,
    callback: fn() -> bool,
}

enum DomainChoice {
    Ready(bool),
    Named { enabled: bool },
}

#[derive(Serialize, Deserialize)]
struct WireState {
    enabled: bool,
}

#[doc = "Serialize this state"]
struct DocumentedState {
    enabled: bool,
}

fn domain_state(flag: bool) -> Result<bool, String> {
    let _ = flag;
    todo!()
}

fn callback_type(callback: extern "C" fn(bool) -> bool) {
    let _ = callback;
}

trait FixedSignature {
    fn is_ready(&self) -> bool;
}

extern "C" fn ffi_state(flag: bool) -> bool {
    flag
}
