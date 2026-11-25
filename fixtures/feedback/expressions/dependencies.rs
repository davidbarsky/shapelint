thread_local! {
    static REQUEST_CONTEXT: std::cell::RefCell<Option<u8>> = const { std::cell::RefCell::new(None) };
}

tokio::task_local! {
    static TASK_CONTEXT: u8;
}

static mut GLOBAL_STATE: u8 = 0;
static CONTEXT: std::sync::OnceLock<u8> = std::sync::OnceLock::new();
static IMMUTABLE_VALUE: u8 = 0;
