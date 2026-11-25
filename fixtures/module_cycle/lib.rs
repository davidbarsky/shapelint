#![allow(dead_code, unused_imports)]

mod queue;
#[path = "wire_format.rs"]
mod wire;

mod api {
    pub(crate) use crate::wire::Packet;
}

mod trace {
    use crate::queue::Queue;

    pub(crate) struct Marker {
        #[cfg(test)]
        queue: Queue,
    }

    pub(crate) fn trace() {
        #[cfg(test)]
        let _: Option<Queue> = None;
    }

    #[cfg(test)]
    fn queue_for_test(_: Queue) {}
}
