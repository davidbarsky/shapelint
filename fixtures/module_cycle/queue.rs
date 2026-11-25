pub(crate) struct Queue;

impl Queue {
    pub(crate) fn push(_: crate::api::Packet, _: crate::trace::Marker) {}
}

mod buffers {
    pub(crate) mod reader {
        pub(crate) struct Cursor;
        pub(crate) fn read(_: super::writer::Slot) {}
    }

    pub(crate) mod writer {
        pub(crate) struct Slot;
        pub(crate) fn write(_: super::reader::Cursor) {}
    }
}
