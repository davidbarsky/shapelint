fn from_row(row: Row) -> Message {
    Message { payload: row.payload }
}

fn packet_to_frame(packet: Packet) -> Result<Frame, Error> {
    Frame::try_new(packet.header, packet.payload)
}

impl Name {
    fn as_str(&self) -> &str { &self.0 }
    fn into_message(self) -> Message { Message { name: self.0 } }
    fn from_iter(items: impl IntoIterator<Item = Entry>) -> Self {
        Self { entries: items.into_iter().collect() }
    }
}

impl From<Row> for Message {
    fn from(row: Row) -> Self { Self { payload: row.payload } }
}

fn from_environment() -> Result<Settings, Error> {
    Settings::read(std::env::vars())
}

fn encode_and_send(socket: &mut Socket, message: &Message) -> Result<(), Error> {
    socket.send(message)
}
