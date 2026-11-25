#[deprecated(note = "use send")]
fn old_send(message: Message) -> Receipt { send(message) }

fn send_compat(message: Message) -> Receipt { send(message) }

#[deprecated]
fn old_notify(message: Message) { notify(message); }

fn legacy_checksum(bytes: &[u8]) -> u8 {
    bytes.iter().fold(0, |acc, byte| acc ^ byte)
}

#[deprecated]
type LegacyMessage = Message;

#[derive(Deserialize)]
struct Message {
    #[serde(alias = "old_payload")]
    payload: String,
    #[serde(rename = "wire_name")]
    name: String,
}

fn legacy_decode(bytes: &[u8]) -> Message {
    let header = Header::parse(bytes);
    match header.version { Version::One => decode_v1(bytes), Version::Two => decode_v2(bytes) }
}

// shapelint: allow(compatibility-scaffolding) Deployed v1 clients still call this endpoint.
#[deprecated]
fn supported_compat(message: Message) -> Receipt { send(message) }
