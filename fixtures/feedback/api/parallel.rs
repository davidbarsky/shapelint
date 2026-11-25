fn send(items: &[Message]) { transport::send(items); }
fn send_one(item: Message) { transport::send(&[item]); }
fn send_many(items: Vec<Message>) { transport::send(&items); }

struct Store;
impl Store {
    fn open(path: &Path) -> Self { disk::open(path) }
}
impl Store {
    fn open_with_options(path: &Path, options: Options) -> Self { disk::open_options(path, options) }
}

mod independent {
    fn send_one(item: Message) { transport::send(&[item]); }
}

struct Other;
impl Other {
    fn open_v2(path: &Path) -> Self { disk::open(path) }
}

trait Api { fn send(&self); fn send_one(&self); }
