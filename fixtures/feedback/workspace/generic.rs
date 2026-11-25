pub trait Convert<T> {
    fn convert(&self) -> T;
}

struct Wrapper<T>(T);

impl<T> Convert /* trivia */ <T> for Wrapper<T> {
    fn convert(&self) -> T {
        todo!()
    }
}
