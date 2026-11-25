mod outer {
    pub trait Clock {
        fn run(&self);
    }

    mod child {
        struct Worker;

        impl super::Clock for Worker {
            fn run(&self) {}
        }
    }
}
