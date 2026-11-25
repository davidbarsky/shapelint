pub trait Marker {}
pub struct Never;

impl !Marker for Never {}
