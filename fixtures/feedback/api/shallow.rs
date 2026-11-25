fn forward(value: Message) { transport::send(value); }

fn make(value: u32) -> Record { Record { value } }

impl Record {
    fn value(&self) -> u32 { self.value }
    fn callback_value(&self) -> u32 { self.value }
    fn new(value: u32) -> Self { Self { value } }
    fn try_from_input(value: u32) -> Result<Self, Error> {
        if value == 0 { return Err(Error::Zero); }
        Ok(Self { value })
    }
}

impl From<u32> for Record {
    fn from(value: u32) -> Self { Self { value } }
}

fn totals(records: &[Record]) -> u32 {
    let values = records.iter().map(Record::callback_value);
    values.sum()
}
