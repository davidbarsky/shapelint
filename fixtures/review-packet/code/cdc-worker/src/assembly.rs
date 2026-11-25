use std::sync::Arc;

impl AssemblySession {
    /// Confirms every output before advancing the source offset and attribution together.
    pub async fn handle_batch(
        &mut self,
        records: &[Record<'_>],
        producer: &Producer,
        destination: &str,
        topic_prefix: Option<&TopicPrefix>,
    ) -> Result<(), AssemblyError> {
        let mut assembler = self.assembler.clone();
        let mut next_offset = self.next_offset;
        let mut deliveries = Vec::with_capacity(records.len());
        for record in records {
            if record.topic != self.source
                || record.partition != PARTITION
                || record.offset != next_offset
            {
                return Err(AssemblyError::Record(
                    "topic, partition, or offset differs from the owned source",
                ));
            }
            let assembled = assembler.apply(record.key, record.value)?;
            deliveries.push(assembled); // [reconstructed]
            next_offset += 1; // [reconstructed]
        }
        Ok(()) // [reconstructed]
    }
}

pub async fn open(config: &AssemblyConfig) -> Result<AssemblySession, AssemblyError> { // [reconstructed]
    let consumer: StreamConsumer = ClientConfig::new()
        .set("bootstrap.servers", config.brokers.join(","))
        .set("group.id", &config.group_id)
        .set("enable.auto.commit", "false")
        .set("enable.auto.offset.store", "false")
        .set("auto.offset.reset", "error")
        .create()?;
    let consumer = Arc::new(consumer);
    let (low, high) = tokio::task::spawn_blocking({
        let consumer = Arc::clone(&consumer);
        let source = config.source.clone();
        move || {
            let metadata = consumer.fetch_metadata(Some(&source), METADATA_TIMEOUT)?;
            let [topic] = metadata.topics() else {
                return Err(AssemblyError::Partitions);
            };
            if topic.name() != source || topic.partitions().len() != 1 {
                return Err(AssemblyError::Partitions);
            }
            Ok::<_, AssemblyError>(consumer.fetch_watermarks(
                &source,
                0,
                METADATA_TIMEOUT,
            )?) // [reconstructed]
        }
    })
    .await??; // [reconstructed]
    todo!() // [reconstructed]
}
