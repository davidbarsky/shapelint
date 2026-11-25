use std::collections::BTreeMap;

use regex::Regex;
use serde::Deserialize;

#[derive(Debug, Deserialize)] // [reconstructed] header
struct ConnectorConfig {
    prefix: String,
    tables: String,
    messages: Option<String>,
    heartbeat: String,
    #[serde(deserialize_with = "deserialize_bool")]
    transaction_metadata: bool,
    #[serde(default)]
    transforms: Option<String>,
    #[serde(flatten)]
    properties: BTreeMap<String, String>,
}

impl ConnectorConfig {
    fn topics(&self) -> Result<Vec<String>, ConnectorConfigError> {
        let mut topics = self
            .tables
            .split(',')
            .map(str::trim)
            .filter(|table| !table.is_empty())
            .map(|table| format!("{}.{table}", self.prefix))
            .collect::<Vec<_>>();
        if let Some(_) = &self.messages {
            topics.push(format!("{}.message", self.prefix));
        }
        topics.push(self.heartbeat.clone());
        // [reconstructed] transform handling between the two excerpts
        for name in self.transforms.iter().flat_map(|t| t.split(',')) {
            if self.property(name, "type")? != "org.apache.kafka.connect.transforms.RegexRouter" {
                return Err(ConnectorConfigError::UnsupportedTransform);
            }
            let regex = Regex::new(self.property(name, "regex")?)?;
            let replacement = self.property(name, "replacement")?;
            topics = topics
                .into_iter()
                .map(|topic| regex.replace(&topic, replacement).into_owned())
                .collect();
        }
        Ok(topics)
    }

    fn property(&self, transform: &str, property: &str) -> Result<&str, ConnectorConfigError> {
        let key = format!("transforms.{transform}.{property}");
        self.properties
            .get(&key)
            .map(String::as_str)
            .ok_or_else(|| ConnectorConfigError::MissingTransformProperty { key })
    }
}

fn validate_connector_topics(
    config: &ConnectorConfig,
    declared: &[topics::TopicSpec],
) -> Result<(), ConnectorValidationError> {
    for name in config.topics()? {
        if !declared.iter().any(|topic| topic.name == name) {
            return Err(ConnectorValidationError::UndeclaredTopic(name));
        }
    }
    Ok(())
}
