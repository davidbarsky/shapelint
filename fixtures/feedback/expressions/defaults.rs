fn defaults(config: Config) {
    let port = std::env::var("PORT").unwrap_or_default();
    let host = config.host.unwrap_or("localhost");
    let optional = Some(1u8).unwrap_or_default();
    let _ = (port, host, optional);
}
