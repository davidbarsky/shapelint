fn erase_errors(value: Result<u8, String>, values: Vec<Result<u8, String>>) {
    let _ = value.ok();
    let _ = values.into_iter().filter_map(Result::ok).collect::<Vec<_>>();
    let _ = match value {
        Ok(value) => Some(value),
        Err(_) => {
            None
        },
    };
    let _ = match value {
        Ok(value) => Some(value),
        Err(_) => Default::default(),
    };
    for value in values {
        match value {
            Ok(_) => {}
            Err(_) => continue,
        }
    }

    let _ = match value {
        Ok(value) => Some(value),
        other::Err(_) => None,
        Err(_) => Option::None,
        Err(_named) => None,
        Err(_) => {
            let _note = "default is documented here";
            Some(1)
        }
    };

    let _ = match value {
        Ok(value) => Some(value),
        Err(_) => {
            let value = Default::default();
            Err(Error::Rejected(value))
        }
    };
}
