pub mod ast;
pub mod init;
pub mod interpreter;
pub mod parser;

#[cfg(test)]
pub(crate) mod tests {
    use std::sync::Mutex;

    use log::LevelFilter;
    use simplelog::{ColorChoice, Config, TermLogger, TerminalMode};

    pub(crate) fn init_test_log() {
        static INIT: Mutex<bool> = Mutex::new(false);

        let mut guard = INIT.lock().unwrap();
        if !*guard {
            TermLogger::init(
                LevelFilter::Trace,
                Config::default(),
                TerminalMode::Stdout,
                ColorChoice::Auto,
            )
            .unwrap();
            *guard = true;
        }
    }
}
