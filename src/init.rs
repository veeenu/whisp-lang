use std::{
    fmt::Write,
    fs, io,
    path::{Path, PathBuf},
};

use thiserror::Error;

use crate::interpreter::{self, Interpreter};

#[derive(Debug, Error)]
pub enum Error {
    #[error("parse error")]
    InterpreterError(#[from] interpreter::Error),
    #[error("io")]
    IoError(#[from] io::Error),
}
type Result<T> = std::result::Result<T, Error>;

pub struct WhispInit {
    path: PathBuf,
    interpreter: Interpreter,
}

impl WhispInit {
    pub fn new<P: AsRef<Path>>(script_path: P) -> Result<Self> {
        let path = script_path.as_ref().to_path_buf();
        let script = fs::read_to_string(&path)?;
        let interpreter = Interpreter::new(&script)?;

        Ok(Self { interpreter, path })
    }

    fn aliases(&self) -> Vec<(String, String, String)> {
        let exe = std::env::current_exe().expect("There is no current exe D:");
        let path_str = self.path.display();

        self.interpreter
            .pub_functions()
            .map(|(name, _)| (exe.display().to_string(), path_str.to_string(), name.to_string()))
            .collect()
    }

    pub fn powershell(&self) -> String {
        // Invoke-Expression (& { (zoxide init powershell | Out-String) })
        let mut buf = String::new();
        self.aliases().into_iter().for_each(|(exe, script, name)| {
            writeln!(&mut buf, r#"function {name}() {{ & '{exe}' '{script}' {name} -- @args }}"#)
                .unwrap();
        });

        buf
    }

    pub fn zsh(&self) -> String {
        let mut buf = String::new();
        self.aliases().into_iter().for_each(|(exe, script, name)| {
            writeln!(&mut buf, r#"{name}() {{ "{exe}" "{script}" {name} -- "$@" }}"#).unwrap();
        });

        buf
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    fn project_root() -> PathBuf {
        Path::new(&env!("CARGO_MANIFEST_DIR")).to_path_buf()
    }

    #[test]
    fn test_aliases() {
        let wi = WhispInit::new(project_root().join("examples").join("git_aliases.whisp")).unwrap();
        println!("--- powershell ---\n{}", wi.powershell());
        println!("--- zsh ---\n{}", wi.zsh());
    }
}
