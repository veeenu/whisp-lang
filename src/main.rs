use std::fs;
use std::path::PathBuf;

use argh::FromArgs;
use whisp::init::WhispInit;
use whisp::interpreter::Interpreter;

#[derive(FromArgs)]
/// Invoke the whisp interpreter.
struct Arguments {
    #[argh(subcommand)]
    subcommand: Subcommand,
}

#[derive(FromArgs)]
#[argh(subcommand)]
enum Subcommand {
    Init(InitSubcommand),
    Run(RunSubcommand),
}

#[derive(FromArgs)]
#[argh(subcommand, name = "init")]
/// Initialize shell aliases.
struct InitSubcommand {
    #[argh(positional)]
    shell_name: String,
    #[argh(positional)]
    script_path: PathBuf,
}

impl InitSubcommand {
    fn run(self) {
        let cmd_string = match self.shell_name.as_str() {
            "zsh" => WhispInit::new(self.script_path).map(|init| init.zsh()),
            "pwsh" | "powershell" => WhispInit::new(self.script_path).map(|init| init.powershell()),
            x => Ok(format!("# whisp: unsupported shell {x}")),
        };

        // TODO ensure the error output doesn't execute commands
        match cmd_string {
            Ok(cmd_string) => println!("{cmd_string}"),
            Err(e) => eprintln!("# whisp: error: {e}"),
        }
    }
}

#[derive(FromArgs)]
#[argh(subcommand, name = "run")]
/// Run whisp function.
struct RunSubcommand {
    #[argh(positional)]
    script_path: PathBuf,
    #[argh(positional)]
    command_name: String,
    #[argh(positional)]
    args: Vec<String>,
}

impl RunSubcommand {
    fn run(self) {
        let script = match fs::read_to_string(&self.script_path) {
            Ok(script) => script,
            Err(e) => {
                eprintln!(r#"Couldn't load script "{}": {e}"#, self.script_path.display());
                return;
            },
        };

        let mut interpreter = match Interpreter::new(&script) {
            Ok(interpreter) => interpreter,
            Err(e) => {
                eprintln!("Interpreter error: {e}");
                return;
            },
        };

        interpreter.call_function(&self.command_name);
    }
}

fn main() {
    let args: Arguments = argh::from_env();

    match args.subcommand {
        Subcommand::Init(init) => init.run(),
        Subcommand::Run(run) => run.run(),
    }
}
