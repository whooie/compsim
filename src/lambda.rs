use std::{
    fs::File,
    io::Read,
    path::PathBuf,
};
use clap::Parser;
use compsim::church::*;

#[derive(Parser, Debug)]
#[command(author = "Will Huie")]
#[command(version = "alpha 0.1.0")]
#[command(about = "Performs β-reduction on λ-terms")]
#[command(long_about = None)]
struct A {
    /// Evaluate the contents of a file. Overridden by `-c`.
    file: Option<PathBuf>,

    /// Pass an expression as a string.
    #[arg(short, long)]
    command: Option<String>,
}

fn main() -> anyhow::Result<()> {
    let A { file, command } = A::parse();

    if let Some(command) = command {
        let mut term: Lambda = command.parse()?;
        term.reduce();
        println!("{}", term);
    } else if let Some(infile) = file {
        let mut file = File::open(infile)?;
        let mut command = String::new();
        file.read_to_string(&mut command)?;
        let mut term: Lambda = command.parse()?;
        term.reduce();
        println!("{}", term);
    } else {
        println!(
            "No input. Provide a filename or a raw expression string with \
            `-c`, or try `--help`."
        );
    }
    Ok(())
}

