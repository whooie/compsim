#![allow(dead_code)]

use std::{
    fs::File,
    io::Read,
    path::PathBuf,
};
use clap::Parser;
use compsim::turing::*;

#[derive(Parser, Debug)]
#[command(author = "Will Huie")]
#[command(version = "alpha 0.1.0")]
#[command(about = "Turing machine simulator")]
#[command(long_about = None)]
struct A {
    /// Run a file as a script. Overridden by `-c`.
    file: Option<PathBuf>,

    /// Program passed as a string.
    #[arg(short, long)]
    command: Option<String>,

    /// Silence live output from the program, instead printing all output at the
    /// end.
    #[arg(short, long)]
    quiet: bool,
}

fn main() -> anyhow::Result<()> {
    let A { file, command, quiet } = A::parse();

    if let Some(command) = command {
        let mut sim = Turing::default();
        let prog = parse(command.chars())?;
        let out = sim.run(&prog, !quiet)?;
        if quiet {
            out.into_iter().for_each(|o| { print!("{}", o); });
            println!();
        }
    } else if let Some(infile) = file {
        let mut file = File::open(infile)?;
        let mut command = String::new();
        file.read_to_string(&mut command)?;
        let mut sim = Turing::default();
        let prog = parse(command.chars())?;
        let out = sim.run(&prog, !quiet)?;
        if quiet {
            out.into_iter().for_each(|o| { print!("{}", o); });
            println!();
        }
    } else {
        println!(
            "No input. Provide a filename or a raw program string with \
            `-c`, or try `--help`."
        );
    }
    Ok(())
}

