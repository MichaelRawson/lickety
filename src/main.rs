mod builder;
mod nf;
mod sat;
mod search;
mod splitter;
mod syntax;
mod tptp;
mod unify;
mod util;

use anyhow::Context;
use clap::Parser;
use std::io::{stdout, Write};
use std::path::PathBuf;
use std::process::exit;
use std::thread;
use std::time::Duration;

#[derive(Parser)]
#[clap(author, version, about)]
struct Options {
    path: PathBuf,
    #[clap(short, long, default_value_t = 10)]
    time: u64,
    #[clap(long)]
    dump_nf: bool,
}

impl Options {
    fn problem_name(&self) -> &str {
        self.path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .unwrap_or_default()
    }

    fn launch_timeout_thread(&self) {
        let time = self.time;
        let name = self.problem_name().to_owned();
        thread::spawn(move || {
            thread::sleep(Duration::from_secs(time));
            let stdout = stdout();
            let mut lock = stdout.lock();
            writeln!(lock, "% SZS status TimeOut for {}", name)
                .map_err(anyhow::Error::new)
                .context("printing timeout message")
                .unwrap();
            std::mem::forget(lock);
            exit(1);
        });
    }
}

fn main() -> anyhow::Result<()> {
    let opts = Options::parse();
    opts.launch_timeout_thread();

    let matrix = tptp::load(&opts.path)?;
    if opts.dump_nf {
        println!("{}", matrix);
        exit(0);
    }

    if search::go(&matrix) {
        println!("% SZS status Theorem for {}", opts.problem_name());
        exit(0)
    }

    Ok(())
}
