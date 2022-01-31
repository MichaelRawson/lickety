mod builder;
mod nf;
mod search;
mod splitter;
mod syntax;
mod tptp;
mod unify;
mod util;

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
                .expect("failed to print timeout message");
            std::mem::forget(lock);
            exit(1);
        });
    }
}

fn main() -> anyhow::Result<()> {
    let opts = Options::parse();
    opts.launch_timeout_thread();

    let matrix = tptp::load(&opts.path)?;
    if search::go(&matrix) {
        println!("% SZS status Theorem for {}", opts.problem_name());
    }
    Ok(())
}
