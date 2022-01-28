mod builder;
mod nf;
mod search;
mod splitter;
mod syntax;
mod tptp;
mod unify;
mod util;

use clap::Parser;
use std::path::PathBuf;

#[derive(Parser)]
#[clap(author, version, about)]
struct Options {
    path: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let opts = Options::parse();
    let matrix = tptp::load(&opts.path)?;
    search::go(&matrix);
    Ok(())
}
