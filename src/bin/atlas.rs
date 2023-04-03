use std::path::PathBuf;
use std::str::FromStr;

use clap::builder::TypedValueParser;
use clap::Parser;

use atlas_lua::typecheck::{FileID, Typechecker};

fn main() {
    let args = Args::parse();

    env_logger::Builder::new()
        .filter(None, args.log)
        .format_timestamp(None)
        .parse_write_style(&args.color)
        .init();

    let mut typechecker = Typechecker::new();

    typechecker.include(&args.file).unwrap();

    let id = FileID::from(&args.file);
    let (_tree, chunk) = &typechecker.files[&id];

    log::info!(
        "Chunk closes over the variables: {:?}",
        chunk.free_variables
    );
    log::info!(
        "Chunk assigns the following global variables: {:?}",
        chunk.provided_globals
    );
    log::info!(
        "Chunk possible return types: {}",
        chunk.possible_return_types
    );
}

/// Typechecker for vanilla Lua without annotations
#[derive(clap::Parser, Debug)]
#[command(name = "atlas", version, about, arg_required_else_help = true)]
struct Args {
    /// Logging level
    #[arg(
        long,
        value_name = "LEVEL",
        default_value = "warn",
        value_parser = clap::builder::PossibleValuesParser::new(
                    ["error", "warn", "info", "debug", "trace", "off"])
                .map(|s| log::LevelFilter::from_str(&s).unwrap()),
        )]
    log: log::LevelFilter,

    /// Use colored output in logging
    #[arg(
        long, short,
        default_value = "auto",
        value_parser = clap::builder::PossibleValuesParser::new(
                    ["auto", "always", "never"]),
        )]
    color: String,

    /// File to be typechecked
    #[arg(required = true)]
    file: PathBuf,
}
