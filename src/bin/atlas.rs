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
        .init();

    let mut parser = tree_sitter::Parser::new();
    parser
        .set_language(tree_sitter_lua::language())
        .expect("Error loading Lua grammar");

    let mut typechecker = Typechecker::new();

    typechecker.include(&args.file).unwrap();
    let id = FileID::from(&args.file);

    let typ = typechecker
        .type_at_point(id, args.line, args.column)
        .unwrap();
    println!("Type: {typ:?}");
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

    /// File to be typechecked
    #[arg(required = true)]
    file: PathBuf,

    /// Line to typecheck (zero-based)
    #[arg(required = true)]
    line: usize,

    /// Column to typecheck (zero-based)
    #[arg(required = true)]
    column: usize,
}
