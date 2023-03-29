use std::path::PathBuf;
use std::str::FromStr;

use clap::builder::TypedValueParser;
use clap::Parser;

fn main() {
    let args = Args::parse();

    let mut parser = tree_sitter::Parser::new();
    parser
        .set_language(tree_sitter_lua::language())
        .expect("Error loading Lua grammar");

    for file in args.files {
        let contents = std::fs::read_to_string(file).unwrap();
        let tree = parser
            .parse(contents, None)
            .expect("Error parsing Lua code");
        println!("{tree:?}");
    }
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

    /// Files to be typechecked
    #[arg(required = true)]
    files: Vec<PathBuf>,
}
