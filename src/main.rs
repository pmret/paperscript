use std::error::Error;
use std::fs::File;
use std::io::Write;

use clap::Clap;
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};
use paperscript::api::Api;

#[derive(Clap)]
#[clap()]
struct Opts {
    #[clap(subcommand)]
    command: Command,
}

#[derive(Clap)]
enum Command {
    Compile {
        input: String,

        #[clap(short, long)]
        output: Option<String>,

        #[clap(short, long)]
        api: Option<Vec<String>>,
    },

    ApiToHeader {
        api: Vec<String>,
    },
}

fn main() {
    let opts: Opts = Opts::parse();

    if let Err(error) = try_main(opts) {
        print_error(error);
        std::process::exit(1);
    }
}

fn try_main(opts: Opts) -> Result<(), Box<dyn Error>> {
    match opts.command {
        Command::Compile { input, output, api } => {
            let input = std::fs::read_to_string(input)?;
            let api = load_api_paths(api)?;

            if let Some(output) = output {
                let mut output = File::create(output)?;
                paperscript::compile(&input, &mut output, &api, &mut print_warning)?;
            } else {
                let mut output = std::io::stdout();
                paperscript::compile(&input, &mut output, &api, &mut print_warning)?;
            }
        }

        Command::ApiToHeader { api } => {
            let api = load_api_paths(Some(api))?;

            println!("#ifndef _PAPERSCRIPT_API_H_");
            println!("#define _PAPERSCRIPT_API_H_");
            println!("");
            println!("#include \"common.h\"");
            println!("");

            for (name, desc) in &api.functions {
                if desc.namespace {
                    println!("#ifdef NAMESPACE");
                    println!("ApiStatus N({})(ScriptInstance* script, s32 isInitialCall);", name);
                    println!("#endif");
                } else {
                    println!("ApiStatus {}(ScriptInstance* script, s32 isInitialCall);", name);
                }
            }

            for (name, desc) in &api.scripts {
                if desc.namespace {
                    println!("#ifdef NAMESPACE");
                    println!("extern Bytecode N({})[];", name);
                    println!("#endif");
                } else {
                    println!("extern Bytecode {}[];", name);
                }
            }

            println!("");
            println!("#endif");
        }
    }

    Ok(())
}

fn load_api_paths(api_paths: Option<Vec<String>>) -> Result<Api, std::io::Error> {
    if let Some(api_paths) = api_paths {
        let mut api = Api::default();

        for path in api_paths {
            let config = std::fs::read_to_string(path)?;
            api.union(toml::from_str(&config)?);
        }

        Ok(api)
    } else {
        Ok(Api::default())
    }
}

fn print_error(error: Box<dyn Error>) {
    let mut stderr = StandardStream::stderr(ColorChoice::Auto);
    let _ = stderr.set_color(ColorSpec::new().set_fg(Some(Color::Red)).set_bold(true));
    let _ = write!(&mut stderr, "error:");
    let _ = stderr.set_color(ColorSpec::new().set_reset(true));
    let _ = writeln!(&mut stderr, " {}", error);
}

fn print_warning(warning: paperscript::Warning) {
    let mut stderr = StandardStream::stderr(ColorChoice::Auto);
    let _ = stderr.set_color(ColorSpec::new().set_fg(Some(Color::Yellow)));
    let _ = write!(&mut stderr, "warning:");
    let _ = stderr.set_color(ColorSpec::new().set_reset(true));
    let _ = writeln!(&mut stderr, " {}", warning);
}
