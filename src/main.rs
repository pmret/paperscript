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

            let api = if let Some(api_paths) = api {
                let mut api = Api::default();

                for path in api_paths {
                    let config = std::fs::read_to_string(path)?;
                    api.union(toml::from_str(&config)?);
                }

                api
            } else {
                Api::default()
            };

            if let Some(output) = output {
                let mut output = File::create(output)?;
                paperscript::compile(&input, &mut output, &api, &mut print_warning)?;
            } else {
                let mut output = std::io::stdout();
                paperscript::compile(&input, &mut output, &api, &mut print_warning)?;
            }
        }
    }

    Ok(())
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
