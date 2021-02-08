mod concrete_analysis;
mod symbolic_analysis;
mod utils;

use clap::{App, Arg};

use std::fs;
use std::process::exit;

use crate::concrete_analysis::concrete_analysis;
use crate::symbolic_analysis::symbolic_and_concolic_analysis;

use rtlola_frontend::{parse, FrontendConfig, RTLolaIR};

/// enum to represent the norm with which the variation of the streams should be analyzed
pub enum LNorm {
  /// Manhattan norm, every input stream can vary by epsilon
  L1,
  /// Chebyshev norm, all input streams together can vary by epsilon
  LInf,
}

/// exits program with error message
/// * `msg` - error message which should be printed
fn exit_error(msg: &str) -> ! {
  eprintln!("Error occurred! {}", msg);
  exit(1);
}

/// read content of a file, returns content as string
/// * `filename` - path to file which should be read
fn read_file(filename: String) -> String {
  let content = fs::read_to_string(filename);
  if content.is_err() {
    exit_error("Reading file was not possible.");
  }
  content.unwrap()
}

/// parse specification as string into RTLolaIR
/// * `filename` - path to file which should be read
/// * `spec` - string with specification which should be parsed
fn parse_ir(filename: String, spec: String) -> RTLolaIR {
  let lola_ir = parse(filename.as_str(), spec.as_str(), FrontendConfig::default());
  if lola_ir.is_err() {
    exit_error(&*format!("Specification was not correct: {}", lola_ir.unwrap_err()));
  }
  lola_ir.unwrap()
}

/// parse input arguments
fn parse_args() -> (String, i32, Option<u16>, Option<LNorm>, bool, bool) {
  let matches = App::new("Robustness Analysis of RTLola Specifications")
        .version("1.0")
        .author("Jessica Schmidt <schmidt-jessica@stud.uni-saarland.de>")
        .about("Bachelor's Thesis")
        // epsilon value
        .arg(Arg::new("epsilon")
            .short('e')
            .long("epsilon")
            .value_name("UINT")
            .about("epsilon value which the allowed variations of the input streams")
            .takes_value(true))
        // eval depth
        .arg(Arg::new("iteration")
            .short('i')
            .long("iteration")
            .value_name("INT")
            .about("depth to which streams should be calculated")
            .takes_value(true)
            .required(true))
        // specification file, default: default.conf
        .arg(Arg::new("file")
            .short('f')
            .long("file")
            .value_name("FILE")
            .about("file with specification to analyse")
            .takes_value(true)
            .required(true))
  // symbolic analysis (default: concrete analysis)
        .arg(Arg::new("symbolic")
            .short('s')
            .long("symbolic")
            .about("symbolic analysis")
            .takes_value(false))
        .arg(Arg::new("lnorm")
            .short('l')
            .long("lnorm")
            .value_name("UINT")
            .about("norm to use (1: L1 norm, 0: L-inf norm)")
            .takes_value(true))
        .arg(Arg::new("z3")
            .short('z')
            .long("z3")
            .about("excute z3")
            .takes_value(false))
        .get_matches();

  // can directly unwrap because required value
  let spec = matches.value_of("file").unwrap().to_string();
  let iteration_res = matches.value_of("iteration").unwrap().to_string().parse::<i32>();
  if iteration_res.is_err() {
    exit_error(format!("Invalid iteration format ({}), expected unsigned int.", iteration_res.unwrap_err()).as_str());
  }

  let iteration = iteration_res.unwrap();
  let symbolic = matches.is_present("symbolic");
  let z3 = matches.is_present("z3");
  let epsilon_val;
  let lnorm_val;
  if symbolic {
    epsilon_val = None;
    lnorm_val = None;
  } else {
    let epsilon = matches.value_of("epsilon");
    if epsilon.is_some() {
      let epsilon_res = epsilon.unwrap().to_string().parse::<u16>();
      if epsilon_res.is_err() {
        exit_error(format!("Invalid epsilon format ({}), expected unsigned int.", epsilon_res.unwrap_err()).as_str());
      } else {
        epsilon_val = Some(epsilon_res.unwrap());
      }
    } else {
      exit_error("epsilon required to find an example!");
    }
    let lnorm = matches.value_of("lnorm");
    if lnorm.is_some() {
      let lnorm_res = lnorm.unwrap().to_string().parse::<u16>();
      if lnorm_res.is_err() {
        exit_error(format!("Invalid LNorm format ({}), expected unsigned int", lnorm_res.unwrap_err()).as_str());
      } else {
        let lnorm_unwrap = lnorm_res.unwrap();
        lnorm_val = match lnorm_unwrap {
          0 => Some(LNorm::LInf),
          1 => Some(LNorm::L1),
          _ => exit_error(format!("Unknown norm {}", lnorm_unwrap).as_str()),
        }
      }
    } else {
      exit_error("No LNorm given for concrete analysis.");
    }
  }
  (spec, iteration - 1, epsilon_val, lnorm_val, symbolic, z3)
}

fn main() {
  let (filename, iteration, epsilon, lnorm, symbolic, z3) = parse_args();
  let spec = read_file(filename.clone());
  let lola_ir = parse_ir(filename, spec);
  if symbolic {
    println!("Analyze specification to find general variations of the output streams ...");
    symbolic_and_concolic_analysis(&lola_ir, iteration);
  } else {
    assert!(lnorm.is_some());
    assert!(epsilon.is_some());
    println!("Find an example where the input streams vary by Ɛ = {} while maximizing the variations of the output streams ...", epsilon.unwrap());
    concrete_analysis(&lola_ir, iteration, epsilon.unwrap(), lnorm.unwrap(), z3);
  }
}
