use std::collections::HashMap;

use rtlola_frontend::ir::{
  ArithLogOp, Constant, Expression, ExpressionKind, InputStream, Offset, OutputStream, StreamReference,
};
use rtlola_frontend::RTLolaIR;
use z3::ast::{Ast, Int};
use z3::{Config, Context};

use crate::utils::{get_linear_and_recursive_streams, max_memory_bound, sort_per_layer};

/// model which holds all information to execute the symbolic and concolic analysis
struct Model<'l> {
  /// parsed RTLola specification which should be analyzed
  ir: &'l RTLolaIR,
  /// context required for the z3 solver
  ctx: &'l Context,
  /// max memory bound of the specification
  max_mem: i32,
  /// evaluation depth, iteration to which we should analyze the streams
  eval_depth: i32,
  /// map which maps name of the recursive streams to the corresponding z3 formula
  recursive_known: HashMap<String, Int<'l>>,
  /// map which maps name of the linear streams to the corresponding z3 formula
  linear_known: HashMap<String, Int<'l>>,
}

impl<'l> Model<'l> {
  /// returns a unique name for a variable based on iteration and stream name
  /// * `name` - a string that holds the name of the variable
  /// * `iteration` - number of current iteration step
  fn create_name(&self, name: String, iteration: i32) -> String {
    format!("{}[{}]", name, iteration)
  }

  /// returns a unique name for a variable for an input stream based on iteration and stream name
  /// * `stream` - input stream for which the variable should be created
  /// * `iteration` - number of current iteration step
  fn create_name_inputs(&self, stream: &InputStream, iteration: i32) -> String {
    self.create_name(stream.name.clone(), iteration)
  }

  /// returns a unique name for a variable for an output stream based on iteration and stream name
  /// * `stream` - output stream for which the variable should be created
  /// * `iteration` - number of current iteration step
  fn create_name_outputs(&self, stream: &OutputStream, iteration: i32) -> String {
    let mut name = stream.name.clone();
    if name == "trigger" {
      // append output reference because name trigger is not unique if several triggers exist
      let reference = &stream.reference;
      if let StreamReference::OutRef(u) = reference {
        name = format!("{}{}", name, u);
      }
    }
    self.create_name(name, iteration)
  }

  /// returns a new z3 variable of type int which varies by epsilon
  /// * `stream` - stream for which the variable should be created
  /// * `iteration` - number of current iteration step
  fn epsilon_variable(&self, stream: &InputStream, iteration: i32) -> Int<'l> {
    let epsilon = Int::new_const(self.ctx, "Ɛ");
    let input = Int::new_const(self.ctx, self.create_name_inputs(&stream, iteration));
    Int::add(&self.ctx, &vec![&epsilon, &input])
  }

  /// returns true if operator is handled like a sum
  /// (note, that or, eq, lt, le, ne, ge, gt ar also handled like sum)
  /// * `operator` - operator which should be checked
  fn is_add_operation(&self, operator: &ArithLogOp) -> bool {
    match operator {
      ArithLogOp::Add
      | ArithLogOp::Or
      | ArithLogOp::Eq
      | ArithLogOp::Lt
      | ArithLogOp::Le
      | ArithLogOp::Ne
      | ArithLogOp::Ge
      | ArithLogOp::Gt => true,
      _ => false,
    }
  }

  /// performs a binary operation on two z3 ints and returns the new formula
  /// * `operator` - the operator which should be executed
  /// * `left` - the left operand
  /// * `right` - the right operand
  fn binary_int_operation(&self, operator: &ArithLogOp, left: Int<'l>, right: Int<'l>) -> Int<'l> {
    let vals = &vec![&left, &right];
    if self.is_add_operation(operator) {
      Int::add(&self.ctx, vals)
    } else {
      match operator {
        ArithLogOp::Sub => Int::sub(&self.ctx, vals),
        ArithLogOp::Mul => Int::mul(&self.ctx, vals),
        ArithLogOp::Div => left.div(&right),
        ArithLogOp::Rem => left.rem(&right),
        ArithLogOp::Pow => left.power(&right),
        ArithLogOp::BitXor => todo!("binary operation: BitXor"),
        ArithLogOp::BitAnd => todo!("binary operation: BitAnd"),
        ArithLogOp::BitOr => todo!("binary operation: BitOr"),
        ArithLogOp::BitNot => todo!("binary operation: BitNot"),
        ArithLogOp::Shl => todo!("binary operation: Shl"),
        ArithLogOp::Shr => todo!("binary operation: Shr"),
        _ => panic!("binary operation: unexpected binary operation {:?}", operator),
      }
    }
  }

  /// performs a binary operation on two expressions and returns the new z3 formula
  /// * `operator` - the operator which should be executed
  /// * `left_expr` - the expression of the left operand
  /// * `right_expr` - the expression of the right operand
  /// * `iteration` - number of current iteration step
  fn binary_operation(
    &self,
    operator: &ArithLogOp,
    left_expr: &Expression,
    right_expr: &Expression,
    iteration: i32,
  ) -> Int<'l> {
    assert!(iteration >= 0, "binary operation: iteration was negative ({})", iteration);
    let left_operand;
    let right_operand;
    left_operand = self.analyze_expression(left_expr, iteration);
    right_operand = self.analyze_expression(right_expr, iteration);
    self.binary_int_operation(operator, left_operand, right_operand)
  }

  /// performs an unary operation on an expression and returns the new z3 formula
  /// * `operator` - the operator which should be executed
  /// * `expr` - the expression of the operand
  /// * `iteration` - number of current iteration step
  fn unary_operation(&self, operator: &ArithLogOp, expr: &Expression, iteration: i32) -> Int<'l> {
    assert!(iteration >= 0, "unary operation: iteration was negative ({})", iteration);
    let operand = self.analyze_expression(expr, iteration);
    match operator {
      ArithLogOp::Neg => operand.unary_minus(),
      ArithLogOp::Not => todo!("unary operation: Not"),
      ArithLogOp::BitNot => todo!("unary operation: BitNot"),
      _ => panic!("unary operation: unexpected unary operation {:?}", operator),
    }
  }

  /// performs an arithmetic operation on an expression and returns the new z3 formula
  /// * `operator` - the operator which should be executed
  /// * `expr` - vector of the expression of the operands
  /// * `iteration` - number of current iteration step
  fn arithmetic_operation(&self, operator: &ArithLogOp, expr: &Vec<Expression>, iteration: i32) -> Int<'l> {
    assert!(iteration >= 0, "arithmetic operation: iteration was negative ({})", iteration);
    match expr.len() {
      1 => self.unary_operation(operator, &expr[0], iteration),
      2 => self.binary_operation(operator, &expr[0], &expr[1], iteration),
      _ => unreachable!("There are only operators for 1 or 2 operands (not more)"),
    }
  }

  /// converts a constant into a z3 constant
  /// note, that bools are converted to ints (true: 1, false: 0)
  /// * `constant` - the constant to convert
  fn load_constant(&self, c: Constant) -> Int<'l> {
    match c {
      Constant::UInt(t) => Int::from_u64(self.ctx, t),
      Constant::Int(t) => Int::from_i64(self.ctx, t),
      Constant::Bool(b) => {
        if b {
          Int::from_u64(self.ctx, 1)
        } else {
          Int::from_u64(self.ctx, 0)
        }
      }
      _ => panic!("load constant: unsupported type of constant {:?}", c),
    }
  }

  /// converts the offset function called on a stream into the corresponding z3 variable access
  /// returns analyzed lookup and new iteration,
  /// or error if the actual offset is negative (due to the iteration)
  /// to indicate that default case needs to be executed
  /// * `stream_ref` - the stream which is accessed
  /// * `offset` - the offset with which the stream is accessed
  /// * `iteration` - number of current iteration step
  fn offset_lookup(&self, stream_ref: &StreamReference, offset: &Offset, iteration: i32) -> Result<Int<'l>, i32> {
    assert!(iteration >= 0, "offset lookup: iteration was negative ({})", iteration);
    if let Offset::PastDiscreteOffset(o) = offset {
      assert!(*o <= 65535, "PastDiscreteOffset was larger than MAX(u16) (but memory bound is only u16)");
      let val = iteration - (*o as i32);
      if val < 0 {
        Err(val)
      } else {
        match stream_ref {
          StreamReference::InRef(_) => {
            let stream = self.ir.get_in(*stream_ref);
            Ok(self.epsilon_variable(&stream, val))
          }
          StreamReference::OutRef(_) => {
            let stream = self.ir.get_out(*stream_ref);
            let known = self.get_known(&stream, val);
            Ok(known.unwrap().clone())
          }
        }
      }
    } else {
      panic!("offset lookup: unsupported offset {:?}", offset)
    }
  }

  /// converts a stream access into the corresponding z3 variable access
  /// * `stream_ref` - the stream which is accessed
  /// * `iteration` - number of current iteration step
  fn stream_access(&self, stream_ref: &StreamReference, iteration: i32) -> Int<'l> {
    assert!(iteration >= 0, "stream access: iteration was negative ({}_{})", stream_ref, iteration);
    match stream_ref {
      StreamReference::InRef(_) => {
        let stream = self.ir.get_in(*stream_ref);
        self.epsilon_variable(&stream, iteration) // input value varies by epsilon
      }
      StreamReference::OutRef(_) => {
        // check variation of output stream
        let stream = self.ir.get_out(*stream_ref);
        let known = self.get_known(&stream, iteration);
        known.unwrap().clone()
      }
    }
  }

  /// converts the offset function called on a stream into the corresponding z3 variable access
  /// * `stream_expr` - expression of the stream which is accessed
  /// * `default_expr` - expession of the default case which is triggered at out-of-bounds access
  /// * `iteration` - number of current iteration step
  fn stream_default(&self, access: &Expression, default: &Expression, iteration: i32) -> Int<'l> {
    assert!(iteration >= 0, "stream default: iteration was negative ({})", iteration);
    match access.kind {
      ExpressionKind::OffsetLookup { target, offset } => {
        let res = self.offset_lookup(&target, &offset, iteration);
        if res.is_err() {
          // lookup negative iteration
          self.analyze_expression(default, iteration)
        } else {
          res.unwrap() // we already called analyze_expression on the access
        }
      }
      _ => panic!("stream default: unsupported left expression {:?}", access),
    }
  }

  /// convert an expression into the corresponding z3 formula
  /// * `expr` - expression which should be converted
  /// * `iteration` - number of current iteration step
  fn analyze_expression(&self, expr: &Expression, iteration: i32) -> Int<'l> {
    match &expr.kind {
      ExpressionKind::ArithLog(operator, e, _) => self.arithmetic_operation(operator, e, iteration),
      ExpressionKind::LoadConstant(c) => self.load_constant(c.clone()),
      ExpressionKind::StreamAccess(stream, _) => self.stream_access(stream, iteration),
      ExpressionKind::Default { expr, default } => self.stream_default(expr, default, iteration),
      ExpressionKind::Ite { .. } => panic!("can not symbolically analyze if then else"),
      ExpressionKind::OffsetLookup { .. } => todo!("analyze expression: offset lookup should be handled by Default"),
      _ => panic!("analyze express: unsupported expression {:?}", expr),
    }
  }

  /// convert an output stream into the corresponding z3 formula
  /// * `stream` - stream which should be converted
  /// * `iteration` - number of current iteration step
  fn analyze_output_stream(&self, stream: &OutputStream, iteration: i32) -> Int<'l> {
    assert!(iteration >= 0, "analyze output stream: iteration was negative ({})", iteration);
    self.analyze_expression(&stream.expr, iteration)
  }

  /// concolic analysis: calculate delta as a function of epsilon and the iteration step
  /// * `linear_streams` - linear streams of the specification which are accessed by recursive streams
  /// * `recursive_streams` - recursive streams of the specification
  /// * `lower_bound` - iteration from which we need to analyze the linear streams
  ///                   (as they were not already analyzed by previous symbolic execution)
  pub fn analyze_recursive_model(
    &mut self,
    linear_streams: &Vec<&StreamReference>,
    recursive_streams: &Vec<&StreamReference>,
    lower_bound: i32,
  ) {
    // analyze remaining linear streams accessed while recursion (which were not already analyzed)
    for i in lower_bound..self.eval_depth + 1 {
      for stream_ref in linear_streams {
        let stream = self.ir.get_out(**stream_ref);
        let formula = self.analyze_output_stream(stream, i).simplify();
        self.add_linear_known(stream, formula.clone(), i);
      }
    }
    // analyze recursive streams
    println!("\nrecursive streams:");
    for i in 0..self.eval_depth + 1 {
      for stream_ref in recursive_streams {
        let stream = self.ir.get_out(**stream_ref);
        let formula = self.analyze_output_stream(stream, i).simplify();
        self.add_recursive_known(stream, i, formula.clone());
        println!("\t\t{}[{}] = {:?}", stream.name, i, formula);
      }
    }
  }

  /// symbolic analysis: calculate delta as a function of epsilon
  /// * `linear_streams` - linear streams of the specification which are accessed by recursive streams
  pub fn analyze_linear_model(&mut self, linear_streams: &Vec<&StreamReference>) {
    // analyze base cases of linear streams
    println!("\nlinear streams:\n\tbase cases:");
    for i in 0..self.max_mem {
      for stream_ref in linear_streams {
        let stream = self.ir.get_out(**stream_ref);
        let formula = self.analyze_output_stream(stream, i).simplify();
        self.add_linear_known(stream, formula.clone(), i);
        let name = self.create_name_outputs(&stream, i);
        println!("\t\t{} = {:?}", name, formula);
      }
    }
    // analyze general cases of linear streams
    println!("\tgeneral cases: (n >= {}, interpret s[c] as s[n+c])", self.max_mem - 1);
    for stream_ref in linear_streams {
      let stream = self.ir.get_out(**stream_ref);
      let formula = self.analyze_output_stream(stream, self.max_mem).simplify();
      self.add_linear_known(&stream, formula.clone(), self.max_mem);
      let name = self.create_name_outputs(&stream, self.max_mem);
      println!("\t\t{} = {:?}", name, formula);
    }
  }

  /// perform symbolic analysis on linear streams
  /// and afterwards concolic analysis on recursive streams
  /// * `linear_streams` - linear streams of the specification which are accessed by recursive streams
  /// * `recursive_streams` - recursive streams of the specification
  pub fn analyze_model(&mut self, linear_streams: &Vec<&StreamReference>, recursive_streams: &Vec<&StreamReference>) {
    // recursive streams can depend on linear streams, but not the other way around
    // -> linear streams need to be analyzed first
    if linear_streams.is_empty() {
      self.analyze_recursive_model(linear_streams, recursive_streams, 0);
    } else {
      self.analyze_linear_model(linear_streams);
      if !recursive_streams.is_empty() {
        self.analyze_recursive_model(linear_streams, recursive_streams, self.max_mem + 1);
      }
    }
  }

  /// add recursive output stream to map of already analyzed recursive streams
  /// * `stream` - output stream which should be added
  /// * `iteration` - number of current iteration step
  /// * `formula` - z3 formula which represents stream
  fn add_recursive_known(&mut self, stream: &OutputStream, iteration: i32, formula: Int<'l>) {
    let name = self.create_name_outputs(stream, iteration);
    self.recursive_known.insert(name, formula);
  }

  /// add linear output stream to map of already analyzed linear streams
  /// * `stream` - output stream which should be added
  /// * `iteration` - number of current iteration step
  /// * `formula` - z3 formula which represents stream
  fn add_linear_known(&mut self, stream: &OutputStream, formula: Int<'l>, iteration: i32) {
    let name = self.create_name_outputs(stream, iteration);
    self.linear_known.insert(name, formula.clone());
  }

  /// get z3 formula of stream which was already analyzed (and hence added to map)
  /// * `stream` - output stream which should be added
  /// * `iteration` - number of current iteration step
  fn get_known(&self, stream: &OutputStream, iteration: i32) -> Option<&Int<'l>> {
    let mut known;
    known = self.get_linear_known(stream, iteration);
    if known.is_none() {
      known = self.get_recursive_known(stream, iteration);
    }
    let name = self.create_name_outputs(stream, iteration);
    assert!(known.is_some(), "get known: every previous stream should already be analyzed (accessed: {})", name,);
    known
  }

  /// get z3 formula of recursive stream which was already analyzed (and hence added to recursive map)
  /// * `stream` - output stream which should be added
  /// * `iteration` - number of current iteration step
  fn get_recursive_known(&self, stream: &OutputStream, iteration: i32) -> Option<&Int<'l>> {
    let name = self.create_name_outputs(stream, iteration);
    self.recursive_known.get(&name)
  }

  /// get z3 formula of linear stream which was already analyzed (and hence added to linear map)
  /// * `stream` - output stream which should be added
  /// * `iteration` - number of current iteration step
  fn get_linear_known(&self, stream: &OutputStream, iteration: i32) -> Option<&Int<'l>> {
    let name = self.create_name_outputs(stream, iteration);
    self.linear_known.get(&name)
  }
}

/// perform a concrete robustness analysis on an RTLola specification
/// * `ir` - the RTLolaIR of the specification which should be analyzed
/// * `iteration` - the number of iterations which should be executed
///                (note, that at least max_mem iterations are executed)
pub fn symbolic_and_concolic_analysis(ir: &RTLolaIR, iteration: i32) {
  let z3_ctx = Context::new(&Config::new());
  let eval_depth;
  let memory = max_memory_bound(ir) as i32;
  if memory > iteration {
    println!(
      "Need to evaluate at least {}, continue with {} instead of {} ...\n",
      memory + 1,
      memory + 1,
      iteration + 1
    );
    eval_depth = memory;
  } else {
    println!("Evaluate {} iterations ...\n", iteration + 1);
    eval_depth = iteration;
  }

  let (linear_streams, recursive_streams) = get_linear_and_recursive_streams(ir);

  let len = ir.outputs.len();
  let lin_streams_sorted = sort_per_layer(&linear_streams, len, ir);
  let rec_streams_sorted = sort_per_layer(&recursive_streams, len, ir);

  let mut model = Model {
    ir: &ir,
    ctx: &z3_ctx,
    max_mem: memory,
    eval_depth,
    recursive_known: HashMap::new(),
    linear_known: HashMap::new(),
  };
  model.analyze_model(&lin_streams_sorted, &rec_streams_sorted);
}
