use std::collections::HashMap;
use std::ops::Neg;

use rtlola_frontend::ir::{
  ArithLogOp, Constant, Expression, ExpressionKind, Offset, OutputStream, StreamReference, Trigger, Type,
};
use rtlola_frontend::RTLolaIR;
use z3::ast::{Ast, Bool, Int};
use z3::{Config, Context, Optimize, SatResult};

use crate::utils::{get_accessed_streams, max_memory_bound};
use crate::LNorm;

/// wrapper for z3 types
#[derive(Clone)]
enum Z3Formula<'l> {
  Z3Int(Int<'l>),
  Z3Bool(Bool<'l>),
}

/// model which holds all information to execute the symbolic and concolic analysis
struct Model<'l> {
  /// parsed RTLola specification which should be analyzed
  ir: &'l RTLolaIR,
  /// context required for the z3 solver
  ctx: &'l Context,
  /// epsilon which represents the allowed variation of the input streams
  epsilon: u16,
  /// evaluation depth, iteration to which we should analyze the streams
  eval_depth: i32,
  /// norm under which the variation should be analyzed
  lnorm: LNorm,
  /// flag to indicate whether we are currently building true or false condition
  is_true: bool,
}

impl<'l> Model<'l> {
  /// returns a unique name for a variable based on iteration, stream name and condition
  /// * `name` - a string that holds the name of the variable
  /// * `iteration` - number of current iteration step
  /// * `is_true` - flag which is true if we are currently building the true condition
  ///               and false if we are building the false condition
  fn create_name(&self, name: &String, iteration: i32, is_true: bool) -> String {
    assert!(iteration >= 0, "create name: iteration was negative ({})", iteration);
    assert_ne!(name, "trigger");
    if is_true {
      format!("T_{}[{}]", name, iteration)
    } else {
      format!("F_{}[{}]", name, iteration)
    }
  }

  /// returns a new z3 variable of type int
  /// * `name` - a string that holds the name of the variable
  /// * `iteration` - number of current iteration step
  /// * `is_true` - flag which is true if we are currently building the true condition
  ///               and false if we are building the false condition
  fn int_variable(&self, name: String, iteration: i32, is_true: bool) -> Int<'l> {
    assert!(iteration >= 0, "int variable: iteration was negative ({})", iteration);
    Int::new_const(self.ctx, self.create_name(&name, iteration, is_true))
  }

  /// returns a new z3 variable of type bool
  /// * `name` - a string that holds the name of the variable
  /// * `iteration` - number of current iteration step
  /// *  `is_true` - flag which is true if we are currently building the true condition
  ///                and false if we are building the false condition
  fn bool_variable(&self, name: String, iteration: i32, is_true: bool) -> Bool<'l> {
    assert!(iteration >= 0, "bool variable: iteration was negative ({})", iteration);
    Bool::new_const(self.ctx, self.create_name(&name, iteration, is_true))
  }

  /// returns a new z3 variable of the same type as stream
  /// * `stream_ref` - stream for which the variable should be created
  /// * `iteration` - number of current iteration step
  fn variable(&self, stream_ref: &StreamReference, iteration: i32) -> Z3Formula<'l> {
    assert!(iteration >= 0, "variable: iteration was negative ({})", iteration);
    let ty;
    let mut name;
    match stream_ref {
      StreamReference::InRef(_) => {
        let stream = self.ir.get_in(*stream_ref);
        ty = &stream.ty;
        name = stream.name.clone();
      }
      StreamReference::OutRef(u) => {
        let stream = self.ir.get_out(*stream_ref);
        ty = &stream.ty;
        name = stream.name.clone();
        if name == "trigger" {
          name = format!("{}{}", name, u)
        }
      }
    }
    match ty {
      Type::Bool => Z3Formula::Z3Bool(self.bool_variable(name.clone(), iteration, self.is_true)),
      Type::Int(_) | Type::UInt(_) => Z3Formula::Z3Int(self.int_variable(name.clone(), iteration, self.is_true)),
      _ => unimplemented!("unsupported type {} of stream {}", ty, name),
    }
  }

  /// performs a binary operation on two z3 ints and returns the new formula
  /// * `operator` - the operator which should be executed
  /// * `left` - the left operand
  /// * `right` - the right operand
  fn binary_int_operation(&self, operator: &ArithLogOp, left: Int<'l>, right: Int<'l>) -> Z3Formula<'l> {
    let vals = &vec![&left, &right];
    match operator {
      ArithLogOp::Add => Z3Formula::Z3Int(Int::add(&self.ctx, vals)),
      ArithLogOp::Sub => Z3Formula::Z3Int(Int::sub(&self.ctx, vals)),
      ArithLogOp::Mul => Z3Formula::Z3Int(Int::mul(&self.ctx, vals)),
      ArithLogOp::Div => Z3Formula::Z3Int(left.div(&right)),
      ArithLogOp::Rem => Z3Formula::Z3Int(left.rem(&right)),
      ArithLogOp::Pow => Z3Formula::Z3Int(left.power(&right)),
      ArithLogOp::BitXor => todo!("binary operation: BitXor"),
      ArithLogOp::BitAnd => todo!("binary operation: BitAnd"),
      ArithLogOp::BitOr => todo!("binary operation: BitOr"),
      ArithLogOp::BitNot => todo!("binary operation: BitNot"),
      ArithLogOp::Shl => todo!("binary operation: Shl"),
      ArithLogOp::Shr => todo!("binary operation: Shr"),
      ArithLogOp::Eq => Z3Formula::Z3Bool(left._eq(&right)),
      ArithLogOp::Lt => Z3Formula::Z3Bool(left.lt(&right)),
      ArithLogOp::Le => Z3Formula::Z3Bool(left.le(&right)),
      ArithLogOp::Ne => Z3Formula::Z3Bool(left._eq(&right).not()),
      ArithLogOp::Ge => Z3Formula::Z3Bool(left.ge(&right)),
      ArithLogOp::Gt => Z3Formula::Z3Bool(left.gt(&right)),
      _ => panic!("binary int operation: unexpected binary operation {:?}", operator),
    }
  }

  /// performs a binary operation on two z3 bools and returns the new formula
  /// * `operator` - the operator which should be executed
  /// * `left` - the left operand
  /// * `right` - the right operand
  fn binary_bool_operation(&self, operator: &ArithLogOp, left: Bool<'l>, right: Bool<'l>) -> Z3Formula<'l> {
    let vals = &vec![&left, &right];
    match operator {
      ArithLogOp::And => Z3Formula::Z3Bool(Bool::and(self.ctx, vals)),
      ArithLogOp::Or => Z3Formula::Z3Bool(Bool::or(self.ctx, vals)),
      _ => panic!("binary bool operation: unexpected binary operation {:?}", operator),
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
  ) -> Z3Formula<'l> {
    assert!(iteration >= 0, "binary operation: iteration was negative ({})", iteration);
    let left_operand;
    let right_operand;
    left_operand = self.analyze_expression(left_expr, iteration);
    right_operand = self.analyze_expression(right_expr, iteration);
    match (left_operand, right_operand) {
      (Z3Formula::Z3Int(x), Z3Formula::Z3Int(y)) => self.binary_int_operation(operator, x, y),
      (Z3Formula::Z3Bool(x), Z3Formula::Z3Bool(y)) => self.binary_bool_operation(operator, x, y),
      _ => panic!("binary operation: lhs and rhs need same type"),
    }
  }

  /// performs an unary operation on an expression and returns the new z3 formula
  /// * `operator` - the operator which should be executed
  /// * `expr` - the expression of the operand
  /// * `iteration` - number of current iteration step
  fn unary_operation(&self, operator: &ArithLogOp, expr: &Expression, iteration: i32) -> Z3Formula<'l> {
    assert!(iteration >= 0, "binary operation: iteration was negative ({})", iteration);
    let operand = self.analyze_expression(expr, iteration);
    match operator {
      ArithLogOp::Neg => {
        if let Z3Formula::Z3Int(x) = operand {
          Z3Formula::Z3Int(x.neg())
        } else {
          unreachable!("cannot neg bool!")
        }
      }
      ArithLogOp::Not => {
        if let Z3Formula::Z3Bool(x) = operand {
          Z3Formula::Z3Bool(x.not())
        } else {
          unreachable!("cannot not int!")
        }
      }
      ArithLogOp::BitNot => todo!("unary operation: BitNot"),
      _ => panic!("unary operation: unexpected unary operation {:?}", operator),
    }
  }

  /// performs an arithmetic operation on an expression and returns the new z3 formula
  /// * `operator` - the operator which should be executed
  /// * `expr` - vector of the expression of the operands
  /// * `iteration` - number of current iteration step
  fn arithmetic_operation(&self, operator: &ArithLogOp, expr: &Vec<Expression>, iteration: i32) -> Z3Formula<'l> {
    assert!(iteration >= 0, "arithmetic operation: iteration was negative ({})", iteration);
    match expr.len() {
      1 => self.unary_operation(operator, &expr[0], iteration),
      2 => self.binary_operation(operator, &expr[0], &expr[1], iteration),
      _ => unreachable!("There are only operators for 1 or 2 operands (not more)"),
    }
  }

  /// converts a constant into a z3 constant
  /// * `constant` - the constant to convert
  fn load_constant(&self, constant: Constant) -> Z3Formula<'l> {
    match constant {
      Constant::UInt(t) => Z3Formula::Z3Int(Int::from_u64(self.ctx, t)),
      Constant::Int(t) => Z3Formula::Z3Int(Int::from_i64(self.ctx, t)),
      Constant::Bool(b) => Z3Formula::Z3Bool(Bool::from_bool(self.ctx, b)),
      _ => panic!("load constant: unsupported type of constant {:?}", constant),
    }
  }

  /// converts an if-then-else construct into a z3 if-then-else
  /// * `condition_expr` - the expression of the condition
  /// * `consequence_expr` - the expression of the consequence
  /// * `alternative_expr` - the expression of the alternative
  /// * `iteration` - number of current iteration step
  fn if_then_else(
    &self,
    condition_expr: &Expression,
    consequence_expr: &Expression,
    alternative_expr: &Expression,
    iteration: i32,
  ) -> Z3Formula<'l> {
    assert!(iteration >= 0, "if then else: iteration was negative ({})", iteration);
    let condition_formula = self.analyze_expression(condition_expr, iteration);
    let consequence_formula = self.analyze_expression(consequence_expr, iteration);
    let alternative_formula = self.analyze_expression(alternative_expr, iteration);
    if let Z3Formula::Z3Bool(condition) = condition_formula {
      match (consequence_formula, alternative_formula) {
        (Z3Formula::Z3Int(consequence), Z3Formula::Z3Int(alternative)) => {
          Z3Formula::Z3Int(condition.ite(&consequence, &alternative))
        }
        (Z3Formula::Z3Bool(consequence), Z3Formula::Z3Bool(alternative)) => {
          Z3Formula::Z3Bool(condition.ite(&consequence, &alternative))
        }
        _ => unreachable!("consequence and alternative need same type"),
      }
    } else {
      unreachable!("condition is always bool")
    }
  }

  /// converts the offset function called on a stream into the corresponding z3 variable access
  /// returns analyzed lookup and new iteration,
  /// or error if the actual offset is negative (due to the iteration)
  /// to indicate that default case needs to be executed
  /// * `stream_ref` - the stream which is accessed
  /// * `offset` - the offset with which the stream is accessed
  /// * `iteration` - number of current iteration step
  fn offset_lookup(&self, stream_ref: &StreamReference, offset: &Offset, iteration: i32) -> Result<Z3Formula<'l>, i32> {
    assert!(iteration >= 0, "offset lookup: iteration was negative ({})", iteration);
    if let Offset::PastDiscreteOffset(o) = offset {
      assert!(*o <= 65535, "PastDiscreteOffset was larger than MAX(u16) (but memory bound is only u16)");
      let val = iteration - (*o as i32);
      if val < 0 {
        Err(val)
      } else {
        Ok(self.variable(stream_ref, val))
      }
    } else {
      panic!("offset lookup: unsupported offset {:?}", offset)
    }
  }

  /// converts a stream access into the corresponding z3 variable access
  /// * `stream_ref` - the stream which is accessed
  /// * `iteration` - number of current iteration step
  fn stream_access(&self, stream_ref: &StreamReference, iteration: i32) -> Z3Formula<'l> {
    assert!(iteration >= 0, "stream access: iteration was negative ({})", iteration);
    self.variable(stream_ref, iteration)
  }

  /// converts the offset function called on a stream into the corresponding z3 variable access
  /// * `stream_expr` - expression of the stream which is accessed
  /// * `default_expr` - expession of the default case which is triggered at out-of-bounds access
  /// * `iteration` - number of current iteration step
  fn stream_default(&self, stream_expr: &Expression, default_expr: &Expression, iteration: i32) -> Z3Formula<'l> {
    assert!(iteration >= 0, "stream default: iteration was negative ({})", iteration);
    match stream_expr.kind {
      ExpressionKind::OffsetLookup { target, offset } => {
        let res = self.offset_lookup(&target, &offset, iteration);
        if res.is_err() {
          // lookup negative iteration -> execute default case
          self.analyze_expression(default_expr, iteration)
        } else {
          // we already called analyze_expression on the access
          res.unwrap()
        }
      }
      _ => panic!("stream default: unsupported left expression {:?}", stream_expr),
    }
  }

  /// convert an expression into the corresponding z3 formula
  /// * `expr` - expression which should be converted
  /// * `iteration` - number of current iteration step
  fn analyze_expression(&self, expr: &Expression, iteration: i32) -> Z3Formula<'l> {
    match &expr.kind {
      ExpressionKind::ArithLog(operator, e, _) => self.arithmetic_operation(operator, e, iteration),
      ExpressionKind::Ite { condition, consequence, alternative } => {
        self.if_then_else(condition, consequence, alternative, iteration)
      }
      ExpressionKind::LoadConstant(c) => self.load_constant(c.clone()),
      ExpressionKind::StreamAccess(stream, _) => self.stream_access(stream, iteration),
      ExpressionKind::Default { expr, default } => self.stream_default(expr, default, iteration),
      ExpressionKind::OffsetLookup { .. } => {
        unreachable!("analyze expression: offset lookup should be handled by Default")
      }
      _ => panic!("analyze express: unsupported expression {:?}", expr),
    }
  }

  /// convert an output stream into the corresponding z3 formula
  /// * `stream` - stream which should be converted
  /// * `iteration` - number of current iteration step
  fn analyze_output_stream(&self, stream: &OutputStream, iteration: i32) -> Z3Formula<'l> {
    assert!(iteration >= 0, "analyze output stream: iteration was negative ({})", iteration);
    self.analyze_expression(&stream.expr, iteration)
  }

  /// convert a trigger into the corresponding z3 bool formula
  /// * `trigger_ref` - trigger which should be converted
  /// * `streams` - streams on which the trigger depends
  fn analyze_trigger(&mut self, trigger_ref: &Trigger, streams: &Vec<&StreamReference>) -> Bool<'l> {
    let trigger = self.ir.get_out(trigger_ref.reference);
    let mut formula = Bool::from_bool(self.ctx, true);

    // bottom up: for every iteration step evaluate dependency streams
    for i in 0..self.eval_depth + 1 {
      for stream_ref in streams {
        let stream = self.ir.get_out(**stream_ref);
        let res = self.analyze_output_stream(stream, i);
        let var = self.variable(&stream_ref, i);
        let assignment = self.assign(&var, &res);
        formula = self.and(formula, assignment);
      }
      let trigger_constraint = self.analyze_output_stream(trigger, i);
      let trigger_assignment;
      let var = self.variable(&trigger.reference, i);
      if self.is_true {
        trigger_assignment = self.assign(&var, &trigger_constraint);
      } else {
        // assert that last triggers differ (we dont care about the others)
        if i == self.eval_depth {
          trigger_assignment = self.assign(&var, &self.not(&trigger_constraint));
        } else {
          trigger_assignment = self.assign(&var, &trigger_constraint);
        }
      }
      // add part-condition to overall constraint
      formula = self.and(formula, trigger_assignment);
      if i == self.eval_depth {
        if let Z3Formula::Z3Bool(v) = var {
          formula = self.and(formula, v);
        } else {
          panic!("trigger did not have bool type");
        }
      }
    }
    formula
  }

  /// conjunct two z3 bool formulas and return the new formula
  /// * `lhs` - the left operand
  /// * `rhs` - the right operand
  fn and(&self, lhs: Bool<'l>, rhs: Bool<'l>) -> Bool<'l> {
    let param = &vec![&lhs, &rhs];
    Bool::and(self.ctx, param)
  }

  /// negate z3 bool formula and return the new formula
  /// * `operand` - the operand
  fn not(&self, operand: &Z3Formula<'l>) -> Z3Formula<'l> {
    if let Z3Formula::Z3Bool(x) = operand {
      Z3Formula::Z3Bool(x.not())
    } else {
      panic!("cannot not int")
    }
  }

  /// add two z3 int formulas and return the new formula
  /// * `lhs` - the left operand
  /// * `rhs` - the right operand
  fn plus(&self, lhs: Int<'l>, rhs: Int<'l>) -> Int<'l> {
    let vals = &vec![&lhs, &rhs];
    Int::add(self.ctx, vals)
  }

  /// assign two z3 int formulas and return the new formula
  /// * `lhs` - the left operand
  /// * `rhs` - the right operand
  /// (we use equality between lhs and rhs which works like an assignment)
  fn assign(&self, lhs: &Z3Formula<'l>, rhs: &Z3Formula<'l>) -> Bool<'l> {
    match (lhs, rhs) {
      (Z3Formula::Z3Int(x), Z3Formula::Z3Int(y)) => x._eq(&y),
      (Z3Formula::Z3Bool(x), Z3Formula::Z3Bool(y)) => x._eq(&y),
      _ => unreachable!("assign: lhs and rhs need same type"),
    }
  }

  /// build z3 formula that represents the fact that the absolute number
  /// of the difference of two values is less or equal than epsilon
  /// * `lhs` - the left operand
  /// * `rhs` - the right operand
  fn minus_leq_epsilon(&self, lhs: Int<'l>, rhs: Int<'l>) -> Bool<'l> {
    let epsilon = Int::from_u64(self.ctx, self.epsilon as u64);
    let param1 = &vec![&lhs, &rhs];
    let param2 = &vec![&rhs, &lhs];
    let pos1 = Int::sub(self.ctx, param1);
    let pos2 = Int::sub(self.ctx, param2);
    let leq1 = pos1.le(&epsilon);
    let leq2 = pos2.le(&epsilon);
    Bool::and(self.ctx, &vec![&leq1, &leq2]) // need AND to simulate absolute number
  }

  /// check if stream is int type
  /// * `stream_reference` - the stream which should be check
  fn is_int(&self, stream_ref: &StreamReference) -> bool {
    let ty;
    match stream_ref {
      StreamReference::InRef(_) => {
        ty = &self.ir.get_in(*stream_ref).ty;
      }
      StreamReference::OutRef(_) => {
        ty = &self.ir.get_out(*stream_ref).ty;
      }
    }
    match ty {
      Type::Bool => false,
      Type::Int(_) | Type::UInt(_) => true,
      _ => unimplemented!("unsupported type {:?}", ty),
    }
  }

  /// return z3 bool formula which represents input constraint with Linf distance (Chebyshev)
  /// * `inputs` - vector of the input streams  which should be considered
  fn input_constraint_linf(&self, inputs: &Vec<StreamReference>) -> Bool<'l> {
    let mut formula = Bool::from_bool(self.ctx, true);
    for i in 0..self.eval_depth + 1 {
      for stream_ref in inputs {
        if self.is_int(stream_ref) {
          let stream = self.ir.get_in(stream_ref.clone());
          let true_assignment = self.int_variable(stream.name.clone(), i, true);
          let false_assignment = self.int_variable(stream.name.clone(), i, false);
          let assignment = self.minus_leq_epsilon(true_assignment, false_assignment);
          formula = self.and(formula, assignment);
        }
      }
    }
    formula
  }

  fn input_constraint_l1_help(&self, stream_ref: &StreamReference, is_true: bool) -> Int<'l> {
    let mut sum = Int::from_u64(self.ctx, 0);
    for i in 0..self.eval_depth + 1 {
      if self.is_int(stream_ref) {
        let stream = self.ir.get_in(stream_ref.clone());
        let var = self.int_variable(stream.name.clone(), i, is_true);
        sum = self.plus(sum, var);
      }
    }
    sum
  }

  /// return z3 bool formula which represents input constraint with L1 distance (Manhattan)
  /// * `inputs` - vector of the input streams which should be considered
  fn input_constraint_l1(&self, inputs: &Vec<StreamReference>) -> Bool<'l> {
    let mut formula = Bool::from_bool(self.ctx, true);
    for stream_ref in inputs {
      let true_sum = self.input_constraint_l1_help(stream_ref, true);
      let false_sum = self.input_constraint_l1_help(stream_ref, false);
      formula = self.and(formula, self.minus_leq_epsilon(true_sum, false_sum))
    }
    formula
  }

  /// return z3 bool formula which represents input constraint
  /// * `inputs` - vector of the input streams which should be considered
  fn input_constraint(&self, inputs: &Vec<StreamReference>) -> Bool<'l> {
    match self.lnorm {
      LNorm::LInf => self.input_constraint_linf(inputs),
      LNorm::L1 => self.input_constraint_l1(inputs),
    }
  }

  // build z3 bool formula which represents output constraint
  /// * `streams` - vector of the output streams which should be considered
  /// * `z3_optimizer` - z3 optimizer which maximizes the output constraints
  fn output_constraint(&self, outputs: &Vec<&StreamReference>, z3_optimizer: &Optimize) {
    for stream_ref in outputs {
      if self.is_int(stream_ref) {
        let stream = self.ir.get_out(**stream_ref);
        let true_var = self.int_variable(stream.name.clone(), self.eval_depth, true);
        let false_var = self.int_variable(stream.name.clone(), self.eval_depth, false);
        let sub = Int::sub(self.ctx, &vec![&true_var, &false_var]);
        println!("maximize {:?}", sub);
        z3_optimizer.maximize(&sub);
      }
    }
  }

  /// analyze the given specification
  /// * `stream_dependencies` - map which holds the information, on which streams a stream depends
  /// * `z3` - flag which is true if z3 should be executed
  ///          or false if constraint should just be printed printed (needed for testing)
  pub fn analyze_model(&mut self, stream_dependencies: &HashMap<&StreamReference, Vec<&StreamReference>>, z3: bool) {
    for trigger in &self.ir.triggers {
      let z3_optimizer = Optimize::new(&self.ctx);
      let stream = self.ir.get_out(trigger.reference);
      let mut trigger_res = self.input_constraint(&stream.input_dependencies);
      let deps = stream_dependencies.get(&trigger.reference);
      let streams;
      if deps.is_some() {
        streams = deps.unwrap().clone();
      } else {
        streams = Vec::new();
      }
      self.is_true = true;
      let true_formula = self.analyze_trigger(trigger, &streams);
      self.is_true = false;
      let false_formula = self.analyze_trigger(trigger, &streams);
      let formula = self.and(true_formula, false_formula);
      trigger_res = self.and(trigger_res, formula);
      self.output_constraint(&streams, &z3_optimizer);

      // print the calculated formula
      println!("Formula:\n{:?}", trigger_res);

      // execute z3 to solve formula and print result
      if z3 {
        let res = z3_optimizer.check(&vec![trigger_res.simplify()]);
        match res {
          SatResult::Unsat => println!("UNSAT"),
          SatResult::Unknown => println!("Unknown outcome."),
          SatResult::Sat => println!("SAT\n{}", z3_optimizer.get_model().unwrap()),
        }
      }
    }
  }
}

/// perform a concrete robustness analysis on an RTLola specification
/// * `ir` - the RTLolaIR of the specification which should be analyzed
/// * `iteration` - the number of iterations which should be executed
///                (note, that at least max_mem iterations are executed)
/// * `epsilon` - epsilon value which represents the allowed input variation
/// * `lnorm` - lnorm which should be applied as a distance function for input / output constraints
/// * `z3` - flag which is true if z3 should be executed
///          or false if constraint should just be printed printed (needed for testing)
pub fn concrete_analysis(ir: &RTLolaIR, iteration: i32, epsilon: u16, lnorm: LNorm, z3: bool) {
  let z3_ctx = Context::new(&Config::new());
  let eval_depth;
  let memory = max_memory_bound(ir) as i32;
  if memory > iteration {
    println!("Need to evaluate at least {}, continue with {} instead of {} ...", memory + 1, memory + 1, iteration + 1);
    eval_depth = memory;
  } else {
    println!("Evaluate {} iterations ...", iteration + 1);
    eval_depth = iteration;
  }

  let accessed_trigger = get_accessed_streams(ir);
  if accessed_trigger.is_empty() {
    println!("No trigger accessed! What output should vary here?")
  }
  let mut model = Model { ir: &ir, ctx: &z3_ctx, epsilon, eval_depth, lnorm, is_true: true };
  model.analyze_model(&accessed_trigger, z3);
}
