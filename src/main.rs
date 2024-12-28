mod tokenizer;
mod parser;
use crate::tokenizer::tokenize;
use crate::parser::*;
use std::collections::HashMap;
use std::fmt::Display;
use std::ops::{RangeInclusive, Add, Sub, Mul, Div};

#[derive(Debug, Clone)]
enum Restriction {
    Number(i32),
    Range(RangeInclusive<i32>)
}

#[derive(Debug, Clone)]
struct NumberType {
    restrictions: Vec<Restriction>
}

impl Add for NumberType {
    type Output = NumberType;

    fn add(self, rhs: Self) -> Self::Output {
        let mut restrictions = Vec::new();

        for lhs in self.restrictions.iter() {
            for rhs in rhs.restrictions.iter() {
                match (lhs, rhs) {
                    (Restriction::Number(lhs), Restriction::Number(rhs)) => {
                        restrictions.push(Restriction::Number(lhs + rhs));
                    },
                    (Restriction::Number(lhs), Restriction::Range(rhs)) => {
                        let range = RangeInclusive::new(lhs + rhs.start(), lhs + rhs.end());
                        restrictions.push(Restriction::Range(range));
                    },
                    (Restriction::Range(lhs), Restriction::Number(rhs)) => {
                        let range = RangeInclusive::new(lhs.start() + rhs, lhs.end() + rhs);
                        restrictions.push(Restriction::Range(range));
                    },
                    (Restriction::Range(lhs), Restriction::Range(rhs)) => {
                        let range = RangeInclusive::new(lhs.start() + rhs.start(), lhs.end() + rhs.end());
                        restrictions.push(Restriction::Range(range));
                    }
                }
            }
        }

        NumberType {restrictions}
    }
}

impl Sub for NumberType {
    type Output = NumberType;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut restrictions = Vec::new();

        for lhs in self.restrictions.iter() {
            for rhs in rhs.restrictions.iter() {
                match (lhs, rhs) {
                    (Restriction::Number(lhs), Restriction::Number(rhs)) => {
                        restrictions.push(Restriction::Number(lhs - rhs));
                    },
                    (Restriction::Number(lhs), Restriction::Range(rhs)) => {
                        let range = RangeInclusive::new(lhs - rhs.start(), lhs - rhs.end());
                        restrictions.push(Restriction::Range(range));
                    },
                    (Restriction::Range(lhs), Restriction::Number(rhs)) => {
                        let range = RangeInclusive::new(lhs.start() - rhs, lhs.end() - rhs);
                        restrictions.push(Restriction::Range(range));
                    },
                    (Restriction::Range(lhs), Restriction::Range(rhs)) => {
                        let range = RangeInclusive::new(lhs.start() - rhs.start(), lhs.end() - rhs.end());
                        restrictions.push(Restriction::Range(range));
                    }
                }
            }
        }

        NumberType {restrictions}
    }
}

impl Mul for NumberType {
    type Output = NumberType;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut restrictions = Vec::new();

        for lhs in self.restrictions.iter() {
            for rhs in rhs.restrictions.iter() {
                match (lhs, rhs) {
                    (Restriction::Number(lhs), Restriction::Number(rhs)) => {
                        restrictions.push(Restriction::Number(lhs * rhs));
                    },
                    (Restriction::Number(lhs), Restriction::Range(rhs)) => {
                        let range = RangeInclusive::new(lhs * rhs.start(), lhs * rhs.end());
                        restrictions.push(Restriction::Range(range));
                    },
                    (Restriction::Range(lhs), Restriction::Number(rhs)) => {
                        let range = RangeInclusive::new(lhs.start() * rhs, lhs.end() * rhs);
                        restrictions.push(Restriction::Range(range));
                    },
                    (Restriction::Range(lhs), Restriction::Range(rhs)) => {
                        let range = RangeInclusive::new(lhs.start() * rhs.start(), lhs.end() * rhs.end());
                        restrictions.push(Restriction::Range(range));
                    }
                }
            }
        }

        NumberType {restrictions}
    }
}

impl Div for NumberType {
    type Output = NumberType;

    fn div(self, rhs: Self) -> Self::Output {
        let mut restrictions = Vec::new();

        for lhs in self.restrictions.iter() {
            for rhs in rhs.restrictions.iter() {
                match (lhs, rhs) {
                    (Restriction::Number(lhs), Restriction::Number(rhs)) => {
                        restrictions.push(Restriction::Number(lhs / rhs));
                    },
                    (Restriction::Number(lhs), Restriction::Range(rhs)) => {
                        let range = RangeInclusive::new(lhs / rhs.start(), lhs / rhs.end());
                        restrictions.push(Restriction::Range(range));
                    },
                    (Restriction::Range(lhs), Restriction::Number(rhs)) => {
                        let range = RangeInclusive::new(lhs.start() / rhs, lhs.end() / rhs);
                        restrictions.push(Restriction::Range(range));
                    },
                    (Restriction::Range(lhs), Restriction::Range(rhs)) => {
                        let range = RangeInclusive::new(lhs.start() / rhs.start(), lhs.end() / rhs.end());
                        restrictions.push(Restriction::Range(range));
                    }
                }
            }
        }

        NumberType {restrictions}
    }
}

fn operation(lhs: NumberType, operator: char, rhs: NumberType) -> NumberType {
    match operator {
        '+' => lhs + rhs,
        '-' => lhs - rhs,
        '*' => lhs * rhs,
        '/' => lhs / rhs,
        _ => panic!("Unexpected operator")
    }
}

fn get_number_type(
    functions: &mut HashMap<&'static str, Function>,
    variables: &mut HashMap<&'static str, NumberType>,
    expression: &Expression
) -> NumberType {
    match expression {
        Expression::ParenExpression(expression) => {
            get_number_type(functions, variables, expression)
        },
        Expression::BinaryExpression {lhs, operator, rhs} => {
            let lhs_number_type = get_number_type(functions, variables, lhs);
            let rhs_number_type = get_number_type(functions, variables, rhs);
            operation(lhs_number_type, *operator, rhs_number_type)
        },
        Expression::Number(number) => {
            NumberType {restrictions: vec![Restriction::Number(number.clone())]}
        },
        Expression::Identifier(identifier) => {
            variables.get(identifier).expect("Unknown variable").clone()
        },
        Expression::Assignment {identifier, expression} => {
            let number_type = get_number_type(functions, variables, expression);

            if number_type.restrictions.len() == 1 {
                match number_type.restrictions[0] {
                    Restriction::Number(_) => {
                        variables.insert(identifier, number_type.clone());
                    },
                    _ => {}
                }
            }

            number_type
        },
        Expression::Call {identifier, ..} => {
            functions.get(identifier).expect("Unknown function").clone()
        },
        Expression::UnaryExpression { .. } => {}
    }
}

fn get_variable_data(functions: &mut HashMap<&'static str, Function>, function: &Function) {
    let mut variables = HashMap::new();

    for statement in function.block.iter() {
        match statement {
            Statement::Assignment {identifier, expression} => {
                let number_type = get_number_type(functions, &mut variables, expression);

                variables.insert(identifier, number_type);
            },
            _ => {}
        }
    }
}

fn get_program_data(program: &Program) {
    let mut functions = HashMap::new();

    for function in program.functions.iter() {
        functions.insert(function.identifier, function.clone());
    }

    for function in program.functions.iter() {

    }
}

fn main() {
    let text = "
    main() {
        a = 1;

        if a {
            a = a * 2;
        }

        return a;
    }
    ";
    let tokens = tokenize(text);
    let program = build_ast(&tokens);

    get_program_data(&program);
}