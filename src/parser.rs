use crate::tokenizer::Token;
use std::fmt::Display;

#[derive(Debug, Clone)]
struct Assignment {
    identifier: &'static str,
    expression: Expression
}

#[derive(Debug, Clone)]
struct Call {
    identifier: &'static str,
    arguments: Vec<Expression>
}

#[derive(Debug, Clone)]
pub enum Expression {
    Identifier(&'static str),
    Number(i32),
    Assignment {
        identifier: &'static str,
        expression: Box<Expression>
    },
    Call {
        identifier: &'static str,
        arguments: Vec<Expression>
    },
    ParenExpression(Box<Expression>),
    UnaryExpression {
        operator: char,
        expression: Box<Expression>
    },
    BinaryExpression {
        lhs: Box<Expression>,
        operator: char,
        rhs: Box<Expression>
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Expression::Number(number) => write!(f, "{}", number),
            Expression::Identifier(identifier) => write!(f, "{}", identifier),
            Expression::Assignment {identifier, expression} => {
                write!(f, "{} = {}", identifier, expression)
            },
            Expression::Call {identifier, arguments} => {
                write!(f, "{}(", identifier)?;

                for (index, argument) in arguments.iter().enumerate() {
                    write!(f, "{}", argument)?;

                    if index != arguments.len() - 1 {
                        write!(f, ", ")?;
                    }
                }

                write!(f, ")")
            },
            Expression::ParenExpression(expression) => {
                write!(f, "({})", expression)
            },
            Expression::UnaryExpression {operator, expression} => {
                write!(f, "{}{}", operator, expression)
            },
            Expression::BinaryExpression {lhs, operator, rhs} => {
                write!(f, "{} {} {}", lhs, operator, rhs)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Statement {
    Assignment {
        identifier: &'static str,
        expression: Expression
    },
    Call {
        identifier: &'static str,
        arguments: Vec<Expression>
    },
    Return {
        expression: Expression
    },
    If {
        expression: Expression,
        block: Vec<Statement>
    },
    Block {
        block: Vec<Statement>
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Statement::Assignment {identifier, expression} => {
                write!(f, "  {} = {};", identifier, expression)?;
            },
            Statement::Call {identifier, arguments} => {
                write!(f, "  {}(", identifier)?;

                for (index, argument) in arguments.iter().enumerate() {
                    write!(f, "{}", argument)?;

                    if index != arguments.len() - 1 {
                        write!(f, ", ")?;
                    }
                }

                write!(f, ");")?;
            },
            Statement::Return {expression} => {
                write!(f, "  return {};", expression)?;
            },
            Statement::If {expression, block} => {
                write!(f, "  if {} {{\n", expression)?;

                for statement in block.iter() {
                    write!(f, "  {}\n", statement)?;
                }

                write!(f, "  }}")?;
            },
            Statement::Block {block} => {
                write!(f, "  {{\n")?;

                for statement in block.iter() {
                    write!(f, "  {}\n", statement)?;
                }

                write!(f, "  }}")?;
            }
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Parameter {
    pub identifier: &'static str,
    pub r#type: &'static str
}

impl Display for Parameter {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}: {}", self.identifier, self.r#type)
    }
}

#[derive(Debug, Clone)]
pub struct Function {
    pub identifier: &'static str,
    pub parameters: Vec<Parameter>,
    pub r#type: Option<&'static str>,
    pub block: Vec<Statement>
}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}(", self.identifier)?;

        for (index, parameter) in self.parameters.iter().enumerate() {
            write!(f, "{}", parameter)?;

            if index != self.parameters.len() - 1 {
                write!(f, ", ")?;
            }
        }

        write!(f, ")")?;

        if let Some(r#type) = self.r#type {
            write!(f, ": {}", r#type)?;
        }

        write!(f, " {{\n")?;

        for statement in self.block.iter() {
            write!(f, "{}\n", statement)?;
        }

        write!(f, "}}")
    }
}

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: Vec<Function>
}

impl Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for function in self.functions.iter() {
            write!(f, "{}\n", function)?;
        }

        Ok(())
    }
}

fn precedence(operator: char) -> i32 {
    match operator {
        '+' | '-' => 0,
        '*' | '/' => 1,
        _ => panic!("Unimplemented operator, got {:#?}", operator)
    }
}

fn make_binary_expression(expression1: Expression, operator1: char, expression2: Expression) -> Expression {
    match expression2 {
        Expression::BinaryExpression {lhs, operator: operator2, rhs } => {
            if precedence(operator1) < precedence(operator2) {
                Expression::BinaryExpression {
                    lhs: Box::new(expression1),
                    operator: operator1,
                    rhs: Box::new(Expression::BinaryExpression {
                        lhs,
                        operator: operator2,
                        rhs
                    })
                }
            } else {
                Expression::BinaryExpression {
                    lhs: Box::new(Expression::BinaryExpression {
                        lhs: Box::new(expression1),
                        operator: operator1,
                        rhs: lhs
                    }),
                    operator: operator2,
                    rhs
                }
            }
        }
        _ => {
            Expression::BinaryExpression {
                lhs: Box::new(expression1),
                operator: operator1,
                rhs: Box::new(expression2)
            }
        }
    }
}

// expression:
//      number
//      identifier
//      call
//      assignment
//      expression operator expression
//      '(' expression ')'
fn read_expression(index: &mut usize, tokens: &[Token]) -> Option<Expression> {
    let minus = match tokens.get(*index) {
        Some(&Token::Operator(operator)) if operator == '-' => {
            *index += 1;
            true
        }
        _ => false
    };

    match tokens.get(*index) {
        Some(&Token::Number(number)) => {
            let expression1 = if minus {
                Expression::Number(-number)
            } else {
                Expression::Number(number)
            };

            *index += 1;
            match tokens.get(*index) {
                Some(&Token::Operator(operator)) => {

                    *index += 1;
                    let expression2 = match read_expression(index, tokens) {
                        Some(expression) => expression,
                        None => panic!("Expected expression after operator, got {:#?}", tokens.get(*index))
                    };

                    let binary_expression = make_binary_expression(expression1, operator, expression2);
                    Some(binary_expression)
                },
                _ => {
                    *index -= 1;
                    Some(expression1)
                }
            }
        },
        Some(&Token::Identifier(identifier)) => {

            *index += 1;
            match tokens.get(*index) {
                Some(&Token::Operator(operator)) => {
                    let expression1 = if minus {
                        Expression::UnaryExpression {
                            operator: '-',
                            expression: Box::new(Expression::Identifier(identifier))
                        }
                    } else {
                        Expression::Identifier(identifier)
                    };

                    *index += 1;
                    let expression2 = match read_expression(index, tokens) {
                        Some(expression) => expression,
                        _ => panic!("Expected expression after operator, got {:#?}", tokens.get(*index))
                    };

                    let binary_expression = make_binary_expression(expression1, operator, expression2);
                    Some(binary_expression)
                },
                Some(Token::LeftParen) => {
                    let arguments = read_arguments(index, tokens);

                    let call = if minus {
                        Expression::UnaryExpression {
                            operator: '-',
                            expression: Box::new(Expression::Call {identifier, arguments})
                        }
                    } else {
                        Expression::Call {identifier, arguments}
                    };

                    Some(call)
                },
                Some(Token::Equals) => {

                    *index += 1;
                    let expression = match read_expression(index, tokens) {
                        Some(expression) => expression,
                        _ => panic!("Expected expression after equals sign, got {:#?}", tokens.get(*index))
                    };

                    let assignment = Expression::Assignment {
                        identifier,
                        expression: Box::new(expression)
                    };

                    Some(assignment)
                }
                _ => {
                    *index -= 1;

                    let expression = if minus {
                        Expression::UnaryExpression {
                            operator: '-',
                            expression: Box::new(Expression::Identifier(identifier))
                        }
                    } else {
                        Expression::Identifier(identifier)
                    };

                    Some(expression)
                }
            }
        },
        Some(Token::LeftParen) => {

            *index += 1;
            let expression1 = match read_expression(index, tokens) {
                Some(expression) => expression,
                _ => panic!("Expected expression after left parenthesis, got {:#?}", tokens.get(*index))
            };

            *index += 1;
            match tokens.get(*index) {
                Some(Token::RightParen) => {},
                _ => panic!("Expected right parenthesis after expression, got {:#?}", tokens.get(*index))
            }

            let expression1 = if minus {
                Expression::UnaryExpression {
                    operator: '-',
                    expression: Box::new(Expression::ParenExpression(Box::new(expression1)))
                }
            } else {
                Expression::ParenExpression(Box::new(expression1))
            };

            *index += 1;
            match tokens.get(*index) {
                Some(&Token::Operator(operator)) => {

                    *index += 1;
                    let expression2 = match read_expression(index, tokens) {
                        Some(expression) => expression,
                        _ => panic!("Expected expression after operator, got {:#?}", tokens.get(*index))
                    };

                    let binary_expression = make_binary_expression(expression1, operator, expression2);
                    Some(binary_expression)
                },
                _ => {
                    *index -= 1;
                    Some(expression1)
                }
            }
        },
        _ => None
    }
}

// Starts on identifier, ends on complete expression
// assignment = identifier '=' expression
fn read_assignment(index: &mut usize, tokens: &[Token]) -> Assignment {
    let identifier = match tokens.get(*index) {
        Some(&Token::Identifier(identifier)) => identifier,
        _ => panic!("Expected identifier, got {:#?}", tokens.get(*index))
    };

    *index += 1;
    match tokens.get(*index) {
        Some(Token::Equals) => {},
        _ => panic!("Expected equals sign after identifier, got {:#?}", tokens.get(*index))
    }

    *index += 1;
    let expression = match read_expression(index, tokens) {
        Some(expression) => expression,
        _ => panic!("Expected expression after equals sign")
    };

    Assignment {identifier, expression}
}

// Starts on identifier, ends on semicolon
// statement = (call | assignment) ';'
fn read_statement(index: &mut usize, tokens: &[Token]) -> Option<Statement> {
    let statement = match tokens.get(*index) {
        Some(&Token::Identifier(identifier)) => {
            *index += 1;
            match tokens.get(*index) {
                Some(Token::LeftParen) => {
                    let arguments = read_arguments(index, tokens);

                    *index += 1;
                    match tokens.get(*index) {
                        Some(Token::Semicolon) => {},
                        _ => panic!("Expected semicolon after call, got {:#?}", tokens.get(*index))
                    }

                    Statement::Call {identifier, arguments}
                }
                Some(Token::Equals) => {

                    *index += 1;
                    let expression = match read_expression(index, tokens) {
                        Some(expression) => expression,
                        _ => panic!("Expected expression after equals sign, got {:#?}", tokens.get(*index))
                    };

                    *index += 1;
                    match tokens.get(*index) {
                        Some(Token::Semicolon) => {},
                        _ => panic!("Expected semicolon after expression, got {:#?}", tokens.get(*index))
                    }

                    Statement::Assignment {identifier, expression}
                },
                _ => panic!("Expected left parenthesis or equals sign after identifier, got {:#?}", tokens.get(*index))
            }
        },
        Some(Token::Return) => {
            *index += 1;

            let expression = match read_expression(index, tokens) {
                Some(expression) => expression,
                _ => panic!("Expected expression after return statement, got {:#?}", tokens.get(*index))
            };

            *index += 1;
            match tokens.get(*index) {
                Some(Token::Semicolon) => {},
                _ => panic!("Expected semicolon after expression, got {:#?}", tokens.get(*index))
            }

            Statement::Return {expression}
        },
        Some(Token::If) => {
            *index += 1;

            let expression = match read_expression(index, tokens) {
                Some(expression) => expression,
                _ => panic!("Expected expression after return statement, got {:#?}", tokens.get(*index))
            };

            *index += 1;
            let block = match tokens.get(*index) {
                Some(Token::LeftBrace) => read_block(index, tokens),
                _ => panic!("Expected left brace, got {:#?}", tokens.get(*index))
            };

            Statement::If {expression, block}
        },
        Some(Token::LeftBrace) => {
            let block = read_block(index, tokens);
            Statement::Block {block}
        }
        _ => return None
    };

    Some(statement)
}

// Starts on '(', ends on ')'
// args = (arg (',' arg)*)?
// arg = expression
fn read_arguments(index: &mut usize, tokens: &[Token]) -> Vec<Expression> {
    let mut arguments: Vec<Expression> = Vec::new();

    *index += 1;
    let argument = match tokens.get(*index) {
        Some(Token::RightParen) => return arguments,
        _ => match read_expression(index, tokens) {
            Some(expression) => expression,
            _ => panic!("Expected right parenthesis or expression, got {:#?}", tokens.get(*index))
        }
    };

    arguments.push(argument);

    *index += 1;
    while *index < tokens.len() {
        match tokens.get(*index) {
            Some(Token::Comma) => {}
            Some(Token::RightParen) => break,
            _ => panic!("Expected right parenthesis or comma after expression, got {:#?}", tokens.get(*index))
        };

        *index += 1;
        let argument = match tokens.get(*index) {
            Some(Token::RightParen) => break,
            _ => match read_expression(index, tokens) {
                Some(expression) => expression,
                _ => panic!("Expected right parenthesis or expression, got {:#?}", tokens.get(*index))
            }
        };
        arguments.push(argument);

        *index += 1;
    }

    arguments
}

// Starts on identifier, ends on identifier
// param = identifier ':' identifier
fn read_parameter(index: &mut usize, tokens: &[Token]) -> Parameter {
    let identifier = match tokens.get(*index) {
        Some(&Token::Identifier(identifier)) => identifier,
        _ => panic!("Expected identifier, got {:#?}", tokens.get(*index))
    };

    *index += 1;
    match tokens.get(*index) {
        Some(Token::Colon) => {},
        _ => panic!("Expected colon, got {:#?}", tokens.get(*index))
    }

    *index += 1;
    let r#type = match tokens.get(*index) {
        Some(&Token::Identifier(identifier)) => identifier,
        _ => panic!("Expected type identifier, got {:#?}", tokens.get(*index))
    };

    Parameter {identifier, r#type}
}

// Starts on '(', ends on ')'
// params = (param (',' param)*)?
fn read_parameters(index: &mut usize, tokens: &[Token]) -> Vec<Parameter> {
    let mut parameters = Vec::new();

    *index += 1;
    let parameter = match tokens.get(*index) {
        Some(Token::RightParen) => return parameters,
        Some(Token::Identifier(_)) => read_parameter(index, tokens),
        _ => panic!("Expected right parenthesis or identifier, got {:#?}", tokens.get(*index))
    };
    parameters.push(parameter);

    *index += 1;
    while *index < tokens.len() {
        match tokens.get(*index) {
            Some(Token::Comma) => {}
            Some(Token::RightParen) => break,
            _ => panic!("Expected right parenthesis or comma after identifier, got {:#?}", tokens.get(*index))
        };

        *index += 1;
        let parameter = match tokens.get(*index) {
            Some(Token::Identifier(_)) => read_parameter(index, tokens),
            _ => panic!("Expected identifier after comma, got {:#?}", tokens.get(*index))
        };
        parameters.push(parameter);

        *index += 1;
    }

    parameters
}

// Starts on '{', ends on '}'
// block = statement*
fn read_block(index: &mut usize, tokens: &[Token]) -> Vec<Statement> {
    let mut block = Vec::new();

    *index += 1;
    while *index < tokens.len() {
        let statement = match tokens.get(*index) {
            Some(Token::RightBrace) => break,
            _ => {
                match read_statement(index, tokens) {
                    Some(statement) => statement,
                    _ => panic!("Expected right brace or statement, got {:#?}", tokens.get(*index))
                }
            },
        };
        block.push(statement);

        *index += 1;
    }

    block
}
// Starts on identifier, ends on '}'
// function = identifier '(' params ')' (':' identifier)? '{' block '}'
fn read_function(index: &mut usize, tokens: &[Token]) -> Function {
    let identifier = match tokens.get(*index) {
        Some(&Token::Identifier(identifier)) => identifier,
        _ => panic!("Expected identifier, got {:#?}", tokens.get(*index))
    };

    *index += 1;
    let parameters = match tokens.get(*index) {
        Some(Token::LeftParen) => read_parameters(index, tokens),
        _ => panic!("Expected left parenthesis, got {:#?}", tokens.get(*index))
    };

    *index += 1;
    let r#type = match tokens.get(*index) {
        Some(Token::Colon) => {

            *index += 1;
            match tokens.get(*index) {
                Some(&Token::Identifier(identifier)) => {
                    *index += 1;
                    Some(identifier)
                },
                _ => panic!("Expected identifier, got {:#?}", tokens.get(*index))
            }
        },
        Some(Token::LeftBrace) => None,
        _ => panic!("Expected left brace or colon, got {:#?}", tokens.get(*index))
    };

    // index not incremented intentionally
    let block = match tokens.get(*index) {
        Some(Token::LeftBrace) => read_block(index, tokens),
        _ => panic!("Expected left brace, got {:#?}", tokens.get(*index))
    };

    Function {identifier, parameters, r#type, block}
}

pub fn build_ast(tokens: &[Token]) -> Program {
    let mut index = 0;
    let mut functions = Vec::new();

    while index < tokens.len() {
        match tokens.get(index) {
            Some(Token::Identifier(_)) => {
                let function = read_function(&mut index, &tokens);
                functions.push(function);
            },
            _ => panic!("Expected identifier, got {:#?}", tokens.get(index))
        }

        index += 1;
    }

    Program {functions}
}