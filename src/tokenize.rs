#[derive(Debug, Clone)]
pub enum Token {
    Identifier(&'static str),
    Number(i32),
    Operator(char),
    Equals,
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Colon,
    Semicolon,
    Return,
    If
}

fn read_identifier(index: &mut usize, chars: &[char], first_char: char) -> &'static str {
    let mut identifier = first_char.to_string();

    *index += 1;
    while *index < chars.len() {
        let c = chars[*index];
        match c {
            'A'..='Z' | 'a'..='z' | '0'..='9' | '_' => {
                identifier.push(c);
                *index += 1;
            },
            _ => {
                *index -= 1;
                break;
            }
        }
    }

    Box::new(identifier).leak()
}

fn read_number(index: &mut usize, chars: &[char], first_char: char) -> i32 {
    let mut number = first_char.to_string();

    *index += 1;
    while *index < chars.len() {
        let c = chars[*index];
        match c {
            '0'..='9' => {
                number.push(c);
                *index += 1;
            },
            _ => {
                *index -= 1;
                break;
            }
        }
    }

    number.parse().expect("Failed to parse number. Should be impossible")
}

pub fn tokenize(text: &'static str) -> Vec<Token> {
    let mut tokens = Vec::new();

    let chars: Vec<char> = text.chars().collect();
    let mut index = 0;

    while index < chars.len() {
        let c = chars[index];

        let token = match c {
            ' ' | '\t' | '\n' => {
                index += 1;
                continue;
            },

            'A'..='Z' | 'a'..='z' => {
                let identifier = read_identifier(&mut index, &chars, c);
                match identifier {
                    "return" => Token::Return,
                    "if" => Token::If,
                    _ => Token::Identifier(identifier)
                }
            },

            '0'..='9' => {
                let number = read_number(&mut index, &chars, c);
                Token::Number(number)
            },

            '+' | '-' | '*' | '/' => Token::Operator(c),

            '=' => Token::Equals,
            '(' => Token::LeftParen,
            ')' => Token::RightParen,
            '{' => Token::LeftBrace,
            '}' => Token::RightBrace,
            ',' => Token::Comma,
            ':' => Token::Colon,
            ';' => Token::Semicolon,

            _ => panic!("Unknown char {}", c)
        };

        tokens.push(token);

        index += 1;
    }

    tokens
}