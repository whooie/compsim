//! Lambda calculus simulator.

use std::{
    mem::{ swap, take },
    rc::Rc,
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LambdaError {
    #[error("error while parsing: invalid character {0:?} in symbol at line {1}, char {2}")]
    InvalidSym(char, usize, usize),

    #[error("error while parsing: invalid symbol terminator at line {0}, char {1}")]
    InvalidSymEnd(usize, usize),

    #[error("error while parsing: unterminated symbol bracket at line {0}, char {1}")]
    UnterminatedSym(usize, usize),

    #[error("error while parsing: illegal empty symbol at line {0}, char {1}")]
    EmptySym(usize, usize),

    #[error("error while parsing: invalid expression terminator at line {0}, char {1}")]
    InvalidExprEnd(usize, usize),

    #[error("error while parsing: unterminated expression bracket at line {0}, char {1}")]
    UnterminatedExpr(usize, usize),

    #[error("error while parsing: invalid character {0:?} in unbracketed arg at line {0}, char {1}")]
    InvalidArg(char, usize, usize),

    #[error("error while parsing: unterminated lambda arg at line {0}, char {1}")]
    UnterminatedArg(usize, usize),

    #[error("error while parsing: invalid function definition")]
    InvalidFunc,

    #[error("error while parsing: unexpected symbol {0}")]
    UnexpectedSym(String),

    #[error("error while parsing: unexpected `.`")]
    UnexpectedDot,

    #[error("error while parsing: unexpected `λ`/`\\`")]
    UnexpectedLambda,

    #[error("error while parsing: missing function arg")]
    MissingArg,

    #[error("error while parsing: missing function body")]
    MissingBody,
}
use LambdaError::*;
pub type LambdaResult<T> = Result<T, LambdaError>;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Sym {
    A(String),
    Z(usize), // used for equality testing
}

impl From<String> for Sym {
    fn from(s: String) -> Self { Self::A(s) }
}

impl From<&str> for Sym {
    fn from(s: &str) -> Self { Self::A(s.to_string()) }
}

impl From<char> for Sym {
    fn from(c: char) -> Self { Self::A(c.to_string()) }
}

impl From<usize> for Sym {
    fn from(n: usize) -> Self { Self::Z(n) }
}

impl std::fmt::Display for Sym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const SPECIAL: [char; 8] = [' ', '.', '\\', 'λ', '(', ')', '[', ']'];
        match self {
            Self::A(s) => {
                if SPECIAL.iter().any(|&c| s.contains(c)) {
                    write!(f, "[{}]", s)
                } else {
                    write!(f, "{}", s)
                }
            },
            Self::Z(n) => write!(f, "[{}]", n),
        }
    }
}

/// A single symbol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbol(Sym);

impl From<String> for Symbol {
    fn from(s: String) -> Self { Self(s.into()) }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Self { Self(s.into()) }
}

impl From<char> for Symbol {
    fn from(c: char) -> Self { Self(c.into()) }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A lambda term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Lambda {
    /// An empty expression.
    Null,
    /// A single symbol.
    Sym(Symbol),
    /// A function definition.
    Func(Symbol, Rc<Lambda>),
    /// An application of the left to the right.
    App(Rc<Lambda>, Rc<Lambda>),
}

impl From<char> for Lambda {
    fn from(c: char) -> Self { Self::Sym(c.into()) }
}

impl Lambda {
    fn is_null(&self) -> bool { matches!(self, Self::Null) }

    /// Create a new symbol.
    pub fn sym<T>(x: T) -> Self
    where T: Into<Symbol>
    {
        Self::Sym(x.into())
    }

    /// Create a new function.
    pub fn func<T>(arg: T, body: Self) -> Self
    where T: Into<Symbol>
    {
        Self::Func(arg.into(), body.into())
    }

    /// Apply a function to an argument.
    pub fn app(func: Self, arg: Self) -> Self {
        Self::App(func.into(), arg.into())
    }

    /// Apply `self` to an argument.
    pub fn apply_to(self, arg: Self) -> Self {
        Self::App(self.into(), arg.into())
    }

    /// Return `true` if `self` is `Sym`.
    pub fn is_sym(&self) -> bool { matches!(self, Self::Sym(_)) }

    /// Return `true` if `self` is `Func`.
    pub fn is_func(&self) -> bool { matches!(self, Self::Func(..)) }

    /// Return `true` if `self` is `App`.
    pub fn is_app(&self) -> bool { matches!(self, Self::App(..)) }

    /// If `self` is `Func`, return its argument symbol.
    pub fn get_func_arg(&self) -> Option<Symbol> {
        match self {
            Self::Func(a, _) => Some(a.clone()),
            _ => None
        }
    }

    /// If `self` is `Func`, return its body.
    pub fn get_func_body(&mut self) -> Option<&mut Self> {
        match self {
            Self::Func(_, b) => Some(Rc::make_mut(b)),
            _ => None
        }
    }

    /// If `self` is `Func`, return its argument symbol and body.
    pub fn get_func_components(&mut self) -> Option<(Symbol, &mut Self)> {
        match self {
            Self::Func(a, b) => Some((a.clone(), Rc::make_mut(b))),
            _ => None
        }
    }

    /// Perform α-conversion.
    pub fn convert(&mut self, old: &Symbol, new: &Symbol) -> &mut Self {
        match self {
            Self::Null => { },
            Self::Sym(s) => {
                if s == old { *s = new.clone(); }
            },
            Self::Func(a, b) => {
                if a == old { *a = new.clone(); }
                Rc::make_mut(b).convert(old, new);
            },
            Self::App(a, b) => {
                Rc::make_mut(a).convert(old, new);
                Rc::make_mut(b).convert(old, new);
            },
        }
        self
    }

    /// Substitute any lambda term for a symbol.
    pub fn substitute(&mut self, old: &Symbol, new: &Self) -> &mut Self {
        match self {
            Self::Null => { },
            Self::Sym(s) => {
                if s == old { *self = new.clone(); }
            },
            Self::Func(_, b) => {
                Rc::make_mut(b).substitute(old, new);
            },
            Self::App(a, b) => {
                Rc::make_mut(a).substitute(old, new);
                Rc::make_mut(b).substitute(old, new);
            }
        }
        self
    }

    fn has_unreduced(&self) -> bool {
        match self {
            Self::Null => false,
            Self::Sym(_) => false,
            Self::Func(_, b) => b.has_unreduced(),
            Self::App(a, b)
                => a.has_unreduced() || b.has_unreduced() || a.is_func(),
        }
    }

    /// Perform β-reduction.
    pub fn reduce(&mut self) -> &mut Self {
        while self.has_unreduced() {
            match self {
                Self::Null => { },
                Self::Sym(_) => { },
                Self::Func(_, b) => {
                    Rc::make_mut(b).reduce();
                },
                Self::App(a, b) => {
                    Rc::make_mut(a).reduce();
                    if a.is_null() {
                        *self = Self::Null;
                        return self;
                    }
                    Rc::make_mut(b).reduce();
                    if let Some(arg) = a.get_func_arg() {
                        Rc::make_mut(a).substitute(&arg, b.as_ref());
                        let Some(bod) = Rc::make_mut(a).get_func_body()
                            else { unreachable!() };
                        let mut new = Self::Null;
                        swap(&mut new, bod);
                        swap(&mut new, self);
                    }
                },
            }
        }
        self
    }
}

impl std::fmt::Display for Lambda {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Null => write!(f, "()"),
            Self::Sym(s) => write!(f, "{}", s),
            Self::Func(a, b) => write!(f, "(λ{}.{})", a, b.as_ref()),
            Self::App(a, b) => write!(f, "({} {})", a.as_ref(), b.as_ref()),
        }
    }
}

impl std::str::FromStr for Lambda {
    type Err = LambdaError;

    fn from_str(s: &str) -> LambdaResult<Self> {
        let tokens = tokenize(s.chars())?;
        parse(&tokens)
    }
}

#[derive(Copy, Clone, Debug)]
struct Position { line: usize, ch: usize }

/// Items interpreted from a string representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    /// A null lambda term, `()`.
    Null,
    /// A lambda argument identifier, `λ` or `\`.
    Lambda,
    /// A lambda body identifier, `.`.
    Dot,
    /// A single symbol.
    Word(String),
    /// A sub-expression grouped in parentheses.
    SubExpr(Vec<Token>),
}

/// Convert a stream of [`char`]s into tokens.
pub fn tokenize<I>(input: I) -> LambdaResult<Vec<Token>>
where I: IntoIterator<Item = char>
{
    let mut tokens: Vec<Token> = Vec::new();
    do_tokenize(
        input.into_iter(),
        false,
        Position { line: 0, ch: 0 },
        &mut tokens,
    )?;
    Ok(tokens)
}

// read chars into words, making sure they're space-delineated
//
// hand off to other functions when the following chars are encountered:
// - `[` => do_tokenize_bracket
// - `//` => do_tokenize_linecmt
// - `/*` => do_tokenize_blkcmt
fn do_tokenize<I>(
    mut input: I,
    in_paren: bool,
    mut pos: Position,
    buf: &mut Vec<Token>,
) -> LambdaResult<(I, Position)>
where I: Iterator<Item = char>
{
    use Token::*;
    let pos0 = pos;
    if in_paren { pos.ch += 1; }
    let mut in_arg: bool = false;
    let mut word = String::new();
    loop {
        match input.next() {
            None => {
                if in_paren {
                    return Err(UnterminatedExpr(pos0.line, pos0.ch));
                } else {
                    if !word.is_empty() { buf.push(Word(take(&mut word))); }
                    return Ok((input, pos));
                }
            },
            Some(' ') | Some('\t') => {
                if !word.is_empty() { buf.push(Word(take(&mut word))); }
                pos.ch += 1;
            },
            Some('\n') => {
                if !word.is_empty() { buf.push(Word(take(&mut word))); }
                pos.ch = 0;
                pos.line += 1;
            },
            Some('(') => {
                if !word.is_empty() {
                    return Err(InvalidSym('(', pos.line, pos.ch));
                }
                let mut expr: Vec<Token> = Vec::new();
                let rec = do_tokenize(input, true, pos, &mut expr)?;
                pos = rec.1;
                input = rec.0;
                if expr.is_empty() {
                    buf.push(Null);
                } else {
                    buf.push(SubExpr(expr));
                }
            },
            Some(')') => {
                if in_paren {
                    if !word.is_empty() { buf.push(Word(take(&mut word))); }
                    pos.ch += 1;
                    return Ok((input, pos));
                } else {
                    return Err(InvalidExprEnd(pos.line, pos.ch));
                }
            },
            Some('[') => {
                if !word.is_empty() {
                    return Err(InvalidSym('[', pos.line, pos.ch));
                }
                let mut sym: Vec<Token> = Vec::new();
                let rec = do_tokenize_bracket(input, pos, &mut sym)?;
                pos = rec.1;
                input = rec.0;
                // sym.len() == 1
                buf.append(&mut sym);
            },
            Some(']') => {
                return Err(InvalidSymEnd(pos.line, pos.ch));
            },
            Some(l) if l == 'λ' || l == '\\' => {
                if !word.is_empty() {
                    return Err(InvalidSym(l, pos.line, pos.ch));
                }
                buf.push(Lambda);
                in_arg = true;
                pos.ch += 1;
            },
            Some('.') => {
                if in_arg {
                    if word.is_empty() {
                        if buf.last() == Some(&Lambda) {
                            return Err(EmptySym(pos.line, pos.ch));
                        }
                    } else {
                        buf.push(Word(take(&mut word)));
                    }
                } else {
                    return Err(InvalidSym('.', pos.line, pos.ch));
                }
                buf.push(Dot);
                in_arg = false;
                pos.ch += 1;
            },
            Some('/') => match input.next() {
                Some('/') => {
                    if !word.is_empty() { buf.push(Word(take(&mut word))); }
                    pos.ch += 2;
                    let rec = do_tokenize_linecmt(input, pos)?;
                    pos = rec.1;
                    input = rec.0;
                },
                Some('*') => {
                    if !word.is_empty() { buf.push(Word(take(&mut word))); }
                    pos.ch += 2;
                    let rec = do_tokenize_blkcmt(input, pos)?;
                    pos = rec.1;
                    input = rec.0;
                },
                _ => {
                    return Err(InvalidSym('/', pos.line, pos.ch));
                },
            },
            Some('*') => {
                return Err(InvalidSym('*', pos.line, pos.ch));
            },
            Some(c) => {
                word.push(c);
                pos.ch += 1;
            },
        }
    }
}

// read every char until the next `]` into a single word
fn do_tokenize_bracket<I>(mut input: I, mut pos: Position, buf: &mut Vec<Token>)
    -> LambdaResult<(I, Position)>
where I: Iterator<Item = char>
{
    use Token::*;
    let pos0 = pos;
    let mut word = String::new();
    loop {
        match input.next() {
            None => { return Err(UnterminatedSym(pos0.line, pos0.ch)); },
            Some(']') => {
                if word.is_empty() {
                    return Err(EmptySym(pos.line, pos.ch));
                } else {
                    buf.push(Word(take(&mut word)));
                }
                pos.ch += 1;
                return Ok((input, pos));
            },
            Some('\n') => { return Err(InvalidSym('\n', pos.line, pos.ch)); },
            Some(c) => {
                word.push(c);
                pos.ch += 1;
            },
        }
    }
}


fn do_tokenize_linecmt<I>(mut input: I, mut pos: Position)
    -> LambdaResult<(I, Position)>
where I: Iterator<Item = char>
{
    loop {
        match input.next() {
            None => { return Ok((input, pos)); },
            Some('\n') => {
                pos.ch = 0;
                pos.line += 1;
                return Ok((input, pos));
            },
            _ => { pos.ch += 1; },
        }
    }
}

fn do_tokenize_blkcmt<I>(mut input: I, mut pos: Position)
    -> LambdaResult<(I, Position)>
where I: Iterator<Item = char>
{
    loop {
        match input.next() {
            None => { return Ok((input, pos)); },
            Some('\n') => {
                pos.ch = 0;
                pos.line += 1;
            },
            Some('*') => match input.next() {
                Some('/') => {
                    pos.ch += 2;
                    return Ok((input, pos));
                },
                Some('\n') => {
                    pos.ch = 0;
                    pos.line += 1;
                },
                _ => { pos.ch += 2; },
            },
            _ => { pos.ch += 1; },
        }
    }
}

/// Parse a stream of [tokens][tokenize] into a [`Lambda`].
pub fn parse(tokens: &[Token]) -> LambdaResult<Lambda> {
    do_parse(tokens, false)
}

fn do_parse(tokens: &[Token], in_arg: bool) -> LambdaResult<Lambda> {
    match tokens.len() {
        0 => if in_arg { Err(MissingArg) } else { Ok(Lambda::Null) },
        1 => if in_arg {
            Err(InvalidFunc)
        } else {
            match &tokens[0] {
                Token::Null => Ok(Lambda::Null),
                Token::Lambda => Err(InvalidFunc), // shouldn't happen if calling on
                Token::Dot => Err(UnexpectedDot),  // output from `tokenize`
                Token::Word(sym) => Ok(Lambda::Sym((&**sym).into())),
                Token::SubExpr(expr) => do_parse(expr, false),
            }
        },
        _ => match &tokens[0] {
            Token::Null => {
                let f = Lambda::Null;
                let on = do_parse(&tokens[1..], false)?;
                Ok(Lambda::App(f.into(), on.into()))
            },
            Token::Lambda => if in_arg {
                Err(UnexpectedLambda)
            } else {
                let arg = do_parse(&tokens[1..], true)?;
                let Lambda::Sym(arg) = arg else { unreachable!() };
                // if arg parse is successful, `tokens` is at least 3 items long
                if tokens.len() > 3 {
                    let body = do_parse(&tokens[3..], false)?;
                    Ok(Lambda::Func(arg, body.into()))
                } else {
                    Err(MissingBody)
                }
            },
            Token::Dot => Err(if in_arg { InvalidFunc } else { UnexpectedDot }),
            Token::Word(sym) => if in_arg {
                // `tokens` is at least 2 items long
                match &tokens[1] {
                    Token::Null => Err(InvalidFunc),
                    Token::Lambda => Err(UnexpectedLambda),
                    Token::Dot => Ok(Lambda::Sym((&**sym).into())),
                    Token::Word(sym) => Err(UnexpectedSym(sym.clone())),
                    Token::SubExpr(_) => Err(InvalidFunc),
                }
            } else {
                let f = Lambda::Sym((&**sym).into());
                let on = do_parse(&tokens[1..], false)?;
                Ok(Lambda::App(f.into(), on.into()))
            },
            Token::SubExpr(expr) => if in_arg {
                Err(InvalidFunc)
            } else {
                let f = do_parse(expr, false)?;
                let on = do_parse(&tokens[1..], false)?;
                Ok(Lambda::App(f.into(), on.into()))
            },
        },
    }
}

