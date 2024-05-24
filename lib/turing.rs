//! Turing machine simulator, following a modified spec of the
//! [Brainfuck][brainfuck] language.
//!
//! Here is the list of allowed symbols:
//! - `<`, `>`: Move the data pointer left/right by one spot.
//! - `+`, `-`: Increment/decrement the cell under the data pointer by one,
//! wrapping at byte boundaries.
//! - `[`: If the cell under the data pointer is `0`, jump to the accompanying
//! `]`, otherwise move to the next command.
//! - `]`: If the cell under the data pointer is not `0`, jump to the
//! accompanying `[`, otherwise move to the next command.
//! - `.`: Output the value of the byte under the data pointer.
//! - `,`: Read one number `0..=255` from STDIN and write it to the cell under
//! the data pointer.
//! - `:`: Output the value of the byte under the data pointer as a [`char`].
//! - `;`: Read one [`char`] equivalent to a number `0..=255` from STDIN and
//! write it to the cell under the data pointer.
//! - `//`: Indicates a comment lasting until the next newline character.
//! - `/*`: Indicates a comment lasting until the next `*/`.
//!
//! [brainfuck]: https://en.wikipedia.org/wiki/Brainfuck

use std::{
    collections::HashMap,
    io,
    str::FromStr,
};
use thiserror::Error;
use crate::{ print_flush, println_flush };

#[derive(Debug, Error)]
pub enum TuringError {
    #[error("cannot write char to cell: {0}")]
    InvalidChar(#[from] std::char::TryFromCharError),

    #[error("error while parsing: invalid character {0} at line {1}, char {2}")]
    InvalidParse(char, usize, usize),

    #[error("error while parsing: invalid loop terminator at line {0}, char {1}")]
    InvalidLoopEnd(usize, usize),

    #[error("error while parsing: unterminated loop beginning at line {0}, char {1}")]
    UnterminatedLoop(usize, usize),

    #[error("invalid byte write input: must be an integer [0, 255]")]
    InvalidByteInput,

    #[error("invalid char write input: must fit into a u8")]
    InvalidCharInput,

    #[error("i/o error: {0}")]
    IOError(#[from] io::Error),
}
pub type TuringResult<T> = Result<T, TuringError>;

/// Turing machine simulator.
///
/// Negative pointer positions are allowed, and cell increments/decrements wrap.
#[derive(Clone, Debug)]
pub struct Turing {
    /// The current location of the data pointer.
    pub ptr: isize,
    /// The current values of all cells. New cells are allocated only when the
    /// data pointer moves to them.
    pub cells: HashMap<isize, u8>,
}

impl Default for Turing {
    fn default() -> Self { Self::new() }
}

impl Turing {
    /// Create a new simulator, initialized with all-zeroed cells and the
    /// pointer located at position zero.
    pub fn new() -> Self {
        Self { ptr: 0, cells: [(0, 0)].into_iter().collect() }
    }

    /// Move the pointer one position to the right.
    pub fn move_r(&mut self) -> &mut Self {
        self.ptr += 1;
        self.cells.entry(self.ptr).or_insert(0);
        self
    }

    /// Move the pointer one position to the left.
    pub fn move_l(&mut self) -> &mut Self {
        self.ptr -= 1;
        self.cells.entry(self.ptr).or_insert(0);
        self
    }

    /// Increment the current cell by one.
    pub fn inc(&mut self) -> &mut Self {
        if let Some(c) = self.cells.get_mut(&self.ptr) {
            *c = c.wrapping_add(1);
        } else {
            unreachable!()
        }
        self
    }

    /// Decrement the current cell by one.
    pub fn dec(&mut self) -> &mut Self {
        if let Some(c) = self.cells.get_mut(&self.ptr) {
            *c = c.wrapping_sub(1);
        } else {
            unreachable!()
        }
        self
    }

    /// Read from the current cell.
    pub fn read(&self) -> u8 {
        self.cells[&self.ptr]
    }

    /// Write to the current cell.
    pub fn write(&mut self, b: u8) -> &mut Self {
        if let Some(c) = self.cells.get_mut(&self.ptr) {
            *c = b;
        } else {
            unreachable!()
        }
        self
    }

    /// Read the current cell as a [`char`].
    pub fn read_char(&self) -> char {
        self.cells[&self.ptr].into()
    }

    /// Write a [`char`] to the current cell.
    pub fn write_char(&mut self, ch: char) -> TuringResult<&mut Self> {
        if let Some(c) = self.cells.get_mut(&self.ptr) {
            *c = ch.try_into()?;
        } else {
            unreachable!()
        }
        Ok(self)
    }

    /// Run a program.
    ///
    /// Setting `live_output = true` allows output from `.`/`:` to be printed
    /// during the execution of the program, with newline appended.
    pub fn run<'a, I>(&mut self, program: I, live_output: bool)
        -> TuringResult<Vec<Output>>
    where I: IntoIterator<Item = &'a Action>
    {
        let mut output: Vec<Output> = Vec::new();
        program.into_iter()
            .try_for_each(|a| {
                self.run_action(a, live_output, &mut output)
                    .map(|_| ())
        })?;
        Ok(output)
    }

    fn run_action(
        &mut self,
        action: &Action,
        live_output: bool,
        output: &mut Vec<Output>,
    ) -> TuringResult<&mut Self>
    {
        match action {
            Action::MoveL => Ok(self.move_l()),
            Action::MoveR => Ok(self.move_r()),
            Action::Inc => Ok(self.inc()),
            Action::Dec => Ok(self.dec()),
            Action::Read => {
                let out = Output::Byte(self.read());
                if live_output {
                    println_flush!("output byte: {}", out);
                }
                output.push(out);
                Ok(self)
            },
            Action::Write => {
                print_flush!("input byte: ");
                let b = try_read_byte()?;
                Ok(self.write(b))
            },
            Action::ReadChar => {
                let out = Output::Char(self.read_char());
                if live_output {
                    println_flush!("output char: {}", out);
                }
                output.push(out);
                Ok(self)
            },
            Action::WriteChar => {
                print_flush!("input char: ");
                let c = try_read_char()?;
                self.write_char(c)
            },
            Action::Loop(l) => self.run_loop(l, live_output, output),
        }
    }

    fn run_loop(
        &mut self,
        program: &[Action],
        live_output: bool,
        output: &mut Vec<Output>,
    ) -> TuringResult<&mut Self>
    {
        while self.read() != 0 {
            for a in program.iter() {
                self.run_action(a, live_output, output)?;
            }
        }
        Ok(self)
    }

}

fn try_read_byte() -> TuringResult<u8> {
    let mut buf = String::new();
    io::stdin().read_line(&mut buf)?;
    u8::from_str(buf.trim()).map_err(|_| TuringError::InvalidByteInput)
}

fn try_read_char() -> TuringResult<char> {
    let mut buf = String::new();
    io::stdin().read_line(&mut buf)?;
    char::from_str(buf.trim()).map_err(|_| TuringError::InvalidCharInput)
}

/// Output from a program.
#[derive(Copy, Clone, Debug)]
pub enum Output {
    Byte(u8),
    Char(char),
}

impl std::fmt::Display for Output {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::Byte(b) => b.fmt(f),
            Self::Char(c) => c.fmt(f),
        }
    }
}

/// Syntax tree for a program.
#[derive(Clone, Debug)]
pub enum Action {
    MoveL,
    MoveR,
    Inc,
    Dec,
    Read,
    Write,
    ReadChar,
    WriteChar,
    Loop(Vec<Action>),
}

/// A `Program` is a sequence of [`Action`]s.
pub type Program = Vec<Action>;

#[derive(Copy, Clone, Debug)]
struct Position { line: usize, ch: usize }

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum ParserState {
    Normal,
    InLoop,
    LineComment,
    BlockComment,
}

/// Parse a stream of [`char`]s into a [`Program`].
pub fn parse<I>(input: I) -> TuringResult<Program>
where I: IntoIterator<Item = char>
{
    let mut program: Program = Vec::new();
    do_parse(
        input.into_iter(),
        ParserState::Normal,
        Position { line: 0, ch: 0 },
        &mut program,
    )?;
    Ok(program)
}

fn do_parse<I>(
    mut input: I,
    state: ParserState,
    pos: Position,
    buf: &mut Vec<Action>,
) -> TuringResult<(I, Position)>
where I: Iterator<Item = char>
{
    use ParserState::*;
    let mut cur = pos;
    loop {
        match input.next() {
            None => match state {
                Normal | LineComment | BlockComment => {
                    return Ok((input, cur));
                },
                InLoop => {
                    return Err(TuringError::UnterminatedLoop(pos.line, pos.ch));
                },
            },
            Some('<') => {
                match state {
                    Normal | InLoop => { buf.push(Action::MoveL); },
                    _ => { },
                }
                cur.ch += 1;
            },
            Some('>') => {
                match state {
                    Normal | InLoop => { buf.push(Action::MoveR); },
                    _ => { },
                }
                cur.ch += 1;
            },
            Some('+') => {
                match state {
                    Normal | InLoop => { buf.push(Action::Inc); },
                    _ => { },
                }
                cur.ch += 1;
            },
            Some('-') => {
                match state {
                    Normal | InLoop => { buf.push(Action::Dec); },
                    _ => { },
                }
                cur.ch += 1;
            },
            Some('.') => {
                match state {
                    Normal | InLoop => { buf.push(Action::Read); },
                    _ => { },
                }
                cur.ch += 1;
            },
            Some(',') => {
                match state {
                    Normal | InLoop => { buf.push(Action::Write); },
                    _ => { },
                }
                cur.ch += 1;
            },
            Some(':') => {
                match state {
                    Normal | InLoop => { buf.push(Action::ReadChar); },
                    _ => { },
                }
                cur.ch += 1;
            },
            Some(';') => {
                match state {
                    Normal | InLoop => { buf.push(Action::WriteChar); },
                    _ => { },
                }
                cur.ch += 1;
            },
            Some('[') => match state {
                Normal | InLoop => {
                    let mut loop_buf: Program = Vec::new();
                    let rec = do_parse(input, InLoop, cur, &mut loop_buf)?;
                    cur = rec.1;
                    input = rec.0;
                    buf.push(Action::Loop(loop_buf));
                },
                _ => { cur.ch += 1; },
            },
            Some(']') => match state {
                Normal => {
                    return Err(TuringError::InvalidLoopEnd(cur.line, cur.ch));
                },
                InLoop => {
                    cur.ch += 1;
                    return Ok((input, cur));
                },
                _ => {
                    cur.ch += 1;
                },
            },
            Some(' ') => {
                cur.ch += 1;
            },
            Some('\n') => {
                cur.ch = 0;
                cur.line += 1;
                if state == LineComment {
                    return Ok((input, cur));
                }
            },
            Some('/') => match input.next() {
                Some('/') => {
                    cur.ch += 2;
                    let rec = do_parse(input, LineComment, cur, buf)?;
                    cur = rec.1;
                    input = rec.0;
                },
                Some('*') => {
                    cur.ch += 2;
                    let rec = do_parse(input, BlockComment, cur, buf)?;
                    cur = rec.1;
                    input = rec.0;
                },
                _ => {
                    return Err(
                        TuringError::InvalidParse('/', cur.line, cur.ch)
                    );
                },
            },
            Some('*') => match input.next() {
                Some('/') => {
                    cur.ch += 2;
                    return Ok((input, cur));
                },
                _ => {
                    return Err(
                        TuringError::InvalidParse('*', cur.line, cur.ch)
                    );
                },
            },
            Some(d) => match state {
                LineComment | BlockComment => {
                    cur.ch += 1;
                },
                _ => {
                    return Err(TuringError::InvalidParse(d, cur.line, cur.ch));
                },
            },
        }
    }
}



