#![allow(dead_code)]

//! Simulators for various fundamental systems in computing theory.

/// Call `print!` and immediately flush.
#[macro_export]
macro_rules! print_flush {
    ( $fmt:literal $(, $val:expr )* $(,)?) => {
        print!($fmt $(, $val )*);
        std::io::Write::flush(&mut std::io::stdout()).unwrap();
    }
}

/// Call `println!` and immediately flush.
#[macro_export]
macro_rules! println_flush {
    ( $fmt:literal $(, $val:expr )* $(,)?) => {
        println!($fmt $(, $val, )*);
        std::io::Write::flush(&mut std::io::stdout()).unwrap();
    }
}

pub mod turing;
pub mod church;

