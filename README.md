# compsim

Minimal simulators for various fundamental systems in computing theory.

## Turing machines

```shell
cargo install brainfuck
```

This is a small implementation of Brainfuck, slightly modified to interpret
bytes as string characters and to support comments.
- `<`, `>`: Move the data pointer left/right by one spot.
- `+`, `-`: Increment/decrement the cell under the data pointer by one,
  wrapping at byte boundaries.
- `[`: If the cell under the data pointer is `0`, jump to the accompanying
  `]`, otherwise move to the next command.
- `]`: If the cell under the data pointer is not `0`, jump to the
  accompanying `[`, otherwise move to the next command.
- `.`: Output the value of the byte under the data pointer.
- `,`: Read one number `0..=255` from STDIN and write it to the cell under
  the data pointer.
- `:`: Output the value of the byte under the data pointer as a [`char`].
- `;`: Read one [`char`] equivalent to a number `0..=255` from STDIN and
  write it to the cell under the data pointer.
- `//`: Indicates a comment lasting until the next newline character.
- `/*`: Indicates a comment lasting until the next `*/`.

```shell
$ brainfuck --help
```
```
Turing machine simulator

Usage: brainfuck [OPTIONS] [FILE]

Arguments:
  [FILE]  Run a file as a script. Overridden by `-c`

Options:
  -c, --command <COMMAND>  Pass a program as a string
  -q, --quiet              Silence live output from the program, instead printing all output at the end
  -h, --help               Print help
  -V, --version            Print version
```

## The lambda calculus

```shell
cargo install lambda
```

This is a program that β-reduces expressions. If you don't want to type the `λ`
character all the time, it also supports `\` to denote functions, and allows for
symbols of arbitrary length. Symbols can contain any character except for
newline if enclosed in `[` brackets `]`. Also supports comments.

```shell
$ lambda --help
```
```
Performs β-reduction on λ-terms

Usage: lambda [OPTIONS] [FILE]

Arguments:
  [FILE]  Evaluate the contents of a file. Overridden by `-c`

Options:
  -c, --command <COMMAND>  Pass an expression as a string
  -h, --help               Print help
  -V, --version            Print version
```

