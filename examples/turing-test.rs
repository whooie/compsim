use compsim::turing::*;

fn main() {
    let mut sim = Turing::default();
    // let program = parse(",>,[-<+>]<.".chars()).expect("error parsing");
    let program = parse(
        "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>:>---:+++++++::+++:\
        >>:<-:<:+++:------:--------:>>+:>++:"
        .chars()
    ).expect("error parsing");
    let out = sim.run(&program, false).expect("error running");
    println!("{:?}", out);
}
