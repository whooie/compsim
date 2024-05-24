use compsim::church::*;

fn main() -> anyhow::Result<()> {
    // let mut term = Lambda::app(Lambda::func('x', Lambda::sym('x')), 'y'.into());
    // println!("{}", term);
    // term.reduce();
    // println!("{}", term);

    // let tokens = tokenize(r"\f.\x.f x".chars())?;
    let tokens = tokenize(r"(λf.(λx.(f x)))".chars())?;
    // println!("{:?}", tokens);

    // let tokens = vec![
    //     Token::SubExpr(vec![
    //         // Token::Lambda,
    //         // Token::Word("x".to_string()),
    //         // Token::Dot,
    //         Token::Word("x".to_string()),
    //         Token::Word("y".to_string()),
    //         Token::Word("z".to_string()),
    //     ])
    // ];
    let term = parse(&tokens)?;
    println!("{}", term);

    Ok(())
}
