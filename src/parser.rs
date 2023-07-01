use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammar.peg"]
pub struct WhispParser;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_load_grammar() {}
}
