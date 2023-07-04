use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammar.peg"]
pub struct WhispParser;

#[cfg(test)]
mod tests {
    use pest::iterators::Pairs;

    use super::*;

    const SAMPLE1: &str = include_str!("../examples/git_aliases.whisp");

    fn print_tree(pairs: Pairs<'_, Rule>, indent: usize) {
        for pair in pairs {
            let rule = format!("{:?}", pair.as_rule());
            let text = pair.as_str();
            for _ in 0..indent {
                print!("  ");
            }
            print!("\x1b[34;1m{rule}\x1b[0m");
            for _ in 0..(32 - indent * 2 - rule.len()) {
                print!(" ");
            }
            println!("{text}");
            print_tree(pair.into_inner(), indent + 1);
        }
    }

    fn parse(rule: Rule, code: &str) {
        match WhispParser::parse(rule, code.trim()) {
            Ok(pairs) => print_tree(pairs, 0),
            Err(e) => {
                eprintln!("{e}");
                panic!();
            }
        }
    }

    #[test]
    fn test_string() {
        parse(Rule::string, r#""string""#);
        parse(Rule::string, r#""another string""#);
        parse(Rule::string, r#"another_string"#);
        parse(Rule::string, r#"another_string!_no,-seriously"#);
    }

    #[test]
    fn test_single_statement() {
        parse(Rule::statement, r#"cur_branch"#);
        parse(Rule::statement, r#" cur_branch "#);
        parse(Rule::statement, r#"run git checkout main"#);
        parse(Rule::statement, r#" run git checkout main "#);
    }

    #[test]
    fn test_statement_block() {
        // Non-terminal function call statement on a single line
        parse(Rule::statement_block, r#"{cur_branch;}"#);
        parse(Rule::statement_block, r#"{run git checkout main;}"#);
        parse(Rule::statement_block, r#"{ cur_branch; }"#);
        parse(Rule::statement_block, r#"{ run git checkout main; }"#);
        // Single terminal function call statements on a single line
        parse(Rule::statement_block, r#"{cur_branch}"#);
        parse(Rule::statement_block, r#"{run git checkout main}"#);
        parse(Rule::statement_block, r#"{ run git checkout main }"#);
        parse(Rule::statement_block, r#"{ cur_branch }"#);
    }

    #[test]
    fn test_load_grammar() {
        let res = WhispParser::parse(Rule::program, SAMPLE1);
        println!("{res:#?}");
    }
}
