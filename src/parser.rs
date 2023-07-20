use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct WhispParser;

#[cfg(test)]
mod tests {
    use pest::iterators::Pairs;
    use pest::Parser;

    use super::*;

    const SAMPLE1: &str = include_str!("../examples/git_aliases.whisp");

    fn print_tree(pairs: Pairs<'_, Rule>, indent: usize) {
        for pair in pairs {
            let rule = format!("{:?}", pair.as_rule());
            let text = {
                let text = pair.as_str();
                if text.contains('\n') {
                    format!("{}...", text.lines().next().unwrap())
                } else {
                    text.to_string()
                }
            };

            for _ in 0..indent {
                print!("  ");
            }
            print!("\x1b[34;1m{rule}\x1b[0m");
            let columns = rule.len() + indent * 2;
            for _ in 0..(32usize.saturating_sub(columns)) {
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
                panic!("Parser errored unexpectedly:\n\x1b[31;1m{e}\x1b[0m");
            },
        }
    }

    fn fail(rule: Rule, code: &str) {
        match WhispParser::parse(rule, code.trim()) {
            Ok(pairs) => {
                print_tree(pairs, 0);
                panic!("This shouldn't have parsed!\n\x1b[33;1m{}\x1b[0m", code.trim());
            },
            Err(e) => {
                println!("Parser errored as expected:\n\x1b[32;1m{e}\x1b[0m");
            },
        }
    }

    #[test]
    fn test_string() {
        parse(Rule::quoted_string, r#""string""#);
        parse(Rule::quoted_string, r#""another string""#);
        parse(Rule::unquoted_string, r#"another_string"#);
        parse(Rule::unquoted_string, r#"another_string!_no,-seriously"#);
        parse(Rule::raw_quoted_string, "r#\"I am a raw string!!!{};\"#");
    }

    #[test]
    fn test_expression() {
        parse(Rule::expression, r#"cur_branch"#);
        parse(Rule::expression, r#" cur_branch "#);
        parse(Rule::expression, r#"(cur_branch)"#);
        parse(Rule::expression, r#"run git checkout main"#);
        parse(Rule::expression, r#" run git checkout main "#);
        parse(Rule::expression, r#"(run git checkout main)"#);
    }

    #[test]
    fn test_lexical_declaration() {
        fail(Rule::lexical_declaration, "letfoo=bar");
        fail(Rule::lexical_declaration, "letfoo = bar");
        fail(Rule::lexical_declaration, r#"let foo = let bar = baz;"#);
        fail(Rule::lexical_declaration, r#"let foo = fn bar() {}"#);
        parse(Rule::lexical_declaration, "let foo = bar;");
        parse(Rule::lexical_declaration, "let foo=bar;");
        parse(Rule::lexical_declaration, r#"let foo = "string";"#);
        parse(Rule::lexical_declaration, r#"let foo = (run git diff main..);"#);
        parse(Rule::lexical_declaration, r#"let foo = { bar; foo };"#);
        parse(Rule::lexical_declaration, r#"let foo = { bar; foo ;};"#);
        parse(Rule::lexical_declaration, r#"let foo = { bar; foo; };"#);
    }

    #[test]
    fn test_function_call() {
        parse(Rule::function_call, r#"print Ciao, come stai?"#);
        parse(Rule::function_call, r#"run git checkout { cur_branch }"#);
        parse(Rule::function_call, r#"run git "checkout" { cur_branch }"#);
        parse(Rule::function_call, "run git r#\"checkout\"# { cur_branch }");
    }

    #[test]
    fn test_statement_block() {
        parse(Rule::statement_block, r#"{cur_branch;}"#);
        parse(Rule::statement_block, r#"{run git checkout main;}"#);
        parse(Rule::statement_block, r#"{ cur_branch; }"#);
        parse(Rule::statement_block, r#"{ run git checkout main; }"#);
        parse(Rule::statement_block, r#"{cur_branch}"#);
        parse(Rule::statement_block, r#"{run git checkout main}"#);
        parse(Rule::statement_block, r#"{ run git checkout main }"#);
        parse(Rule::statement_block, r#"{ cur_branch }"#);
        parse(Rule::statement_block, r#"{ fn foo() {} }"#);
        parse(Rule::statement_block, r#"{ fn foo() {} fn bar() {} foo; bar }"#);
        parse(Rule::statement_block, r#"{ fn foo() {} fn bar() {} foo; (bar) }"#);
    }

    #[test]
    fn test_formal_parameters() {
        parse(Rule::formal_parameters, r#"()"#);
        parse(Rule::formal_parameters, r#"(foo)"#);
        parse(Rule::formal_parameters, r#"(foo,)"#);
        parse(Rule::formal_parameters, r#"( foo, )"#);
        parse(Rule::formal_parameters, r#"(foo, bar, baz)"#);
        parse(Rule::formal_parameters, r#"(foo, bar, baz,)"#);
    }

    #[test]
    fn test_function_declaration() {
        fail(Rule::function_declaration, "fnfoo(){}");
        parse(Rule::function_declaration, "fn foo(){}");
        parse(Rule::function_declaration, "fn foo() {}");
        parse(Rule::function_declaration, "fn foo ( ) {}");
        fail(
            Rule::function_declaration,
            r#"
            fn grom() {
              fn gpm;
              fn gpm
            }
            "#,
        );
        parse(
            Rule::function_declaration,
            r#"
            fn grom() {
              fn other_fn() {
                  foo;
              }

              run git rebase origin main;
            }
            "#,
        );
        parse(
            Rule::function_declaration,
            r#"
            fn grom() {
              gpm;

              fn other_fn() {
                  foo;
              }

              run git rebase origin main;
            }
            "#,
        );
    }

    #[test]
    fn test_if_expr() {
        parse(
            Rule::if_expr,
            r#"
            if (run program1) {
                run program2
            }
            "#,
        );
        parse(
            Rule::if_expr,
            r#"
            if (run program1) {
                run program2
            } else {
                run program3
            }
            "#,
        );
        parse(
            Rule::if_expr,
            r#"
            if (run program1) {
                run program2
            } else if (run program3) {
                run program4
            } else {
                run program5
            }
            "#,
        );
        fail(
            Rule::statement_block,
            r#"
            {
                if (run program1) {
                    run program2
                } else {
                    run program4
                } else if (run program2) {
                    run program5
                }
            }
            "#,
        );
    }

    #[test]
    fn test_loop() {
        parse(
            Rule::loop_expr,
            r#"
            loop {
                run program3;
                break;
                break foo;
            }
            "#,
        );
        parse(Rule::loop_expr, "loop { break }");
        parse(Rule::loop_expr, "loop { break; }");
        parse(Rule::loop_expr, "loop { break foo }");
        parse(Rule::loop_expr, "loop { break foo; }");
    }

    #[test]
    fn test_program() {
        parse(Rule::program, SAMPLE1);
    }
}
