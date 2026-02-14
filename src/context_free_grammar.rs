use std::collections::{HashMap, HashSet};
use std::hash::Hash;

pub trait ItemTrait: Hash + Clone + PartialEq + Eq {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Item<N: ItemTrait, T: ItemTrait> {
    NonTerminal(N),
    Terminal(T),
    Epsilon,
    EndOfInput,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Terminal<T: ItemTrait> {
    Terminal(T),
    Epsilon,
    EndOfInput,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Production<N: ItemTrait, T: ItemTrait>(pub N, pub Vec<Item<N, T>>);

pub struct Grammar<N: ItemTrait, T: ItemTrait> {
    nullable: HashMap<N, bool>, // because we know that all terminals are non-nullable anyway,
    // except epsilon
    first: HashMap<N, HashSet<Terminal<T>>>,
    productions: HashSet<Production<N, T>>,
    start_symbol: N,
}
impl<N: ItemTrait, T: ItemTrait> Grammar<N, T> {
    pub fn new(productions: HashSet<Production<N, T>>, start_symbol: N) -> Self {
        let nullables = Self::compute_nullables(&productions);
        let first = Self::compute_firsts(&productions, &nullables);

        Self {
            nullable: nullables,
            first,
            productions,
            start_symbol,
        }
    }

    fn compute_nullables(productions: &HashSet<Production<N, T>>) -> HashMap<N, bool> {
        let mut computed: HashMap<N, bool> = HashMap::new();
        for nonterminal in productions.iter().map(|x| x.0.clone()) {
            if !computed.contains_key(&nonterminal) {
                let nullability =
                    Self::compute_non_terminal_nullability(productions, &nonterminal, &computed);
                computed.insert(nonterminal, nullability);
            }
        }
        computed
    }

    fn compute_non_terminal_nullability(
        productions: &HashSet<Production<N, T>>,
        nonterminal: &N,
        already_computed: &HashMap<N, bool>,
    ) -> bool {
        for result in productions
            .iter()
            .filter(|prod| &prod.0 == nonterminal)
            .map(|Production(_, result)| result)
        {
            if Self::is_sequence_nullable(productions, already_computed, result) {
                return true;
            }
        }
        false
    }

    fn compute_firsts(
        productions: &HashSet<Production<N, T>>,
        nullables: &HashMap<N, bool>,
    ) -> HashMap<N, HashSet<Terminal<T>>> {
        let mut result: HashMap<N, HashSet<Terminal<T>>> = HashMap::new();
        let mut changed = true;
        while changed {
            changed = false;
            for production in productions {
                if Self::is_sequence_nullable(productions, nullables, &production.1) {
                    changed = changed
                        || if result.contains_key(&production.0) {
                            result
                                .get_mut(&production.0)
                                .unwrap()
                                .insert(Terminal::Epsilon)
                        } else {
                            result.insert(
                                production.0.clone(),
                                HashSet::from_iter([Terminal::Epsilon]),
                            );
                            true
                        };
                }
                for item in &production.1 {
                    // get FIRST(item)
                    // NOTE: there's got to be a simple way of doing this without cloning
                    let mut firsts = match item {
                        Item::NonTerminal(n) => result.get(n).cloned().unwrap_or_default(),
                        Item::Terminal(x) => HashSet::from_iter([Terminal::Terminal(x.clone())]),
                        Item::Epsilon => HashSet::from_iter([Terminal::Epsilon]),
                        Item::EndOfInput => HashSet::from_iter([Terminal::EndOfInput]),
                    };
                    // add that (but not epsilon!) to `result`
                    let nullable = firsts.remove(&Terminal::Epsilon);
                    for first in firsts {
                        changed = changed
                            || if result.contains_key(&production.0) {
                                result.get_mut(&production.0).unwrap().insert(first)
                            } else {
                                result.insert(production.0.clone(), HashSet::from_iter([first]));
                                true
                            }
                    }
                    // if epsilon was not in FIRST(item) (i.e. if `item` is NOT nullable) then
                    if !nullable {
                        break;
                    }
                }
            }
        }
        result
    }
    fn is_sequence_nullable(
        productions: &HashSet<Production<N, T>>,
        nullables: &HashMap<N, bool>,
        result: &Vec<Item<N, T>>,
    ) -> bool {
        result.iter().all(|item| match item {
            Item::EndOfInput => false,
            Item::Epsilon => true,
            Item::Terminal(_) => false,
            Item::NonTerminal(n) => {
                if let Some(x) = nullables.get(n) {
                    *x
                } else {
                    Self::compute_non_terminal_nullability(productions, n, nullables)
                }
            }
        })
    }
}

#[macro_export]
macro_rules! item {
    (t $value:expr) => {
        Item::Terminal($value)
    };
    (n $value:expr) => {
        Item::NonTerminal($value)
    };
}

#[macro_export]
macro_rules! nterm {
    ($value:expr) => {
        item!(n $value)
    }
}

#[macro_export]
macro_rules! term {
    ($value:expr) => {
        item!(t $value)
    }
}

#[macro_export]
macro_rules! production {
    ($start:expr => $($result:expr),+) => {
        Production($start, vec![$($result),+])
    };

    ($start:expr => $($($result:expr),+);+) => {
        [$(production!($start => $($result),+)),+]
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use lexer::TokenType;
    impl ItemTrait for TokenType {}

    use crate::context_free_grammar::{Item, ItemTrait, Production, Terminal};

    use super::Grammar;

    #[test]
    fn create_grammar() {
        #[derive(Debug, Clone, Hash, PartialEq, Eq)]
        enum NonTerminal {
            Expr,
            ExprPrime,
            Term,
            TermPrime,
            Factor,
            Start,
        }
        impl ItemTrait for NonTerminal {}

        use NonTerminal::*;
        use TokenType::*;

        dbg!("Starting!");
        let grammar = Grammar::new(
            HashSet::from_iter([
                production!(Start => nterm!(Expr), Item::EndOfInput),
                production!(Expr => nterm!(Term), nterm!(ExprPrime)),
                production!(ExprPrime => term!(Plus), nterm!(Term), nterm!(ExprPrime)),
                production!(ExprPrime => Item::Epsilon),
                production!(Term => nterm!(Factor), nterm!(TermPrime)),
                production!(TermPrime => term!(Star), nterm!(Factor), nterm!(TermPrime)),
                production!(TermPrime => Item::Epsilon),
                production!(Factor => term!(OpenParen), nterm!(Expr), term!(CloseParen)),
                production!(Factor => term!(Identifier)),
            ]),
            NonTerminal::Start,
        );
        dbg!("Created grammar!");

        assert_eq!(
            grammar.nullable,
            HashMap::from_iter([
                (ExprPrime, true),
                (TermPrime, true),
                (Term, false),
                (Expr, false),
                (Factor, false),
                (Start, false)
            ])
        );

        assert_eq!(
            grammar.first,
            HashMap::from_iter([
                (
                    Start,
                    HashSet::from_iter([
                        Terminal::Terminal(OpenParen),
                        Terminal::Terminal(Identifier)
                    ])
                ),
                (
                    Expr,
                    HashSet::from_iter([
                        Terminal::Terminal(OpenParen),
                        Terminal::Terminal(Identifier)
                    ])
                ),
                (
                    ExprPrime,
                    HashSet::from_iter([Terminal::Terminal(Plus), Terminal::Epsilon])
                ),
                (
                    Term,
                    HashSet::from_iter([
                        Terminal::Terminal(Identifier),
                        Terminal::Terminal(OpenParen),
                    ])
                ),
                (
                    TermPrime,
                    HashSet::from_iter([Terminal::Terminal(Star), Terminal::Epsilon])
                ),
                (
                    Factor,
                    HashSet::from_iter([
                        Terminal::Terminal(OpenParen),
                        Terminal::Terminal(Identifier),
                    ])
                ),
            ])
        )
    }
}
