use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

pub trait ItemTrait: Debug + Hash + Clone + PartialEq + Eq {}

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
    start_symbol: N,
    parsing_table: HashMap<(N, Terminal<T>), Vec<Item<N, T>>>,
}
impl<N: ItemTrait, T: ItemTrait> Grammar<N, T> {
    pub fn new(productions: HashSet<Production<N, T>>, start_symbol: N) -> Option<Self> {
        let Some(parsing_table) = Self::compute_parsing_table(&productions, start_symbol.clone())
        else {
            return None;
        };

        Some(Self {
            parsing_table,
            start_symbol,
        })
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
            if Self::is_sequence_nullable(productions, already_computed, result.as_slice()) {
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
                if Self::is_sequence_nullable(productions, nullables, production.1.as_slice()) {
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

    fn compute_parsing_table(
        productions: &HashSet<Production<N, T>>,
        start_symbol: N,
    ) -> Option<HashMap<(N, Terminal<T>), Vec<Item<N, T>>>> {
        let mut result = HashMap::new();

        let nullables = Self::compute_nullables(productions);
        let firsts = Self::compute_firsts(productions, &nullables);
        let follows = Self::compute_follows(start_symbol.clone(), productions, &firsts);

        for Production(source, results) in productions {
            let production_firsts: HashSet<Terminal<T>> =
                Self::compute_sequence_firsts(results.as_slice(), &firsts);
            for first in &production_firsts {
                if first.clone() != Terminal::Epsilon {
                    result
                        .entry((source.clone(), first.clone()))
                        .or_insert_with(Vec::new);
                    result
                        .get_mut(&(source.clone(), first.clone()))
                        .unwrap()
                        .push(results.clone());
                } else if production_firsts.contains(&Terminal::Epsilon) {
                    for b in follows.get(source).cloned().unwrap_or_default() {
                        result
                            .entry((source.clone(), b.clone()))
                            .or_insert_with(Vec::new);
                        result
                            .get_mut(&(source.clone(), b.clone()))
                            .unwrap()
                            .push(results.clone());
                    }
                }
            }
        }

        let mut final_result = HashMap::new();
        dbg!(&result);
        for (key, mut value) in result.into_iter() {
            if value.len() > 1 {
                return None;
            }
            if let Some(value) = value.pop() {
                final_result.insert(key, value);
            }
        }

        Some(final_result)
    }

    fn compute_follows(
        start_symbol: N,
        productions: &HashSet<Production<N, T>>,
        firsts: &HashMap<N, HashSet<Terminal<T>>>,
    ) -> HashMap<N, HashSet<Terminal<T>>> {
        let mut result = HashMap::new();
        result.insert(start_symbol, HashSet::from_iter([Terminal::EndOfInput]));

        let mut changed = true;
        while changed {
            changed = false;

            for production in productions {
                for (i, item) in production.1.iter().enumerate() {
                    if let Item::NonTerminal(n) = item {
                        // if A = aB is a production, then FOLLOW(B) += FOLLOW(A)
                        if i == production.1.len() - 1
                            || match &production.1[i + 1] {
                                Item::NonTerminal(n) => firsts
                                    .get(n)
                                    .map(|firsts| firsts.contains(&Terminal::Epsilon))
                                    .unwrap_or(false),
                                Item::Terminal(_) => false,
                                Item::Epsilon => true,
                                Item::EndOfInput => false,
                            }
                        {
                            let follow_a = result.get(&production.0).cloned().unwrap_or_default();
                            if !result.contains_key(n) {
                                result.insert(n.clone(), HashSet::new());
                            }
                            if follow_a.iter().any(|x| !result.get(n).unwrap().contains(x)) {
                                changed = true;
                                result.get_mut(n).unwrap().extend(follow_a.into_iter());
                            }
                        }
                        if i != production.1.len() - 1 {
                            if !result.contains_key(n) {
                                result.insert(n.clone(), HashSet::new());
                            }
                            let firsts_following = match &production.1[i + 1] {
                                Item::NonTerminal(n) => firsts
                                    .get(n)
                                    .map(|x| {
                                        x.iter()
                                            .filter(|x| (*x).clone() != Terminal::<T>::Epsilon)
                                            .cloned()
                                            .collect::<Vec<_>>()
                                    })
                                    .unwrap_or_default(),
                                Item::Terminal(c) => vec![Terminal::Terminal(c.clone())],
                                Item::Epsilon => vec![],
                                Item::EndOfInput => vec![Terminal::EndOfInput],
                            };
                            if firsts_following
                                .iter()
                                .any(|x| !result.get(n).unwrap().contains(x))
                            {
                                changed = true;
                                result
                                    .get_mut(n)
                                    .unwrap()
                                    .extend(firsts_following.into_iter());
                            }
                        }
                    }
                }
            }
        }

        result
    }

    fn is_sequence_nullable(
        productions: &HashSet<Production<N, T>>,
        nullables: &HashMap<N, bool>,
        result: &[Item<N, T>],
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

    fn compute_sequence_firsts(
        sequence: &[Item<N, T>],
        first: &HashMap<N, HashSet<Terminal<T>>>,
    ) -> HashSet<Terminal<T>> {
        let mut results = HashSet::new();
        for item in sequence {
            match item {
                Item::NonTerminal(n) => {
                    let new_firsts = if let Some(new_firsts) = first.get(n) {
                        new_firsts.clone()
                    } else {
                        Self::compute_sequence_firsts(sequence, first)
                    };
                    let nullable = new_firsts.contains(&Terminal::Epsilon);
                    results.extend(new_firsts.into_iter());
                    if !nullable {
                        return results;
                    }
                }
                Item::Terminal(c) => {
                    results.insert(Terminal::Terminal(c.clone()));
                    return results;
                }
                Item::Epsilon => {
                    results.insert(Terminal::Epsilon);
                }
                Item::EndOfInput => {
                    results.insert(Terminal::EndOfInput);
                    return results;
                }
            }
        }
        results // NOTE: is this an error case?
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
        )
        .unwrap();
        dbg!("Created grammar!");

        assert_eq!(
            grammar.parsing_table,
            HashMap::from_iter([
                (
                    (Start, Terminal::Terminal(Identifier)),
                    vec![Item::NonTerminal(Expr), Item::EndOfInput]
                ),
                (
                    (Start, Terminal::Terminal(OpenParen)),
                    vec![Item::NonTerminal(Expr), Item::EndOfInput]
                ),
                (
                    (Expr, Terminal::Terminal(Identifier)),
                    vec![Item::NonTerminal(Term), Item::NonTerminal(ExprPrime)],
                ),
                (
                    (Expr, Terminal::Terminal(OpenParen)),
                    vec![Item::NonTerminal(Term), Item::NonTerminal(ExprPrime)],
                ),
                (
                    (ExprPrime, Terminal::Terminal(Plus)),
                    vec![
                        Item::Terminal(Plus),
                        Item::NonTerminal(Term),
                        Item::NonTerminal(ExprPrime)
                    ],
                ),
                (
                    (ExprPrime, Terminal::Terminal(CloseParen)),
                    vec![Item::Epsilon]
                ),
                ((ExprPrime, Terminal::EndOfInput), vec![Item::Epsilon]),
                (
                    (TermPrime, Terminal::Terminal(CloseParen)),
                    vec![Item::Epsilon]
                ),
                ((TermPrime, Terminal::Terminal(Plus)), vec![Item::Epsilon]),
                ((TermPrime, Terminal::EndOfInput), vec![Item::Epsilon]),
                (
                    (Term, Terminal::Terminal(Identifier)),
                    vec![Item::NonTerminal(Factor), Item::NonTerminal(TermPrime)]
                ),
                (
                    (Term, Terminal::Terminal(OpenParen)),
                    vec![Item::NonTerminal(Factor), Item::NonTerminal(TermPrime)]
                ),
                (
                    (TermPrime, Terminal::Terminal(Star)),
                    vec![
                        Item::Terminal(Star),
                        Item::NonTerminal(Factor),
                        Item::NonTerminal(TermPrime)
                    ]
                ),
                (
                    (Factor, Terminal::Terminal(Identifier)),
                    vec![Item::Terminal(Identifier),]
                ),
                (
                    (Factor, Terminal::Terminal(OpenParen)),
                    vec![
                        Item::Terminal(OpenParen),
                        Item::NonTerminal(Expr),
                        Item::Terminal(CloseParen)
                    ]
                ),
            ]),
        )

        /*assert_eq!(
            grammar.nullable,
            HashMap::from_iter([
                (ExprPrime, true),
                (TermPrime, true),
                (Term, false),
                (Expr, false),
                (Factor, false),
                (Start, false)
            ])
        );*/

        /*assert_eq!(
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
        );*/

        /*assert_eq!(
            grammar.follows,
            HashMap::from_iter([
                (Start, HashSet::from_iter([Terminal::EndOfInput])),
                (
                    Expr,
                    HashSet::from_iter([Terminal::Terminal(CloseParen), Terminal::EndOfInput])
                ),
                (
                    ExprPrime,
                    HashSet::from_iter([Terminal::Terminal(CloseParen), Terminal::EndOfInput])
                ),
                (
                    Term,
                    HashSet::from_iter([
                        Terminal::Terminal(Plus),
                        Terminal::Terminal(CloseParen),
                        Terminal::EndOfInput
                    ])
                ),
                (
                    TermPrime,
                    HashSet::from_iter([
                        Terminal::Terminal(Plus),
                        Terminal::Terminal(CloseParen),
                        Terminal::EndOfInput
                    ])
                ),
                (
                    Factor,
                    HashSet::from_iter([
                        Terminal::Terminal(Plus),
                        Terminal::Terminal(Star),
                        Terminal::Terminal(CloseParen),
                        Terminal::EndOfInput
                    ])
                ),
            ])
        )*/
    }
}
