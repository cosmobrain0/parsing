use std::collections::{HashMap, HashSet};

use super::{Item, ItemTrait, Production, Terminal};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Lr0Item<N: ItemTrait, T: ItemTrait> {
    pub nonterminal: N,
    pub parsed: Vec<Item<N, T>>,
    pub potential: Vec<Item<N, T>>,
}
impl<N: ItemTrait, T: ItemTrait> Lr0Item<N, T> {
    fn from_production(production: &Production<N, T>) -> Vec<Self> {
        (0..=production.1.len())
            .map(|i| {
                (
                    production.1.iter().take(i).cloned().collect(),
                    production.1.iter().skip(i).cloned().collect(),
                )
            })
            .map(|(parsed, potential)| Self {
                nonterminal: production.0.clone(),
                parsed,
                potential,
            })
            .collect()
    }

    fn find_shifted_item(original_item: &Lr0Item<N, T>, items: &[Lr0Item<N, T>]) -> Lr0ItemIndex {
        let mut want_to_find = original_item.clone();
        want_to_find.parsed.push(want_to_find.potential.remove(0));
        Lr0ItemIndex(
            items
                .iter()
                .enumerate()
                .find_map(|(i, x)| (x == &want_to_find).then_some(i))
                .unwrap(),
        )
    }
}

struct Configuration<N: ItemTrait, T: ItemTrait> {
    stack: Vec<Item<N, T>>,
    input: Vec<Terminal<T>>,
}
impl<N: ItemTrait, T: ItemTrait> Configuration<N, T> {
    fn new(input: Vec<T>) -> Self {
        Self {
            stack: vec![Item::EndOfInput],
            input: input
                .into_iter()
                .map(Terminal::T)
                .chain([Terminal::EndOfInput])
                .rev()
                .collect(),
        }
    }

    fn try_shift(&mut self) -> Result<(), ()> {
        if let Some(t) = self.input.pop() {
            self.stack.push(t.into());
            Ok(())
        } else {
            Err(())
        }
    }

    fn try_reduce(&mut self, production: &Production<N, T>) -> Result<(), ()> {
        if production
            .1
            .iter()
            .rev()
            .enumerate()
            .map(|(i, element)| (&self.stack[self.stack.len() - i], element))
            .all(|(stack_element, production_element)| stack_element == production_element)
        {
            self.stack.truncate(self.stack.len() - production.1.len());
            self.stack.push(Item::NonTerminal(production.0.clone()));
            Ok(())
        } else {
            Err(())
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Lr0ItemIndex(usize);

struct Lr0ItemNfa<N: ItemTrait, T: ItemTrait> {
    items: Vec<Lr0Item<N, T>>,
    terminal_transitions: HashMap<(Lr0ItemIndex, Terminal<T>), Lr0ItemIndex>,
    non_terminal_transitions: HashMap<(Lr0ItemIndex, N), Lr0ItemIndex>,
    epsilon_transitions: HashMap<Lr0ItemIndex, Vec<Lr0ItemIndex>>,
}
impl<N: ItemTrait, T: ItemTrait> Lr0ItemNfa<N, T> {
    pub fn new(productions: &HashSet<Production<N, T>>) -> Self {
        let items: Vec<_> = productions
            .iter()
            .flat_map(|p| Lr0Item::from_production(p))
            .collect();

        let mut terminal_transitions = HashMap::new();
        let mut non_terminal_transitions = HashMap::new();
        let mut epsilon_transitions = HashMap::new();
        for (i, item) in items.iter().enumerate().map(|(i, e)| (Lr0ItemIndex(i), e)) {
            match item.potential.first() {
                None => (),
                Some(Item::NonTerminal(n)) => {
                    // non-terminal transition to the shifted item
                    let shifted = Lr0Item::find_shifted_item(item, items.as_slice());
                    non_terminal_transitions.insert((i, n.clone()), shifted);
                    // and epsilon transitions to all productions starting with `n`
                    let epsilon_destinations = items
                        .iter()
                        .enumerate()
                        .map(|(i, e)| (Lr0ItemIndex(i), e))
                        .filter(|(i, e)| &e.nonterminal == n && e.parsed.is_empty())
                        .map(|(dest_i, _)| dest_i)
                        .collect::<Vec<_>>();
                    epsilon_transitions.entry(i).and_modify(
                        |destinations: &mut Vec<Lr0ItemIndex>| {
                            destinations.extend(epsilon_destinations.clone())
                        },
                    );
                }
                Some(Item::Epsilon) => {
                    let shifted = Lr0Item::find_shifted_item(item, items.as_slice());
                    epsilon_transitions.entry(i).and_modify(
                        |destinations: &mut Vec<Lr0ItemIndex>| destinations.push(shifted),
                    );
                }
                Some(x) => {
                    let x = match x {
                        Item::NonTerminal(_) | Item::Epsilon => unreachable!(),
                        Item::Terminal(c) => Terminal::T(c.clone()),
                        Item::EndOfInput => Terminal::EndOfInput,
                    };
                    terminal_transitions
                        .insert((i, x), Lr0Item::find_shifted_item(item, items.as_slice()));
                }
            }
        }

        todo!()
    }

    fn get_item_index(&self, item: &Lr0Item<N, T>) -> Lr0ItemIndex {
        self.items
            .iter()
            .enumerate()
            .find_map(|(i, element)| (element == item).then_some(Lr0ItemIndex(i)))
            .unwrap()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct StateIndex(usize);

#[derive(Debug)]
struct Dfa<N: ItemTrait, T: ItemTrait> {
    states: Vec<HashSet<Lr0Item<N, T>>>,
    transitions: HashMap<(StateIndex, Item<N, T>), StateIndex>,
}
impl<N: ItemTrait, T: ItemTrait> Dfa<N, T> {
    fn new(nfa: Lr0ItemNfa<N, T>, start_symbol: &N) -> Self {
        // TODO: complete this
        // NOTE: this is basically a breadth-first graph traversal, only
        // we're building the graph while traversing it.
        let mut handled_states = vec![];
        // NOTE: once something is added to this ^^
        // vec, it CAN'T be moved to a different index or removed!!
        let mut need_to_handle: Vec<(Option<(StateIndex, Item<N, T>)>, Vec<Lr0Item<N, T>>)> =
            vec![];

        let mut item_states: HashMap<Lr0Item<N, T>, StateIndex> = HashMap::new();
        let mut transitions: HashMap<(StateIndex, Item<N, T>), StateIndex> = HashMap::new();

        need_to_handle.push((
            None,
            nfa.items
                .iter()
                .filter(|item| item.parsed.is_empty() && &item.nonterminal == start_symbol)
                .cloned()
                .collect::<Vec<_>>(),
        ));

        while let Some((prior_connection, state)) = need_to_handle.pop() {
            // find all transitions
            // identify which ones lead to new states, and create those new states
            // identify which of the "new states" already exist, and connect those
            // TODO: how are connections supposed to be stored???

            // we have a few of the items in this state, but we need to add more
            let state = Self::get_item_group(&state, &nfa);

            handled_states.push(state);
            let current_state_index = StateIndex(handled_states.len() - 1);
            if let Some((prior_state, segment)) = prior_connection {
                transitions.insert((prior_state, segment), current_state_index);
            }
            let state = handled_states[handled_states.len() - 1].clone();
            for item in &state {
                item_states.insert(item.clone(), StateIndex(handled_states.len() - 1));
            }

            let mut new_transitions: HashMap<_, Vec<_>> = HashMap::new();
            for item in &state {
                if let Some(x) = item.potential.first() {
                    let next =
                        &nfa.items[Lr0Item::find_shifted_item(&item, nfa.items.as_slice()).0];
                    new_transitions
                        .entry(x)
                        .and_modify(|destinations| destinations.push(next.clone()));
                }
            }

            for (segment, items) in new_transitions {
                // check if the transition is to a group that already exists
                let item_group_index = handled_states
                    .iter()
                    .enumerate()
                    .find_map(|(i, state)| state.contains(&items[0]).then_some(StateIndex(i)));
                if let Some(index) = item_group_index {
                    transitions.insert((current_state_index, segment.clone()), index);
                } else {
                    need_to_handle.push((Some((current_state_index, segment.clone())), items));
                }
            }
        }

        Self {
            states: handled_states,
            transitions,
        }
    }

    fn get_item_group<'a>(
        root_items: impl IntoIterator<Item = &'a Lr0Item<N, T>>,
        nfa: &Lr0ItemNfa<N, T>,
    ) -> HashSet<Lr0Item<N, T>>
    where
        T: 'a,
        N: 'a,
    {
        let mut changed = true;
        let mut result: HashSet<Lr0Item<N, T>> =
            HashSet::from_iter(root_items.into_iter().cloned());
        while changed {
            changed = false;
            for item in &result {
                let new_items = nfa
                    .epsilon_transitions
                    .get(&nfa.get_item_index(&item))
                    .cloned()
                    .unwrap_or_default();
                if new_items.iter().any(|x| !result.contains(&nfa.items[x.0])) {
                    changed = true;
                    result.extend(new_items.iter().map(|i| nfa.items[i.0].clone()));
                    break; // NOTE: can we get rid of this `break` somehow?
                }
            }
        }

        todo!()
    }

    fn get_group_transitions<'a>(
        group: impl IntoIterator<Item = &'a Lr0Item<N, T>>,
    ) -> impl IntoIterator<Item = &'a Lr0Item<N, T>>
    where
        N: 'a,
        T: 'a,
    {
        group
            .into_iter()
            .filter(|x| !matches!(x.potential.first(), None | Some(Item::Epsilon)))
    }
}
