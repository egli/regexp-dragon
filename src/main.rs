use std::collections::{HashMap, HashSet, VecDeque};

// Some dummy data to put into an accepting state
type Translation = usize;

type StateId = usize;

#[derive(Debug, Default)]
struct State {
    translation: Option<Translation>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum Boundary {
    Word,
    NotWord,
    Number,
    NumberWord,
    WordNumber,
    PrePattern,
    None,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum Transition {
    Character(char),
    Any,
    Start(Boundary),
    End(Boundary),
    Epsilon,
}

#[derive(Debug)]
pub struct NFA {
    states: Vec<State>,
    start: StateId,
    transitions: HashMap<(StateId, Transition), StateId>,
    epsilon_transitions: HashMap<StateId, HashSet<StateId>>,
}

#[derive(Debug)]
struct Fragment {
    start: StateId,
    end: StateId,
}

enum AST {
    Character(char),
    String(String),
    Any,
    Concat(Box<AST>, Box<AST>),
    ZeroOrMore(Box<AST>),
    Optional(Box<AST>),
    OneOrMore(Box<AST>),
    Either(Box<AST>, Box<AST>),
}

impl NFA {
    fn new() -> NFA {
        NFA {
            start: 0,
            states: vec![],
            transitions: HashMap::new(),
            epsilon_transitions: HashMap::new(),
        }
    }

    fn add_state(&mut self, state: State) -> StateId {
        let idx = self.states.len();
        self.states.push(state);
        idx
    }

    fn add_char(&mut self, c: char, translation: Option<Translation>) -> Fragment {
        let start = self.add_state(State { translation: None });
        let end = self.add_state(State { translation });
        self.transitions
            .insert((start, Transition::Character(c)), end);
        Fragment { start, end }
    }

    fn add_string(&mut self, s: &str, translation: Option<Translation>) -> Fragment {
        let start = self.add_state(State { translation: None });
        let mut prev = start;
        let mut end = start;
        for c in s.chars() {
            end = self.add_state(State { translation: None });
            self.transitions
                .insert((prev, Transition::Character(c)), end);
            prev = end;
        }
        self.states[end].translation = translation;
        Fragment { start, end }
    }

    fn add_epsilon(&mut self, start: StateId, end: StateId) -> Fragment {
        self.epsilon_transitions
            .entry(start)
            .or_default()
            .insert(end);
        Fragment { start, end }
    }

    fn add_any(&mut self, translation: Option<Translation>) -> Fragment {
        let start = self.add_state(State { translation: None });
        let end = self.add_state(State { translation });
        self.transitions.insert((start, Transition::Any), end);
        Fragment { start, end }
    }

    fn add_union(&mut self, r1: &Fragment, r2: &Fragment) -> Fragment {
        let start = self.add_state(State { translation: None });
        let end = self.add_state(State { translation: None });
        self.add_epsilon(start, r1.start);
        self.add_epsilon(start, r2.start);
        self.add_epsilon(r1.end, end);
        self.add_epsilon(r2.end, end);
        Fragment { start, end }
    }

    fn add_concatenation(&mut self, r1: &Fragment, r2: &Fragment) -> Fragment {
        self.add_epsilon(r1.end, r2.start);
        Fragment {
            start: r1.start,
            end: r2.end,
        }
    }

    fn add_kleene(&mut self, r: &Fragment) -> Fragment {
        let start = self.add_state(State { translation: None });
        let end = self.add_state(State { translation: None });
        self.add_epsilon(start, r.start);
        self.add_epsilon(start, end);
        self.add_epsilon(r.end, r.start);
        self.add_epsilon(r.end, end);
        Fragment { start, end }
    }

    fn add_optional(&mut self, r: &Fragment) -> Fragment {
        self.add_epsilon(r.start, r.end);
        Fragment {
            start: r.start,
            end: r.end,
        }
    }

    fn add_fragment(&mut self, ast: &AST) -> Fragment {
        match ast {
            AST::Character(c) => self.add_char(*c, None),
            AST::String(s) => self.add_string(s, None),
            AST::Any => self.add_any(None),
            AST::Concat(ast1, ast2) => {
                let r1 = self.add_fragment(ast1);
                let r2 = self.add_fragment(ast2);
                self.add_concatenation(&r1, &r2)
            }
            AST::ZeroOrMore(ast) => {
                let fragment = self.add_fragment(ast);
                self.add_kleene(&fragment)
            }
            AST::Optional(ast) => {
                let fragment = self.add_fragment(ast);
                self.add_optional(&fragment)
            }
            AST::OneOrMore(ast) => {
                let one = self.add_fragment(ast);
                let fragment = self.add_fragment(ast);
                let kleene = self.add_kleene(&fragment);
                self.add_concatenation(&one, &kleene)
            }
            AST::Either(ast1, ast2) => {
                let r1 = self.add_fragment(ast1);
                let r2 = self.add_fragment(ast2);
                self.add_union(&r1, &r2)
            }
        }
    }

    fn from(ast: &AST) -> NFA {
        let mut nfa = NFA::new();
        let body = nfa.add_fragment(ast);
        nfa.start = body.start;
        nfa.states[body.end].translation = Some(1);
        nfa
    }

    fn epsilon_closure(&self, states: &HashSet<StateId>) -> HashSet<StateId> {
        let mut closure: HashSet<StateId> = states.clone();
        let mut queue = VecDeque::from(states.iter().cloned().collect::<Vec<_>>());

        while let Some(state) = queue.pop_front() {
            if let Some(next_states) = self.epsilon_transitions.get(&state) {
                for state in next_states.difference(&closure) {
                    queue.push_back(*state);
                }
                closure.extend(next_states);
            }
        }
        closure
    }

    fn move_state(&self, states: &HashSet<StateId>, transition: Transition) -> HashSet<StateId> {
        let mut next_states = HashSet::new();

        for from in states {
            let key = (*from, transition.clone());
            if let Some(to) = self.transitions.get(&key) {
                next_states.insert(*to);
            }
        }
        next_states
    }

    /**
     * Given an input string, simulate the NFA to determine if the
     * input is accepted by the input string.
     */
    pub fn accepts(&self, input: &str) -> bool {
        let mut next_states = self.epsilon_closure(&HashSet::from([self.start]));
        for c in input.chars() {
            let reachable_via_character = self.move_state(&next_states, Transition::Character(c));
            let reachable_via_any = self.move_state(&next_states, Transition::Any);
            next_states = reachable_via_character
                .union(&reachable_via_any)
                .cloned()
                .collect();
            next_states = self.epsilon_closure(&next_states);
        }
        next_states
            .iter()
            .any(|s| self.states[*s].translation.is_some())
    }
}

/**
 * Generate a DOT structured string.
 */
pub fn nfa_dot(nfa: &NFA) -> String {
    let mut dot = String::from("digraph nfa {\n\trankdir=\"LR\";\n\tnode [shape = circle];\n");
    dot.push_str(&format!(
        "\tstart [shape=\"none\"]\n\tstart -> {}\n",
        nfa.start
    ));
    for (idx, state) in nfa.states.iter().enumerate() {
        if state.translation.is_some() {
            dot.push_str(&format!("\t{} [shape=\"doublecircle\"]\n", idx));
        }
    }
    for ((from, transition), to) in nfa.transitions.iter() {
        match transition {
            Transition::Character(c) => {
                dot.push_str(&format!("\t{} -> {} [label=\"{}\"]\n", from, to, c))
            }
            Transition::Any => {
                dot.push_str(&format!("\t{} -> {} [label=\"{}\"]\n", from, to, "Any"))
            }
            Transition::Start(boundary) => dot.push_str(&format!(
                "\t{} -> {} [label=\"{:?}\"]\n",
                from, to, boundary
            )),
            Transition::End(boundary) => dot.push_str(&format!(
                "\t{} -> {} [label=\"{:?}\"]\n",
                from, to, boundary
            )),
            Transition::Epsilon => unreachable!(),
        }
    }
    for (from, tos) in nfa.epsilon_transitions.iter() {
        for to in tos.iter() {
            dot.push_str(&format!("\t{} -> {} [label=\"{}\"]\n", from, to, "ε"));
        }
    }
    dot += "}";
    dot
}

fn main() {
    //    let ast = AST::Concat(Box::new(AST::Character('a')), Box::new(AST::Character('b')));
    //    let ast = AST::Either(Box::new(AST::Character('a')), Box::new(AST::Character('b')));
    // let ast = AST::ZeroOrMore(Box::new(AST::Either(
    // let ast = AST::OneOrMore(Box::new(AST::Either(
    //     Box::new(AST::Character('a')),
    //     Box::new(AST::Any),
    // )));
    let ast = AST::Concat(
        Box::new(AST::Concat(
            Box::new(AST::OneOrMore(Box::new(AST::Character('(')))),
            Box::new(AST::String("hello".to_string())),
        )),
        Box::new(AST::OneOrMore(Box::new(AST::Character(')')))),
    );
    //    let ast = AST::ZeroOrMore(Box::new(AST::Character('a')));
    let nfa = NFA::from(&ast);
    let dot = nfa_dot(&nfa);
    println!("{}", dot);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn character() {
        let ast = AST::Character('a');
        let nfa = NFA::from(&ast);
        nfa.accepts("a");
        assert!(nfa.accepts("a"));
        assert!(!nfa.accepts("b"));
    }

    #[test]
    fn alteration() {
        let ast = AST::Either(Box::new(AST::Character('a')), Box::new(AST::Character('b')));
        let nfa = NFA::from(&ast);
        assert!(nfa.accepts("a"));
        assert!(nfa.accepts("b"));
        assert!(!nfa.accepts("ab"));
        assert!(!nfa.accepts("c"));
    }

    #[test]
    fn concatenation() {
        let ast = AST::Concat(Box::new(AST::Character('a')), Box::new(AST::Character('b')));
        let nfa = NFA::from(&ast);
        assert!(nfa.accepts("ab"));
        assert!(!nfa.accepts("a"));
        assert!(!nfa.accepts("b"));
        assert!(!nfa.accepts("ba"));
        assert!(!nfa.accepts("c"));
        assert!(!nfa.accepts("abc"));
    }

    #[test]
    fn kleene() {
        let ast = AST::ZeroOrMore(Box::new(AST::Character('a')));
        let nfa = NFA::from(&ast);
        assert!(nfa.accepts(""));
        assert!(nfa.accepts("a"));
        assert!(nfa.accepts("aa"));
        assert!(nfa.accepts("aaaaa"));
        assert!(!nfa.accepts("b"));
        assert!(!nfa.accepts("ba"));
        assert!(!nfa.accepts("ab"));
        assert!(!nfa.accepts("c"));
        assert!(!nfa.accepts("abc"));
    }

    #[test]
    fn one_or_more() {
        let ast = AST::OneOrMore(Box::new(AST::Character('a')));
        let nfa = NFA::from(&ast);
        assert!(!nfa.accepts(""));
        assert!(nfa.accepts("a"));
        assert!(nfa.accepts("aa"));
        assert!(nfa.accepts("aaaaa"));
        assert!(!nfa.accepts("b"));
        assert!(!nfa.accepts("ba"));
        assert!(!nfa.accepts("ab"));
        assert!(!nfa.accepts("c"));
        assert!(!nfa.accepts("abc"));
    }

    #[test]
    fn any() {
        let ast = AST::Concat(
            Box::new(AST::Concat(
                Box::new(AST::Character('a')),
                Box::new(AST::Any),
            )),
            Box::new(AST::Character('b')),
        );
        let nfa = NFA::from(&ast);
        assert!(nfa.accepts("abb"));
    }

    #[test]
    fn optional() {
        let ast = AST::Concat(
            Box::new(AST::Optional(Box::new(AST::Concat(
                Box::new(AST::Character('a')),
                Box::new(AST::Any),
            )))),
            Box::new(AST::Character('b')),
        );
        let nfa = NFA::from(&ast);
        assert!(nfa.accepts("acb"));
        assert!(nfa.accepts("axb"));
        assert!(nfa.accepts("b"));
        assert!(!nfa.accepts("c"));
        assert!(!nfa.accepts("bbb"));
    }

    #[test]
    fn string() {
        let ast = AST::Concat(
            Box::new(AST::Concat(
                Box::new(AST::OneOrMore(Box::new(AST::Character('(')))),
                Box::new(AST::String("hello".to_string())),
            )),
            Box::new(AST::OneOrMore(Box::new(AST::Character(')')))),
        );
        let nfa = NFA::from(&ast);
        assert!(nfa.accepts("(hello)"));
        assert!(nfa.accepts("(((((hello)))"));
        assert!(!nfa.accepts("hello"));
        assert!(!nfa.accepts("(hello"));
        assert!(!nfa.accepts("hello)"));
        assert!(!nfa.accepts("()"));
        assert!(!nfa.accepts("(helo)"));
    }
}
