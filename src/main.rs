use std::{
    cmp::Ordering,
    collections::{BinaryHeap, HashMap, HashSet},
    vec,
};

fn main() {
    let clauses = vec![
        vec![1, -3, 5],
        vec![-2, -5],
        vec![2, 4, -5],
        vec![-1, 2, -4, 5],
        vec![-2, -3],
        vec![-3, 4],
        vec![1, -2, -4, 5],
        vec![4, -5],
        vec![3, -4, 5],
        vec![-1, 3],
        vec![1, 2, 3, 4],
        vec![1, -2, 4, 5],
        vec![-2, -3, -4, 5],
        vec![2, -5],
        vec![-1, 4, 5],
    ];
    if let Some(result) = search(clauses.into_iter().map(Clause).collect()) {
        println!("{}", result);
    }
}

type Literal = i8;
type Var = u8;

#[derive(Debug, PartialEq, Eq, Clone)]
struct Clause(Vec<i8>);

impl std::fmt::Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[")?;
        for (i, l) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            f.write_fmt(format_args!("{}", l))?;
        }
        f.write_str("]")
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum Step {
    Decide(Var),
    Propagate(Clause, Literal),
    Conflict(Clause),
    Backtrack,
    SAT,
    UNSAT,
}

impl std::fmt::Display for Step {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Decide(var) => f.write_fmt(format_args!("Decide -{}", var)),
            Step::Propagate(clause, literal) => f.write_fmt(format_args!(
                "Propagate {{ use = {}, obtain = {} }}",
                clause, literal
            )),
            Step::Conflict(clause) => f.write_fmt(format_args!("Conflict {}", clause)),
            Step::Backtrack => f.write_str("Backtrack"),
            Step::SAT => f.write_str("SAT"),
            Step::UNSAT => f.write_str("UNSAT"),
        }
    }
}

#[derive(Debug, Clone)]
struct State {
    /// Steps taken so far
    steps: Vec<Step>,
    /// Current (partial) model
    vars: HashMap<Var, bool>,
    /// Stack variable values obtained through Decide/Backtrack steps
    set_vars: Vec<Literal>,
    /// Stack of variable values obtained through propagation since last Decide/Backtrack step
    propagated_vars: Vec<Vec<Var>>,
}

impl State {
    fn get_vars(clauses: Vec<Clause>) -> Vec<Var> {
        clauses
            .iter()
            .flat_map(|clause| clause.0.iter())
            // .flatten()
            .map(|literal| literal.unsigned_abs())
            .collect::<HashSet<u8>>()
            .into_iter()
            .collect()
    }

    fn get_conflict(&self, clauses: Vec<Clause>) -> Option<Clause> {
        'clauses: for clause in clauses {
            for &literal in clause.0.iter() {
                match self.vars.get(&(literal.unsigned_abs())) {
                    Some(value) => {
                        if (literal > 0) == *value {
                            continue 'clauses;
                        }
                    }
                    None => continue 'clauses,
                }
            }
            return Some(clause);
        }
        None
    }

    fn backtrack(&self) -> Self {
        let mut ret = self.clone();
        while let Some(last_var) = ret.set_vars.pop() {
            if let Some(prop_vars) = ret.propagated_vars.pop() {
                for var in prop_vars {
                    ret.vars.remove(&var);
                }
            }

            ret.vars.remove(&last_var.unsigned_abs());

            if last_var < 0 {
                ret.steps.push(Step::Backtrack);
                ret.vars.insert(last_var.unsigned_abs(), true);
                ret.set_vars.push(-last_var);
                ret.propagated_vars.push(vec![]);
                return ret;
            }
        }

        ret.steps.push(Step::UNSAT);
        ret
    }

    fn propagate(&self, clauses: Vec<Clause>) -> Vec<Self> {
        let mut new_states = vec![];
        let unsat_clauses = clauses.iter().filter(|clause| {
            !clause
                .0
                .iter()
                .any(|&literal| Some(&(literal > 0)) == self.vars.get(&(literal.unsigned_abs())))
        });

        for clause in unsat_clauses {
            let unset_vars: Vec<i8> = clause
                .0
                .iter()
                .filter(|&literal| !self.vars.contains_key(&(literal.unsigned_abs())))
                .cloned()
                .collect();

            if unset_vars.len() == 1 {
                let var = unset_vars[0];
                let mut new_state = self.clone();
                new_state.steps.push(Step::Propagate(clause.clone(), var));
                new_state.vars.insert(var.unsigned_abs(), var > 0);
                let idx = new_state.propagated_vars.len() - 1;
                new_state
                    .propagated_vars
                    .get_mut(idx)
                    .unwrap()
                    .push(var.unsigned_abs());
                new_states.push(new_state);
            }
        }

        new_states
    }

    fn decide(&self, clauses: Vec<Clause>) -> Vec<Self> {
        let mut new_states = vec![];
        for var in Self::get_vars(clauses) {
            if !self.vars.contains_key(&var) {
                let mut new_state = self.clone();
                new_state.steps.push(Step::Decide(var));
                new_state.vars.insert(var, false);
                new_state.set_vars.push(-(var as i8));
                new_state.propagated_vars.push(vec![]);
                new_states.push(new_state);
            }
        }
        new_states
    }

    fn is_final(&self) -> bool {
        self.steps.contains(&Step::UNSAT) || self.steps.contains(&Step::SAT)
    }
}

impl PartialEq for State {
    fn eq(&self, other: &Self) -> bool {
        self.steps == other.steps
    }
}

impl Eq for State {}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(other.steps.len().cmp(&self.steps.len()))
    }
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl std::fmt::Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[ ")?;
        for (i, step) in self.steps.iter().enumerate() {
            if i > 0 {
                f.write_str("\n, ")?;
            }
            f.write_fmt(format_args!("{}", step))?;
        }
        f.write_str("]")
    }
}

fn search(clauses: Vec<Clause>) -> Option<State> {
    let state = State {
        steps: vec![],
        vars: HashMap::new(),
        set_vars: vec![],
        propagated_vars: vec![],
    };

    let mut queue: BinaryHeap<State> = BinaryHeap::new();

    queue.push(state);

    while let Some(mut state) = queue.pop() {
        if state.is_final() {
            return Some(state);
        }

        if let Some(clause) = state.get_conflict(clauses.clone()) {
            state.steps.push(Step::Conflict(clause));
            let new_state = state.backtrack();
            queue.push(new_state);
        } else {
            //todo!("Check for sat");
            for new_state in state.propagate(clauses.clone()) {
                queue.push(new_state)
            }
            for new_state in state.decide(clauses.clone()) {
                queue.push(new_state)
            }
        }
    }

    None
}
