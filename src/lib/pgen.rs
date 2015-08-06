use grammar::{Grammar, Symbol, SymbolType};
use std::collections::HashSet;

struct ParserGenerator;

pub struct First {
    pub grm: Grammar
}

impl First {

    pub fn first(&self, s: &Symbol) -> HashSet<Symbol> {
        let mut f:HashSet<Symbol> = HashSet::new();
        match s.typ {
            SymbolType::Terminal => { f.insert(s.clone()); },
            SymbolType::Nonterminal => {
                // if epsilon => add epsilon to first(X)
                // if nonterm => add first(production)
                match self.grm.get_rule(&s.name) {
                    Some(rule) => {
                        for a in rule.alternatives.iter(){
                            let r = &mut self.first_vec(a);
                            for e in r.iter() {
                                f.insert(e.clone());
                            }
                        }
                    },
                    None => { f.insert(s.clone()); },
                }
            },
            SymbolType::Epsilon => { f.insert(s.clone()); }
        }
        f
    }

    pub fn first_vec(&self, v: &Vec<Symbol>) -> HashSet<Symbol> {
        // while first contains epsilon, add next first
        let mut result: HashSet<Symbol> = HashSet::new();
        for s in v.iter() {
            let first = &mut self.first(s);
            println!("{:?}", first);
            if first.contains(&Symbol::new("".to_string(), SymbolType::Epsilon)) {
                // element has epsilon -> add without epsilon and continue
                for e in first.iter() {
                    if e.typ != SymbolType::Epsilon || v.last() == Some(s) {
                        result.insert(e.clone());
                    }
                }
            }
            else {
                // element has not epsilon -> add and stop
                println!("first {:?}", first);
                for e in first.iter() {
                    result.insert(e.clone()); // union is not inplace
                }
                println!("result {:?}", result);
                break
            }
        }
        result
    }
}

impl ParserGenerator {
}
