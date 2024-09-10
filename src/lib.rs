use std::collections::{VecDeque, HashMap};
use std::mem;
use std::ops::{BitAnd, BitOr, Not, Shr, Rem};
use regex::Regex;
use proposition::proposition;

type Model = HashMap<String, bool>;

#[derive(Clone)]
struct UnaryOp {
    arg: Prop,
}

impl UnaryOp {
    fn new(arg: Prop) -> Self {
        Self {
            arg,
        }
    }
}

#[derive(Clone)]
struct BinaryOp {
    lhs: Prop,
    rhs: Prop,
}

impl BinaryOp {
    fn new(lhs: Prop, rhs: Prop) -> Self {
        Self {
            lhs,
            rhs,
        }
    }
}

#[derive(Clone, Default)]
enum Prop {
    #[default]
    True,
    False,
    Symbol(String),
    Not(Box<UnaryOp>),
    And(Box<BinaryOp>),
    Or(Box<BinaryOp>),
    Implic(Box<BinaryOp>),
    Iff(Box<BinaryOp>),
}

impl Prop {
    fn true_literal() -> Self {
        Prop::True
    }

    fn false_literal() -> Self {
        Prop::False
    }

    fn symbol(name: &str) -> Self {
        Prop::Symbol(String::from(name))
    }

    fn not(p: Prop) -> Self {
        Prop::Not(Box::new(UnaryOp::new(p)))
    }

    fn and(lhs: Prop, rhs: Prop) -> Self {
        Prop::And(Box::new(BinaryOp::new(lhs, rhs)))
    }
    
    fn or(lhs: Prop, rhs: Prop) -> Self {
        Prop::Or(Box::new(BinaryOp::new(lhs, rhs)))
    }

    fn implic(lhs: Prop, rhs: Prop) -> Self {
        Prop::Implic(Box::new(BinaryOp::new(lhs, rhs)))
    }
    
    fn iff(lhs: Prop, rhs: Prop) -> Self {
        Prop::Iff(Box::new(BinaryOp::new(lhs, rhs)))
    }

    fn eval(&self, model: &Model) -> bool {
        match self {
            Prop::True => true,
            Prop::False => false,
            // Closed-world assumption: Anything not specified is false
            Prop::Symbol(name) => *(model.get(name).unwrap_or_else(|| &false)),
            Prop::Not(p) => !p.arg.eval(model),
            Prop::And(p) => p.lhs.eval(model) && p.rhs.eval(model),
            Prop::Or(p) => p.lhs.eval(model) || p.rhs.eval(model),
            Prop::Implic(p) => !p.lhs.eval(model) || p.rhs.eval(model),
            Prop::Iff(p) => p.lhs.eval(model) == p.rhs.eval(model),
        }
    }

    fn bicon_elim(&mut self) {
        match self {
            Prop::True | Prop::False | Prop::Symbol(_) => (),
            Prop::Not(p) => p.arg.bicon_elim(),
            Prop::And(p) | Prop::Or(p) | Prop::Implic(p) | Prop::Iff(p) => {
                p.lhs.bicon_elim();
                p.rhs.bicon_elim();
            },
        }
        if let Prop::Iff(p) = self {
            *self = Prop::and(
                Prop::implic(p.lhs.clone(), p.rhs.clone()),
                Prop::implic(mem::take(&mut p.rhs), mem::take(&mut p.lhs)));
        }
    }

    fn implic_elim(&mut self) {
        match self {
            Prop::True | Prop::False | Prop::Symbol(_) => (),
            Prop::Not(p) => p.arg.implic_elim(),
            Prop::And(p) | Prop::Or(p) | Prop::Implic(p) | Prop::Iff(p) => {
                p.lhs.implic_elim();
                p.rhs.implic_elim();
            },
        }
        if let Prop::Implic(p) = self {
            *self = Prop::or(
                Prop::not(mem::take(&mut p.lhs)), mem::take(&mut p.rhs));
        }
    }

    fn move_not_inward(&mut self) {
        if let Prop::Not(p) = self {
            match &mut p.arg {
                // Double negation: !!p == p
                Prop::Not(p) => {
                    *self = mem::take(&mut p.arg);
                    // Check for another double negative
                    self.move_not_inward();
                },
                // DeMorgan: !(p & q) == (!p | !q)
                Prop::And(p) => {
                    let mut new_lhs = Prop::not(mem::take(&mut p.lhs));
                    let mut new_rhs = Prop::not(mem::take(&mut p.rhs));
                    // We may have introduced a double negative to the smaller
                    // expressions, so handle them recursively
                    new_lhs.move_not_inward();
                    new_rhs.move_not_inward();
                    *self = Prop::or(new_lhs, new_rhs);
                },
                // DeMorgan: !(p | q) == (!p & !q)
                Prop::Or(p) => {
                    let mut new_lhs = mem::take(&mut p.lhs);
                    let mut new_rhs = mem::take(&mut p.rhs);
                    // We may have introduced a double negative to the smaller
                    // expressions, so handle them recursively
                    new_lhs.move_not_inward();
                    new_rhs.move_not_inward();
                    *self = Prop::and(Prop::not(new_lhs), Prop::not(new_rhs));
                }
                Prop::True => *self = Prop::False,
                Prop::False => *self = Prop::True,
                Prop::Symbol(_) => (),
                Prop::Implic(_) | Prop::Iff(_) => 
                    panic!("Must eliminate implic and iff before moving not inward")
            }
        } else if let Prop::And(p) | Prop::Or(p) = self {
            p.lhs.move_not_inward();
            p.rhs.move_not_inward();
        } else if let Prop::Implic(_) | Prop::Iff(_) = self {
            panic!("Must eliminate implic and iff before moving not inward.");
        }
    }

    fn distribute_or_over_and(&mut self) {
        if let Prop::Or(outer) = self {
            if let Prop::And(inner) = &mut outer.lhs {
                let mut new_lhs = Prop::or(
                    mem::take(&mut inner.lhs), outer.rhs.clone());
                let mut new_rhs = Prop::or(
                    mem::take(&mut inner.rhs), mem::take(&mut outer.rhs));
                new_lhs.distribute_or_over_and();
                new_rhs.distribute_or_over_and();
                *self = Prop::and(new_lhs, new_rhs);
            } else if let Prop::And(inner) = &mut outer.rhs {
                let mut new_lhs = Prop::or(
                    outer.lhs.clone(), mem::take(&mut inner.lhs));
                let mut new_rhs = Prop::or(
                    mem::take(&mut outer.lhs), mem::take(&mut inner.rhs));
                new_lhs.distribute_or_over_and();
                new_rhs.distribute_or_over_and();
                *self = Prop::and(new_lhs, new_rhs);
            }
        } else if let Prop::And(p) = self {
            p.lhs.distribute_or_over_and();
            p.rhs.distribute_or_over_and();
        } else if let Prop::Not(p) = self {
            p.arg.distribute_or_over_and();
        } else if let Prop::Implic(_) | Prop::Iff(_) = self {
            panic!("Must eliminate implic and iff before distributing.");
        }
    }

    fn split_clause(self) -> Vec<Self> {
        let mut stack = vec![self];
        let mut new_clauses = vec![];
        while !stack.is_empty() {
            let prop = stack.pop().unwrap();
            if let Prop::And(p) = prop {
                if let Prop::And(_) = p.lhs {
                    stack.push(p.lhs);
                } else {
                    new_clauses.push(p.lhs);
                }
                if let Prop::And(_) = p.rhs {
                    stack.push(p.rhs);
                } else {
                    new_clauses.push(p.rhs);
                }
            } else {
                new_clauses.push(prop);
            }
        }
        new_clauses
    }

    fn cnf(mut self) -> Vec<Self> {
        self.bicon_elim();
        self.implic_elim();
        self.move_not_inward();
        self.distribute_or_over_and();
        self.split_clause()
    }

    fn print_tree(&self) {
        self.print_layer(0);
    }

    fn print_layer(&self, depth: usize) {
        let mut s = "\t".repeat(depth);
        match self {
            Prop::True => {
                s.push_str("True");
                println!("{}", s);
            },
            Prop::False => {
                s.push_str("False");
                println!("{}", s);
            },
            Prop::Symbol(name) => {
                s.push_str(&name);
                println!("{}", s);
            }
            Prop::Not(p) => {
                s.push_str("Not");
                println!("{}", s);
                p.arg.print_layer(depth + 1);
            }
            Prop::And(p) => {
                s.push_str("And");
                println!("{}", s);
                p.lhs.print_layer(depth + 1);
                p.rhs.print_layer(depth + 1);
            },
            Prop::Or(p) => {
                s.push_str("Or");
                println!("{}", s);
                p.lhs.print_layer(depth + 1);
                p.rhs.print_layer(depth + 1);
            },
            Prop::Implic(p) => {
                s.push_str("Implic");
                println!("{}", s);
                p.lhs.print_layer(depth + 1);
                p.rhs.print_layer(depth + 1);
            },
            Prop::Iff(p) => {
                s.push_str("Iff");
                println!("{}", s);
                p.lhs.print_layer(depth + 1);
                p.rhs.print_layer(depth + 1);
            },
        }
    }
}

struct KB {
    sentences: Vec<Prop>,
}

impl KB {
    fn empty() -> Self {
        Self {
            sentences: vec![],
        }
    }

    // Just the usual shunting-yard algorithm
    fn str_to_prop(sentence: &str) -> Result<Prop, &'static str> {
        let sentence = String::from(sentence);
        let tokens: Vec<&str> = sentence.split(" ").collect();
        let mut expr = VecDeque::new();
        let mut ops = vec![];
        let err_msg = "invalid sentence";
        let left_paren_symbol = Regex::new(r"\([[:alpha:]]*").unwrap();
        let right_paren_symbol = Regex::new(r"[[::alpha::]]*\)").unwrap();
        for token in tokens.iter() {
            match *token {
                "&" => {
                    ops.push("&");
                },
                "|" => {
                    while let Some(&"&") = ops.last() {
                        expr.push_back(ops.pop().unwrap());
                    }
                    ops.push("|");
                },
                "=>" => {
                    while let Some(&"&") | Some(&"|") = ops.last() {
                        expr.push_back(ops.pop().unwrap());
                    }
                    ops.push("=>");
                },
                "<=>" => {
                    while let Some(&"&") | Some(&"|") | Some(&"=>") 
                        = ops.last() {
                        expr.push_back(ops.pop().unwrap());
                    }
                    ops.push("<=>");
                },
                "(" => ops.push("("),
                ")" => {
                    loop {
                        let op = ops.pop().ok_or_else(|| err_msg)?;
                        if let "(" = op {
                            break;
                        } else {
                            expr.push_back(op);
                        }
                    }
                },
                name => {
                    if let Some(caps) = left_paren_symbol.captures(name) {
                        ops.push("(");
                        expr.push_back(&name[1..]);
                    } else if let Some(caps) 
                        = right_paren_symbol.captures(name) {
                        expr.push_back(&name[..name.len()-1]);
                        loop {
                            let op = ops.pop().ok_or_else(|| err_msg)?;
                            if let "(" = op {
                                break;
                            } else {
                                expr.push_back(op);
                            }
                        }
                    } else {
                        expr.push_back(name);
                    }
                },
            }
        }
        while !ops.is_empty() {
            expr.push_back(ops.pop().unwrap());
        }

        let mut stack = vec![];
        while !expr.is_empty() {
            match expr.pop_front().unwrap() {
                "&" => {
                    let rhs = stack.pop().ok_or_else(|| err_msg)?;
                    let lhs = stack.pop().ok_or_else(|| err_msg)?;
                    stack.push(Prop::and(lhs, rhs));
                }
                "|" => {
                    let rhs = stack.pop().ok_or_else(|| err_msg)?;
                    let lhs = stack.pop().ok_or_else(|| err_msg)?;
                    stack.push(Prop::or(lhs, rhs));
                },
                "=>" => {
                    let rhs = stack.pop().ok_or_else(|| err_msg)?;
                    let lhs = stack.pop().ok_or_else(|| err_msg)?;
                    stack.push(Prop::implic(lhs, rhs));
                },
                "<=>" => {
                    let rhs = stack.pop().ok_or_else(|| err_msg)?;
                    let lhs = stack.pop().ok_or_else(|| err_msg)?;
                    stack.push(Prop::iff(lhs, rhs));
                },
                "True" => stack.push(Prop::true_literal()),
                "False" => stack.push(Prop::false_literal()),
                name => stack.push(Prop::symbol(name)),
            }
        }
        stack.pop().ok_or_else(|| err_msg)
    }

    // Split nested ANDs into separate clauses
    fn split_clauses(&mut self) {
        let mut new_sentences = vec![];
        while !self.sentences.is_empty() {
            let prop = self.sentences.pop().unwrap();
            if let Prop::And(p) = prop {
                if let Prop::And(_) = p.lhs {
                    self.sentences.push(p.lhs);
                } else {
                    new_sentences.push(p.lhs);
                }
                if let Prop::And(_) = p.rhs {
                    self.sentences.push(p.rhs);
                } else {
                    new_sentences.push(p.rhs);
                }
            } else {
                new_sentences.push(prop);
            }
        }
        self.sentences = new_sentences;
    }

    fn tell(&mut self, mut prop: Prop) -> Result<(), &'static str> {
        self.sentences.append(&mut prop.cnf());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn print() {
        let mut kb = KB::empty();
        kb.tell(proposition!(p & q => r));
        kb.tell(proposition!(q | r));
        println!("{}", kb.sentences.len());
        for prop in kb.sentences.iter() {
            prop.print_tree();
        }
    }
}
