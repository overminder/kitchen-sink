use ast::*;
use lir::{Node, NodeId, NodeGraph, Reg};

use std::collections::HashMap;

struct Context {
    unique_gen: usize,
    defs: Defs,
    g: NodeGraph,
    // unresolved_phis: Vec<(NodeId,
    here: NodeId,
}

type Defs = HashMap<NodeId, HashMap<Name, NodeId>>;

impl Context {
    fn stmt(&mut self, s: &Stmt) {
        match s {
            &Move(ref v, ref e) => {
                let e = self.expr(e);
                self.define(v, e);
            }
            _ => {
            }
        }
    }

    fn expr(&mut self, e: &Expr) -> NodeId {
        match e {
            &Arith(op, ref e1, ref e2) => {
                let ctor = match op {
                    Add => Node::Add,
                    Sub => Node::Sub,
                    Lt => Node::Lt,
                };
                let n1 = self.expr(e1);
                let n2 = self.expr(e2);
                self.add_node(ctor(n1, n2))
            }
            &Var(ref v) => {
                self.use_name(v)
            }
            &Lit(v) => {
                self.add_node(Node::Lit(v))
            }
        }
    }

    fn add_node(&mut self, n: Node) -> NodeId {
        let id = self.g.add(n);
        self.g.add_to_region(id, self.here);
        id
    }

    fn define(&mut self, v: &Name, e: NodeId) {
    }

    fn use_name(&mut self, v: &Name) -> NodeId {
        use_name_inner(&mut self.g, &mut self.defs, &mut self.unique_gen, self.here, v)
    }

}

fn use_name_inner(g: &mut NodeGraph,
                  defs: &mut Defs,
                  unique_gen: &mut usize,
                  here: NodeId,
                  v: &Name) -> NodeId {
    let mbN = {
        defs.entry(here)
            .or_insert(Default::default())
            .get(v).map(|x| x.to_owned())
    };

    match mbN {
        Some(n) => n,
        None => {
            let fresh = Reg::new(v.to_owned(), *unique_gen);
            *unique_gen += 1;

            // Add an empty phi.
            let id = g.add(Node::Phi(fresh, vec![]));
            defs.get_mut(&here).unwrap().insert(v.to_owned(), id);

            // Record this phi to be resolved when the graph is finished.


            // And recursively traverse the graph.
            id
        }
    }
}
