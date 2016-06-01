use petgraph::graph::{Graph, NodeIndex};

#[derive(Debug)]
pub struct Reg {
    number: isize,
    name: String,
}

#[derive(Debug)]
pub enum Node {
    Lit(i64),
    Add(NodeId, NodeId),
    Move(Reg, NodeId),

    Phi(Reg, Vec<NodeId>),

    Region(Vec<NodeId>),

    Jmp(NodeId),
    Jnz(Reg, NodeId, NodeId),
    Ret(NodeId),

    Start,
    Exit(NodeId),
}

pub struct NodeGraph {
    nodes: Graph<Node, ()>,
    exit: Option<NodeIndex>,
}

impl NodeGraph {
    pub fn new() -> Self {
        NodeGraph {
            nodes: Graph::new(),
            exit: None,
        }
    }

    pub fn add(&mut self, n: Node) -> NodeId {
        self.nodes.add_node(n)
    }

    pub fn add_to_region(&mut self, n: NodeId, r: NodeId) {
        match self.nodes[r] {
            Node::Region(ref mut vs) => {
                vs.push(n);
            }
            ref r => panic!("Not a region node: {:?}", r),
        }
        self.nodes.add_edge(r, n, ());
    }

    pub fn set_exit(&mut self, n: NodeId) {
        self.exit = Some(n);
    }
}

pub type NodeId = NodeIndex;
