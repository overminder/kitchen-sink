# Node

(Also see node-operator)

A sea-of-nodes SSA PDG node.

### Implementation details

- Node inputs/outputs are stored in an optimized extensible smallvec, where some storage are inline while others require one more indirection.
- Nodes are mutable.
  + use.addInput(def) will also call def.addUse(use), but not vice versa. Also for {remove,update}Input.
  + Externally, node's input and outputs are always consistent with its operator. But internally during modifications there can be inconsistencies.
  + To ensure consistency, verify nodes often.