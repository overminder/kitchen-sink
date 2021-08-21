# Node

(Also see node-operator)

A sea-of-nodes SSA PDG node.

### Implementation details

- Node inputs/outputs are stored in an optimized extensible smallvec, where some storage are inline while others require one more indirection.
- Nodes are mutable.
  + use.addInput(def) will also call def.addUse(use), but not vice versa. Also for {remove,update}Input.
  + Externally, node's input and outputs are always consistent with its operator. But internally during modifications there can be inconsistencies.
  + To ensure consistency, verify nodes often.

### Typing

Nodes have a bitvec that describes their types:
- Int ranges (e.g. for bounds check elimination)
- OO types (struct, union of structs)
- Graal also has this as in Stamps. But stamps are likely more type-safe, since the nodes and the stamps are all typed.

types.h defines a long list of types, and their bitvec representations.