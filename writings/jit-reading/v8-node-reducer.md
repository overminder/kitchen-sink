### Graph Reducer

Edits the SSA graph by updating/adding/removing nodes.

- Reduction(node): represents the result of a reduction.
- Reducer: can reduce one node
- AdvancedReducer: can reduce multiple nodes
- AdvancedReducer.Editor: helper that performs the actual edit operations on the graph. This does most of the heavy lifting, and hides the details.

# Reading some of the analyses

## escape-analysis

Seems to be similar to Graal's PEA. Tracks the alloc/read/write in a tracker.

The analysis is path sensitive, but LoadElement may be handled in a more precise way: when there are only 2 elements, it's data-sensitve in that the index is used to select one of the elements! When there's only 1, the access is even assumed to always success so the only element is chosen (i.e. array out of bound access is UB).

There's a special case for uninhabited types -- constant-folding a node that has a uninhabited type with a constant (i.e. boolean true) is wrong!