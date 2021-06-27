### Graph Reducer

Edits the SSA graph by updating/adding/removing nodes.

- Reduction(node): represents the result of a reduction.
- Reducer: can reduce one node
- AdvancedReducer: can reduce multiple nodes
- AdvancedReducer.Editor: helper that performs the actual edit operations on the graph. This does most of the heavy lifting, and hides the details.

