### pipeline.cc

`PipelineImpl` documents each step. A step (e.g. OptimizeGraph) contains multiple phases (e.g. TypedLoweringPhase). Each phase contains multiple reducers (e.g. ConstantFoldingReducer). A reducer is the smallest unit that edits the graph.

### Lowering

GraphAssembler provides a macro-assembler-ish interface to help with creating nodes.