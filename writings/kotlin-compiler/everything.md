### Pipeline

1. Kotlin source -> ASTNode(untyped AST)/PsiElement(typed wrapper/getter)
  - See class KtVisitor for an overview of many Kotlin PsiElements
  - compiler.psi defines KtElement and [Stubs](https://www.jetbrains.org/intellij/sdk/docs/basics/indexing_and_psi_stubs/stub_indexes.html), also provides parser
    + Stubs represents the interface parts of a kt compilation unit
      (.h, .mli, .hi etc).
    + There's also a LighterASTNNode (KotlinLightParser) -- what is it? (Flyweight pattern is like hash consing)
    + Some KtElements are related to types: e.g. KtTypeReference (some of them are not KtElements but stubs!)

2. PsiElement -> Fir (an intermediate yet still high-level IR)
  - See generated class FirVisitor for an overview of many of the Fir exprs
  - compiler.frontend (not sure which step it is in, but it at least does symbol resolution, type checking, (Psi->CFG?)
     + See key classes: AnalysisResult, BindingContext, BindingTrace (records the collected binding / type substs?)
  - compiler.fir: cones (types and symbols used in Fir?), fir2ir (lowering to Ir), psi2fir (lowering Psi to Fir), resolve, jvm, tree (Fir definitions and impl for psi2fir)
    + cones: StandardClassIds contains a bunch of core Kt (read: not JVM) type Ids. They have a JVM-like fqname.
    SyntheticCallableId contains when/try/nullcheck synthetic call exprs
    + tree.gen contains all Fir expressions (see tree.tree-generator's readme for how they are generated), as well as extra info (FirTypeRef). And even on Fir level, the generic types are not yet erased (FirTypeProjectionWithVariance)

3. Fir -> Ir (an lower-level IR?)

### Example Pipeline from "kotlin -e <expr>"

compiler.cli.K2JVMCompiler ->
plugins.scripting-compiler ->
compiler.cli.TopDownAnalyzerFacadeForJVM.analyzeFilesWithJavaIntegration ->
compiler.frontend.LazyTopDownAnalyzer.analyzeDeclarations
(HUGE): go through all stmts -> 
BodyResolver.resolveBodies ->
DeclarationChecker.process
(HUGE): go through files.annotations,
class.{modifiers,idents,header(super+generic bounds)},
{function,property,destructionDecl,typealias}.{modifiers,idents} ->

What is a core.descriptors.LazyTypeParameterDescriptor?

See core.descriptors.DeclarationDescriptorVisitor for an overview.
- DeclarationDescriptorVisitor sounds like an type-instantiated/abstracted wrapper of an element. Also has a bunch of annotations (AnnotationDescriptor) and a name.

### Type System

- `core/type-system`: type system core (equality, bounds checking etc)
