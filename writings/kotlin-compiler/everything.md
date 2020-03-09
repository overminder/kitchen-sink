# Tl;dr: Pipeline

Kotlin source ->
KtElement (Psi) ->
core.descriptor (ClassicTypeSystemContext) ->
FirElement (nodes) / FirBasedSymbol (infotable?) (ConeTypeContext) ->
IrElement (nodes) / IrSymbol (infotable?) (IrTypeSystemContext)

### Source -> KtElement

Kotlin source -> ASTNode(untyped AST)/PsiElement(typed wrapper/getter)

- See class KtVisitor for an overview of many Kotlin PsiElements
- compiler.psi defines KtElement and [Stubs](https://www.jetbrains.org/intellij/sdk/docs/basics/indexing_and_psi_stubs/stub_indexes.html), also provides parser
  + Stubs represents the interface parts of a kt compilation unit
    (.h, .mli, .hi etc).
  + There's also a LighterASTNNode (KotlinLightParser) -- what is it? (Flyweight pattern is like hash consing)
  + Some KtElements are related to types: e.g. KtTypeReference (some of them are not KtElements but stubs!)
- compiler.psi.KtPsiFactory is the entrypoint for creating KtFile (a PsiElement) from source text.

### KtElement -> core.desciptor

DeclarationDescriptor seems to be a high-level IR with type analyzed.
It contains both the expr tree and the types.

#### LazyTopDownAnalyzer

compiler.frontend.LazyTopDownAnalyzer seems to be the psi analyzer. (Is there another analyzer that's not lazy?)

analyzeDeclarations returns an AnalysisResult which contains a ModuleDescriptor and a BindingContext.

### core.descriptor -> FIR

FIR (compiler.fir) seems to be an intermediate yet still high-level IR.

- See generated class FirVisitor for an overview of many of the Fir exprs
- compiler.frontend (not sure which step it is in, but it at least does symbol resolution, type checking, (Psi->CFG?)
   + See key classes: AnalysisResult, BindingContext, BindingTrace (records the collected binding / type substs?)
- compiler.resolution: tower/ReceiverValue etc
- compiler.fir: cones (types and symbols used in Fir?), fir2ir (lowering to Ir), psi2fir (lowering Psi to Fir), resolve, jvm, tree (Fir definitions and impl for psi2fir)
  + cones: StandardClassIds contains a bunch of core Kt (read: not JVM) type Ids. They have a JVM-like fqname.
  SyntheticCallableId contains when/try/nullcheck synthetic call exprs
  + tree.gen contains all Fir expressions (see tree.tree-generator's readme for how they are generated), as well as extra info (FirTypeRef). And even on Fir level, the generic types are not yet erased (FirTypeProjectionWithVariance)

### FIR -> IR

IR (compiler.ir) seems to be an lower-level IR.

### Example Pipeline from "kotlin -e <expr>"

(CLI driver)

compiler.cli.K2JVMCompiler ->
plugins.scripting-compiler ->
compiler.cli.TopDownAnalyzerFacadeForJVM.analyzeFilesWithJavaIntegration ->

(Analyze KtElement)

compiler.frontend.LazyTopDownAnalyzer.analyzeDeclarations
(HUGE): go through all stmts -> 
BodyResolver.resolveBodies ->
DeclarationChecker.process
(HUGE): go through files.annotations,
class.{modifiers,idents,header(super+generic bounds)},
{function,property,destructionDecl,typealias}.{modifiers,idents} ->

### KtElement

#### Example tree: script

KtFile - KtScript - toplevel decls
E.g., class/interface -> KtClass, fun name() -> KtNamedFunction, val -> KtProperty

### Descriptor

What is a core.descriptors.LazyTypeParameterDescriptor?

See core.descriptors.DeclarationDescriptorVisitor for an overview.
- DeclarationDescriptorVisitor sounds like an type-instantiated/abstracted wrapper of an element. Also has a bunch of annotations (AnnotationDescriptor) and a name. And is also a tree node (has parent: getContainingDecl)

### Fir

- compiler.fir.resolve: ResolutionStage sounds like something pipeline-related

### Ir

- compiler.ir.tree: IR (called IrSymbol) definitions. See IrSymbolVisitor for an overview. Looks that they have descriptors attached.


### Scope

core.descriptors.MemberScope 

# Type System

## core.type-system

type system core (equality, bounds checking etc). However this is more of an interface module -- the actual impls are in core.descriptors, fir and ir modules.

### TypeSystemContext.kt

Defines many marker types (guess it's used for disjoint classes)

#### TypeSystemTypeFactoryContext

Contains a bunch of common type factories:

- flexibleType has lower/upper bounds
- simpleType has tycon, tyargs, nullablep
- tyarg has ty and variance
- star has tyarg (why?)
- there's also an error type used in diagnosis

#### TypeCheckerProviderContext

- modular axioms (errorType unifiable with all types etc)
- what is a stub type?

#### TypeSystemCommonSuperTypesContext

Used to check if two type has common super types, and lowest-common ancestor utils.

typeDepth is a safe overestimation of the depth (from `Any`).

Seems to also be used in Fir.

#### TypeSystemInferenceExtensionContext

Inference related.

- What is a isCapturedTypeConstructor?
- What is a singleBestRepresentative?
- What is a noInferAnnotation?
- What is mayBeTypeVariable?
- What is a defaultType?
- Read impl of isUnit vs isUnitTypeConstructor
- Read impl of createCapturedType
- Read impl of createStubType
- Read impl createEmptySubstitutor, typeSubstitutorByTypeConstructor, safeSubstitute

#### TypeSystemContext

Lots of getters on various marker types. Makes the code less intuitive...

- fastCorrespondingSupertypes has no actual impl? (No, it's just that intellij's search functionality fail to find overridden extension methods)
- isCommonFinalClassConstructor is implemented in three (Psi, Fir, Ir) stage's TypeSystemContext:
  + ClassicTypeSystemContext: get ClassDescriptor from TypeConstructor.declarationDescriptor, then check it's final but not (enum or annotation). So the method really checks that the tycon is "final" but is not a uncommon (enum/annotation) class.
  + ConeTypeContext: Does almost the same thing, but also return true if is anonymous object (final by design). Works on FirBasedSymbol (some sort of class infotable?). Check that this is a FirRegularClassSymbol, whose FirRegularClass is final but not uncommon.
  + IrTypeSystemContext: Check this is a IrClassSymbol whose owner is final and not uncommon.
  So basically ClassDescriptor, FirRegularClass and IrClassSymbol.owner are the same thing across three stages.
  Sounds that reading the common implemented methods of these three TySysCtx impl classes would be super helpful to understand the stages.

What's the diff between TypeCheckerCtx and TypeSystemCtx?

## Type System for (Psi?)

Read core.descriptors.ClassicTypeSystemContext and TypeUtils

We can see that classes are represented by ClassDescriptor .

TypeParameterDescripter.representativeUpperBound is to find first in upperBound whose tycon is a single-inheritance class?

## Type System for Fir

Read ConeTypeContext

## Type System for Ir

Read IrTypeSystemContext

## compiler.resolution/.inference

Type inference? constraint system, subst, fresh tycon, tyvar etc

## compiler.frontend/.types

TypeIntersector (unify), DeferredType (I guess this is for when inference can't proceed at some first, and will retry when it has more information. Not really fully bidirectional (H-M style) type inference, but an approximation)

### types.expressions

Contains a bunch of KtElement visitors that does type recon/checking:
- ExpressionTypingVisitorDispatcher
- ControlStructureTypingVisitor
- FunctionsTypingVisitor
- BasicExpressionTypingVisitor (constants etc)
  + This actually does a bit of parsing/validation work... e.g. understore on int literals.
  + Also uses ConstantExpressionEvaluator to check for possible compile time constants (this indeed sounds like something a parser would do).
    ^ Folds boolean && and ||
    ^ Look up simple unary and binary func in OperationsMapGenerated

# Analysis

## compiler.frontend.LazyTopDownAnalyzer

### TopDownAnalysisContext

Stores the toplevel declarations (in typed maps) found during analysis.

## BindingTrace

Has a BindingContext. Is writable. Can record/inquiry KotlinType for a KtElement.
Impls:
- BindingTraceContext
- ObservingBindingTrace

## BindingContext

Sounds like a read-only counterpart to the BindingTrace.

## Smartcasting

compiler.frontend/smartcasts.DataFlowInfo: bunch of maps to stores the data flow analysis result useful for smart casts.

DataFlowValue: one instance of a value in a dataflow

DataFlowValue.Kind: classify exprs into smart cast enabled, possible, or disabled ones. Quite intuitive.

IdentifierInfo: represents both qualifier and ident name. what is this for?

# Descriptors

Looks that descriptors are something that's used throughout the whole compilation pipeline. They are more often used in frontend, but even in backend I can see some usage of them.

## CallableD: VisD & NonRootD & Subst

Receiver types (dispatch / extension), arg types, return types, type params;
Parameter names, names may be unstable/synthesized (e.g. from JVM object code)
Parameter values (what is ValueParameterDescriptor?)
Cross ref to overridden methods
UserDataKey<A>: stores typed user data

## MemberD: VisD & NonRootD

Has member modifiers: `expect` / `actual` / `external`.

## CallableMemberD: CallableD & MemberD

Kind: Decl/delegation/fakeOverride/synthesized (what's the last two?)
Has a copy(owner, modality[final,sealed,open,abstract], visibility, kind, copyOverrides) method.

## FunD: CallableMemberD

initialSignatureD: the initial D before renaming (didn't find SimpleFunctionD.rename)
hiddenToOvercomeSignatureClash: hack to handle corner case signature clash (said see nio.CharBuffer)
hiddenEverywhereBesideSupercalls: undocumented, another hack
Function modifiers: infix/inline/operator/suspend/tailrec

## FunDImpl: NonRootDImpl & FunD

Base impl for function modifiers. Setters set the local modifier (mostly happen during conversion from KtElement), while some getters (infix, operator) respect super class methods.
Base impl for substitution (doSubstitute), and substituted value param. Worth reading.
Base impl for initialize.
Only here documents hiddenToOvercomeSignatureClash and hiddenEverywhereBesideSupercalls: former makes the function completely hidden (even in super-call), latter permits super-call and propagates to overriden methods

## ConD: FunD

containingD: ClassifierDWithTypeParams (what is this?)
constructedClass: ClassD

## ClassConD: ConD

Just a bunch of return type specializations

## ClassConDImpl: FunDImpl & ClassConD

Default (<init>) or synthesized.
Has a way to calculate dispatchReceiverParam. If inner, outer class instance; else null.

# Backend

compiler.backend/StackValue is something that I can definitely read. It has an 
InstructionAdapter (a JVM bytecode emitter)

# Jargons

- Psi (compiler.psi): concrete syntax tree (aka parse tree). KtElement are psi nodes.
- PsiStub (compiler.psi): interface part of a Psi, see JetBrains' online doc
- Descriptor (core.descriptors): high level IR
- FIR (compiler.fir): intermediate level IR
- IR (compiler.ir): low level IR
- Tower (compiler.resolution/.calls): ?
- Resolve (compiler.frontend, fir, core): kind of analysis?
