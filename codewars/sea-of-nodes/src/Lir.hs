{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}

module Lir where

import           Control.Lens
import           Control.Monad.Representable.State (MonadState)
import           Control.Monad.Trans.State
import           Data.Function                     (on)
import qualified Data.Map                          as M
import           Data.Maybe                        (fromMaybe)
import qualified Data.Set                          as S
import qualified Data.Text                         as T
import           Text.PrettyPrint.ANSI.Leijen      hiding ((<$>))
import           Unsafe.Coerce                     (unsafeCoerce)

-- SSA IR.

data Reg
  = RegV Int (Maybe T.Text)
  | RegP T.Text
  deriving (Show, Eq, Ord)

newtype Label' (a :: LirType) = LAnonymous Int
  deriving (Show, Eq, Ord)

data Label = forall a. Label (Label' a)

deriving instance Show Label

instance Eq Label where
  (==) = (==) `on` unwrapLabel

unwrapLabel :: Label -> Int
unwrapLabel (Label (LAnonymous i)) = i

instance Ord Label where
  compare = compare `on` unwrapLabel

data LOperand
  = LoAtom LValue
  | LoArith LArithOp LValue LValue
  deriving (Show, Eq, Ord)

data LArithOp
  = LAdd
  | LLt
  deriving (Show, Eq, Ord)

data LValue
  = LvReg Reg
  | LvLit Int
  deriving (Show, Eq, Ord)

data LirType
  = Phi
  | Region
  | Prim
  | Exit
  deriving (Show, Eq, Ord)

data Lir' (a :: LirType) where
  LPhi :: Label' 'Region -> Reg -> [LValue] -> Lir' 'Phi
  LPrim :: Label' 'Region -> Reg -> LOperand -> Lir' 'Prim
  -- Set of defs and the exit label.
  LRegion :: S.Set (Label' 'Region) -> S.Set Reg -> Label' 'Exit -> Lir' 'Region
  -- Non-SSA, used to build the graph.
  LSeq :: [Label' 'Prim] -> Label' 'Exit -> Lir' 'Region
  LJnz :: Label' 'Region -> LValue -> Label' 'Region -> Label' 'Region -> Lir' 'Exit
  LJmp :: Label' 'Region -> Label' 'Region -> Lir' 'Exit
  LRet :: Label' 'Region -> LValue -> Lir' 'Exit

deriving instance Show (Lir' a)
deriving instance Eq (Lir' a)

data Lir = forall a. Lir (Lir' a)

deriving instance Show Lir

data LGraph = LGraph
  { _lgDefs      :: M.Map Reg (Label' 'Prim)
  , _lgStart     :: Label' 'Region
  , _lgNodes     :: M.Map Label Lir
  , _lgUniqueGen :: !Int
  } deriving (Show)

data LDefUse = LDefUse
  { _lDef :: [Reg]
  , _lUse :: [LValue]
  } deriving (Show)

makeLenses ''LDefUse

type DUTuple = ([Reg], [LValue])

class IsLOperand a where
  lOperand :: a -> LOperand

lAssign :: IsLOperand a => Label' 'Region -> Reg -> a -> Lir' 'Prim
lAssign label d s = LPrim label d (lOperand s)

class IsLValue a where
  lValue :: a -> LValue

instance IsLValue a => IsLOperand a where
  lOperand = LoAtom . lValue

instance IsLValue Reg where
  lValue = LvReg

instance IsLValue Int where
  lValue = LvLit

lvReg :: Lens' LValue [Reg]
lvReg f = \case
  LvReg r -> fmap (\[r'] -> LvReg r') (f [r])
  LvLit i -> fmap (\[] -> LvLit i) (f [])

opValue :: Lens' LOperand [LValue]
opValue f = \case
  LoAtom v -> fmap (\[v'] -> LoAtom v') (f [v])
  LoArith aop v1 v2 -> fmap (\[v1', v2'] -> LoArith aop v1' v2') (f [v1, v2])

duTuple :: Lens' DUTuple LDefUse
duTuple f (ds, us) = fmap (\(LDefUse ds' us') -> (ds', us')) (f $ LDefUse ds us)

exitJumpsTo :: Lens' (Lir' 'Exit) [Label' 'Region]
exitJumpsTo f = \case
  LJnz region r lt lf -> fmap (\[lt', lf'] -> LJnz region r lt' lf') (f [lt, lf])
  LJmp region lbl -> fmap (\[lbl'] -> LJmp region lbl') (f [lbl])
  LRet region r -> fmap (\[] -> LRet region r) (f [])

irDefUse :: Lens' Lir LDefUse
irDefUse = irDefUse'.duTuple

irDefUse' :: Lens' Lir DUTuple
irDefUse' mkF (Lir lir) = mkL $ case lir of
  LPhi region d ss -> (\([d'], ss') -> Lir $ LPhi region d' ss', ([d], ss))
  LSeq {} -> error "irDefUse' LSeq"
  -- XXX: what about region's use?
  LRegion prev defs exit -> (\(defs', []) -> Lir $ LRegion prev (S.fromList defs') exit,
                             (S.toList defs, []))
  LPrim region d lop -> (\([d'], vs') -> Lir $ LPrim region d' (lop & opValue .~ vs'),
                         ([d], lop ^. opValue))
  LJnz region s t f -> (\([], [s']) -> Lir $ LJnz region s' t f, ([], [s]))
  LJmp region x -> (\([], []) -> Lir $ LJmp region x, ([], []))
  LRet region s -> (\([], [s']) -> Lir $ LRet region s', ([], [s]))
  where
    mkL (setDU, getDU) = fmap setDU (mkF getDU)

irOperands :: Lens' Lir (Maybe (Reg, LOperand))
irOperands f (Lir lir) = case lir of
  LPrim region d lop -> fmap
    (\(Just (d', lop')) -> Lir $ LPrim region d' lop')
    (f (Just (d, lop)))
  x@_ -> fmap (\Nothing -> Lir x) (f Nothing)

regionDefs :: Lens' (Lir' 'Region) (S.Set Reg)
regionDefs f (LRegion preds defs exit)
  = fmap (\defs' -> LRegion preds defs' exit) (f defs)
regionDefs _ _ = error "regionDefs LSeq"

regionPreds :: Lens' (Lir' 'Region) (S.Set (Label' 'Region))
regionPreds f (LRegion preds defs exit)
  = fmap (\preds' -> LRegion preds' defs exit) (f preds)
regionPreds _ _ = error "regionPreds LSeq"

regionExit :: Lens' (Lir' 'Region) (Label' 'Exit)
regionExit f (LRegion preds defs exit) = fmap (LRegion preds defs) (f exit)
regionExit f (LSeq irs exit) = fmap (LSeq irs) (f exit)

makeLenses ''LGraph

emptyLGraph :: LGraph
emptyLGraph = LGraph M.empty undefined M.empty 1

mkUnique :: LGraph -> (Int, LGraph)
mkUnique g = (g ^. lgUniqueGen, g & lgUniqueGen +~ 1)

mkUnique' :: MonadState s m => Lens s s LGraph LGraph -> m Int
mkUnique' s2g = do
  (i, g) <- uses s2g mkUnique
  s2g .= g
  return i

newRegion :: LGraph -> (Label' 'Region, LGraph)
newRegion g = (`runState` g) $ do
  label <- state newLabel
  let ir = LRegion S.empty S.empty undefined
  id %= putIr label ir
  return label

newLabel :: LGraph -> (Label' a, LGraph)
newLabel g = (LAnonymous label, g')
  where
    (label, g') = mkUnique g

addDefToRegion :: Label' 'Region -> Lir' 'Prim -> LGraph -> (Label' 'Prim, LGraph)
addDefToRegion regionLabel ir@(LPrim _ d _) g = (`runState` g) $ do
  let mbIrLabel = getLabelByDef d g
  let Just region = getIrByLabel regionLabel g
  irLabel <- case mbIrLabel of
    Nothing -> state newLabel
    Just irLabel -> return irLabel
  id %= putIr irLabel ir
  id %= putIr regionLabel (region & regionDefs %~ S.insert d)
  return irLabel

setExitOfRegion :: Label' 'Region -> Lir' 'Exit -> LGraph -> (Label' 'Exit, LGraph)
setExitOfRegion regionLabel ir g = (`runState` g) $ do
  let Just region = getIrByLabel regionLabel g
  irLabel <- state newLabel
  id %= putIr irLabel ir
  id %= putIr regionLabel (region & regionExit .~ irLabel)
  return irLabel

putIr :: Label' a -> Lir' a -> LGraph -> LGraph
putIr label ir = lgNodes %~ M.insert (Label label) (Lir ir)

getIrByLabel :: Label' a -> LGraph -> Maybe (Lir' a)
getIrByLabel label g = g ^. lgNodes.to (fmap unwrap . M.lookup (Label label))
  where
    unwrap (Lir lir) = unsafeCoerce lir

getIrByLabelOrFail :: Label' a -> LGraph -> Lir' a
getIrByLabelOrFail label g = fromMaybe (error $ "getIrByLabel: " ++ show label) $
  getIrByLabel label g

getIrByDef :: Reg -> LGraph -> Maybe (Lir' 'Prim)
getIrByDef r g = (`getIrByLabel` g) =<< getLabelByDef r g

getIrByDefOrFail :: Reg -> LGraph -> Lir' 'Prim
getIrByDefOrFail r g = fromMaybe (error $ "getIrByDef: " ++ show r) $ getIrByDef r g

getLabelByDef :: Reg -> LGraph -> Maybe (Label' 'Prim)
getLabelByDef r g = g ^. lgDefs.to (M.lookup r)

predLabels :: Label' 'Region -> LGraph -> Maybe (S.Set (Label' 'Region))
predLabels label g = (^. regionPreds) <$> getIrByLabel label g

isExit :: Lir -> Bool
isExit (Lir lir) = isExit' lir

isExit' :: Lir' a -> Bool
isExit' = \case
  LJnz {} -> True
  LJmp {} -> True
  LRet {} -> True
  _ -> False

instance Pretty Reg where
  pretty = \case
    RegV i name -> (text . maybe "$t_" T.unpack) name <> int i
    RegP s -> text (T.unpack s)

instance Pretty Label where
  pretty (Label label) = pretty label

instance Pretty (Label' a) where
  pretty (LAnonymous i) = text "L" <> int i

instance Pretty LValue where
  pretty = \case
    LvReg r -> pretty r
    LvLit i -> pretty i

instance Pretty LOperand where
  pretty = \case
    LoArith lop a b -> pretty a <+> aOpToS lop <+> pretty b
    LoAtom a -> pretty a
    where
      aOpToS = text . \case
        LAdd -> "+"
        LLt -> "<"

instance Pretty (Lir' ty) where
  pretty = \case
    LPhi _ d ss -> prettyAssign d (simpl "phi" (map pretty ss))
    -- Shouldn't call pretty on 'Region.
    LRegion {} -> text "region"
    LSeq {} -> text "seq"
    LPrim _ d lop -> prettyAssign d lop

    LJnz _ r t f -> simpl "jnz" [pretty r, pretty t, pretty f]
    LJmp _ d -> simpl "jmp" [pretty d]
    LRet _ r -> simpl "ret" [pretty r]

    where
      commaSep :: [Doc] -> Doc
      commaSep = hcat . punctuate comma

      simpl tag xs = text tag <+> commaSep xs

      prettyAssign :: (Pretty a, Pretty b) => a -> b -> Doc
      prettyAssign a b = pretty a <+> equals <+> pretty b

instance Pretty Lir where
  pretty (Lir lir) = pretty lir


instance Pretty LGraph where
  pretty g = vsep $ bfs [g ^. lgStart] S.empty
    where
      bfs :: [Label' 'Region] -> S.Set (Label' 'Region) -> [Doc]
      bfs workList visited = case workList of
        [] -> []
        x:xs | S.member x visited -> bfs xs visited
             | otherwise ->
               let region = getIrByLabelOrFail x g
                   exit = getIrByLabelOrFail (region ^. regionExit) g
                   succs = exit ^. exitJumpsTo
               in prettyRegion x region : bfs (xs ++ succs) (S.insert x visited)
      prettyRegion :: Label' 'Region -> Lir' 'Region -> Doc
      prettyRegion label = \case
        LRegion _ defs exit ->
          let defIrs = map (Lir . (`getIrByDefOrFail` g)) . S.toList $ defs
              exitIr = Lir (getIrByLabelOrFail exit g)
          in prettyBody label (defIrs ++ [exitIr])
        LSeq defs exit ->
          let defIrs = map (Lir . (`getIrByLabelOrFail` g)) defs
              exitIr = Lir (getIrByLabelOrFail exit g)
          in prettyBody label (defIrs ++ [exitIr])

      prettyBody label irs = pretty label <+> text "{"
        <$$> (indent 2 . vsep . map pretty $ irs)
        <$$> text "}"
