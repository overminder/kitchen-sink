module CpsPpr (
  module CpsPpr,
  module Text.PrettyPrint.ANSI.Leijen
  ) where

import           Cps
import qualified Data.Map                     as M
import qualified Data.Set                     as S
import           Text.PrettyPrint.ANSI.Leijen

instance Pretty Id where
  pretty (Id i) = text "v" <> int i
  pretty (GlobalId s) = text "$" <> text s
  pretty (RegId s) = text "%" <> text s

pprIds :: [Id] -> Doc
pprIds = hsep . map pretty

instance Pretty CCont where
  pretty (CCont lbl uses) = text "->" <+>
    pretty lbl <+> text "uses" <+> pprIds (S.toList uses)

instance Pretty CLabel where
  pretty (CLabel i) = text "L" <> int i

instance Pretty CFunction where
  pretty (CFunction name args entry labels) = vcat $
    (text "cfun" <+> text name <+> hsep (map pretty args) <+> equals
    <+> pretty entry) : body
    where
      body = map (nest 2 . pprLabelStmt) (M.toList labels)

pprLabelStmt :: (CLabel, CStmt) -> Doc
pprLabelStmt (lbl, stmt) = pretty lbl <> colon <+> pretty stmt

instance Pretty CStmt where
  pretty s = case s of
    CRet u -> text "ret" <+> pretty u
    CDef u k d -> text "def" <+> pretty d <+> equals <+> pretty u <+> pretty k
    CCall f es k r -> text "call" <+> pretty r <+> equals <+> pprIds (f:es) <+> pretty k
    CPrimLt lhs rhs t f -> text "if" <+> pretty lhs <+> text "<"
      <+> pretty rhs <+> text "true" <+> pretty t
      <+> text "false" <+> pretty f
    CPrimAdd lhs rhs k r -> text "arith" <+> pretty r <+> equals
      <+> pretty lhs <+> text "+" <+> pretty rhs <+> pretty k
    CLit i k r -> text "lit" <+> pretty r <+> equals <+> int i
      <+> pretty k
    CNop k -> text "nop" <+> pretty k
    _ -> error $ "pprStmt: " ++ show s
