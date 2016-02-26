module CpsPpr where

import           Cps
import qualified Data.Map         as M
import qualified Data.Set         as S
import           Text.PrettyPrint

pprId :: Id -> Doc
pprId (Id i) = text "v" <> int i
pprId (GlobalId s) = text "$" <> text s
pprId (RegId s) = text "%" <> text s

pprIds :: [Id] -> Doc
pprIds = hsep . map pprId

pprCont :: CCont -> Doc
pprCont (CCont lbl uses) = text "->" <+>
  pprLabel lbl <+> text "uses" <+> pprIds (S.toList uses)

pprLabel :: CLabel -> Doc
pprLabel (CLabel i) = text "L" <> int i

pprFunction :: CFunction -> Doc
pprFunction (CFunction name args entry labels) = vcat $
  (text "cfun" <+> text name <+> hsep (map pprId args) <+> equals
   <+> pprCont entry) : body
  where
    body = map (nest 2 . pprLabelStmt) (M.toList labels)

pprLabelStmt :: (CLabel, CStmt) -> Doc
pprLabelStmt (lbl, stmt) = pprLabel lbl <> colon <+> pprStmt stmt

pprStmt :: CStmt -> Doc
pprStmt s = case s of
  CRet u -> text "ret" <+> pprId u
  CDef u k d -> text "def" <+> pprId d <+> equals <+> pprId u <+> pprCont k
  CCall f es k r -> text "call" <+> pprId r <+> equals <+> pprIds (f:es) <+> pprCont k
  CPrimLt lhs rhs t f -> text "if" <+> pprId lhs <+> text "<"
    <+> pprId rhs <+> text "true" <+> pprCont t
    <+> text "false" <+> pprCont f
  CPrimAdd lhs rhs k r -> text "arith" <+> pprId r <+> equals
    <+> pprId lhs <+> text "+" <+> pprId rhs <+> pprCont k
  CLit i k r -> text "lit" <+> pprId r <+> equals <+> int i
    <+> pprCont k
  CNop k -> text "nop" <+> pprCont k
  _ -> error $ "pprStmt: " ++ show s
