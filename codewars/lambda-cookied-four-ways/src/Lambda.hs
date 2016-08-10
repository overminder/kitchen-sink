module Lambda where

import qualified Data.List as L
import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

readLC src = case parse pLC "Lambda" src of
  Left e -> error $ "readLC: " ++ show e
  Right r -> r

data LC v
  = Var v
  | Lam v (LC v)
  | App (LC v) (LC v)
  deriving (Eq)

freeVars :: Eq v => LC v -> [v]
freeVars = \case
  Var v -> [v]
  Lam v e -> freeVars e L.\\ [v]
  App f a -> freeVars f `L.union` freeVars a

allVars :: Eq v => LC v -> [v]
allVars = \case
  Var v -> [v]
  Lam _ e -> allVars e
  App f a -> allVars f `L.union` allVars a

-- Parsing

lexer = P.makeTokenParser haskellDef

reservedOp = P.reservedOp lexer
reserved = P.reserved lexer
identifier = P.identifier lexer
pParens = P.parens lexer
pSemi = P.semi lexer

pLC = pLam <|> pApp <|> pLet

pAtom = pParens pLC <|> pVar
pVar = Var <$> identifier
pLam = Lam <$> (reservedOp "\\" *> identifier) <*> (reservedOp "->" *> pLC)
pApp = foldl1 App <$> many1 pAtom
pLet = do
  reserved "let"
  bs <- pDef `sepBy` pSemi
  reserved "in"
  e <- pLC
  pure $ foldr mkLet e bs
  where
    pDef = (,) <$> identifier <*> (reservedOp "=" *> pLC)
    mkLet (x, e) b = App (Lam x b) e

-- Pretty-Printing

instance Show v => Show (LC v) where
  show = show . pprLC 0

pprLC :: Show v => Int -> LC v -> Doc
pprLC p = \case
  Var v -> text $ show v
  Lam v e -> mbP (p > 0) $ text ("\\" ++ show v) <+> text "->" <+> pprLC 0 e
  App f a -> mbP (p > 1) $ pprLC 1 f <+> pprLC 2 a

  where
    mbP True = parens
    mbP False = id
