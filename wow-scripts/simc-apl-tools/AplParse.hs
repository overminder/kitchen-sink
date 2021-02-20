module AplParse (
  pApl
) where

import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (javaStyle)
import Text.Parsec.Expr

import Apl

pApl src = parse pStmt "SimcApl" src

-- Lexing

lexer = P.makeTokenParser (javaStyle {
  P.reservedNames = ["variable", "name", "value", "floor", "if"],
  P.reservedOpNames = ["=", ",", "|", "&"]
})

parens = P.parens lexer
ident = P.identifier lexer
comma = P.comma lexer
dot = P.dot lexer
rOp = P.reservedOp lexer
rId = P.reserved lexer
integer = P.integer lexer

-- Parsing

pStmt = pSVar
pSVar = do
  rId "variable"
  comma

  rId "name"
  rOp "="
  name <- ident
  comma

  rId "value"
  rOp "="
  exp <- pExp

  pure $ SVar name exp

pExp = pEBOp

pEBOp = buildExpressionParser table pEProp <?> "EBOp"
 where
  table = [ [prefix "!" URNot]
          , [binary "%" BRRem AssocLeft]
          , [binary "*" BRMult AssocLeft]
          , [binary "+" BRPlus AssocLeft, binary "-" BRMinus AssocLeft]
          , [binary ">" BRGt AssocLeft, binary "<" BRLt AssocLeft]
          , [binary "&" BRAnd AssocLeft]
          , [binary "|" BROr AssocLeft]
          ]
  binary name op assoc = Infix (do { rOp name; pure (EBOp op) }) assoc
  prefix name op       = Prefix (do { rOp name; pure (EUOp op) })

pEProp = do
  atom <- pEAtom
  props <- many (dot *> ident)
  pure $ foldr (flip EProp) atom props

pEAtom = parens pExp <|> pAp <|> pEInt <|> pEVar
pAp = do
  rId "floor"
  parens pExp

pEInt = EInt . fromInteger <$> integer
pEVar = EVar <$> ident
