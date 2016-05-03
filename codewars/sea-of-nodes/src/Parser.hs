module Parser
  ( parseAst
  ) where

import qualified Data.Text as T
import Text.Parsec
import Data.Functor.Identity
import Text.Parsec.String (Parser)
import Text.Parsec.Language (javaStyle)
import Text.Parsec.Expr
import qualified Text.Parsec.Token as P

import Ast

parseAst :: String -> Stmt
parseAst source = case parse pStmt "Ast" source of
  Left e -> error $ "parseAst: " ++ show e
  Right r -> r

pVar :: Parser Var
pVar = T.pack <$> ident <?> "identifier"

pLit :: Parser Expr
pLit = ELit . fromInteger <$> integer <?> "int-literal"

pExpr :: Parser Expr
pExpr = buildExpressionParser table term <?> "expr"
  where
    term = parens pExpr <|> pLit <|> (EVar <$> pVar) <?> "term"
    table = [ [binary "+" AAdd AssocLeft]
            , [binary "<" ALt AssocLeft]
            ]

    binary opName op = Infix (reservedOp opName *> pure (EArith op))

pStmt :: Parser Stmt
pStmt = pIfStmt <|> pWhileStmt <|> pRetStmt <|> pSeqStmt <|> pAssignStmt <?> "stmt"
  where
    pIfStmt = SIf
      <$> (reserved "if" *> pExpr)
      <*> (reserved "then" *> pStmt)
      <*> (reserved "else" *> pStmt)

    pWhileStmt = SWhile
      <$> (reserved "while" *> pExpr)
      <*> (reserved "do" *> pStmt)

    pRetStmt = SRet
      <$> (reserved "return" *> pExpr)

    pSeqStmt = SSeq
      <$> braces (many pStmt)

    pAssignStmt = SAssign
      <$> pVar <*> (reservedOp "=" *> pExpr)

-- Tokens

lexer :: P.GenTokenParser String u Identity
lexer = P.makeTokenParser (javaStyle { P.reservedNames = words "if then else while do return"
                                     , P.reservedOpNames = words "+ < ="
                                     })

parens :: forall u a. ParsecT String u Identity a -> ParsecT String u Identity a
parens = P.parens lexer

braces :: forall u a. ParsecT String u Identity a -> ParsecT String u Identity a
braces = P.braces lexer

ident :: forall u. ParsecT String u Identity String
ident = P.identifier lexer

reserved :: forall u. String -> ParsecT String u Identity ()
reserved = P.reserved lexer

reservedOp :: forall u. String -> ParsecT String u Identity ()
reservedOp = P.reservedOp lexer

integer :: forall u. ParsecT String u Identity Integer
integer = P.integer lexer
