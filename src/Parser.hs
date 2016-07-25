{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Control.Monad (void)
import Text.Megaparsec
import Text.Megaparsec.Expr
import Text.Megaparsec.String -- input stream is of type ‘String’
import qualified Text.Megaparsec.Lexer as L

sc :: Parser ()
sc = L.space (void spaceChar) lineCmnt blockCmnt
  where lineCmnt = L.skipLineComment "//"
        blockCmnt = L.skipBlockComment "/*" "*/"

  


edgeTest :: String
edgeTest = concat ["edge(a, b). edge(b, c). edge(c, d). edge(d, a).\n"
        , "path(X, Y) :- edge(X, Y).\n"
        , "path(X, Y) :- edge(X, Z), path(Z, Y).\n"
        , "path(X, Y)?"]
