{-# LANGUAGE OverloadedStrings #-}

module Datalog where

-- data Constant = ConstantIdentifier Text
--               | ConstantString Text
--               deriving (Show)
--
-- data Term = TermVariable Text
--           | TermConstant Constant
--           deriving (Show)
--
-- data PredicateSym = PredicateIdentifier Text
--                   | PredicateString Text
--                   deriving (Show)
--
-- data Literal = LiteralPredicateSym PredicateSym [Term]
--              | LiteralEquals Term Term
--              | LiteralNotEquals Term Term
--              deriving (Show)
--
-- infix 6 :-
-- data Clause = Literal :- [Literal]
--             | ClauseLiteral Literal
--             deriving (Show)
--
-- data Statement = StatementAssertion Clause
--                | StatementRetraction Clause
--                | StatementQuery Literal
--                deriving (Show)
--
-- q :: Statement
-- q = StatementQuery (LiteralPredicateSym (PredicateString "hi") [TermVariable "var1"])

-- Okay very simple now.

import Data.Text (Text)
import Data.String
import Data.Char (isUpper)
import Data.Maybe

data Term = TermConstant Text
  | TermVar Text Int
  | TermPredicate Text [Term]
  deriving (Show)

infix 6 :-
data Clause = Term :- [Term]
  deriving (Show)

instance IsString Term where
  fromString s@(x:_) | isUpper x = TermVar (fromString s) 0
  fromString s = TermPredicate (fromString s) []

-- XXX Why doesn't this work?
--{-# LANGUAGE FlexibleInstances #-}
--instance IsString ([Term] -> Term) where
--  fromString s = TermPredicate (fromString s)

p :: String -> [Term] -> Term
p s = TermPredicate (fromString s)

data Statement = Assertion Clause | Retraction Clause | Query [Term]
  deriving (Show)

type Program = [Statement]

---- Unification ----

-- XXX replace with [(Var, Term)]?
type Substitution = [(Term, Term)]
true :: Substitution
true = []

apply :: Substitution -> [Term] -> [Term]
apply subs terms = [applyTerm subs term | term <- terms]

applyTerm :: Substitution -> Term -> Term
applyTerm [] (TermVar y n) = TermVar y n
applyTerm ((TermVar x i, t):s) (TermVar y j)
  | x == y && i == j = applyTerm s t
  | otherwise = applyTerm s (TermVar y j)
applyTerm s (TermPredicate n ts) = TermPredicate n (apply s ts)
--applyTerm ((TermPredicate n ts):s) o = TermPredicate n (apply s o)
applyTerm _ _ = error "IDk what to do here yet!"

substitute :: Substitution -> Term -> Term
substitute s x = case x of
  (TermConstant _) -> x
  (TermVar _ _) -> fromMaybe x $ do
    a <- assoc s x
    return $ substitute s (snd a)
  (TermPredicate predSym predArgs) -> TermPredicate predSym $ subArgs s predArgs
    where subArgs _ [] = []
          subArgs s (arg : args)  = substitute s arg : subArgs s args

assoc :: Substitution -> Term -> Maybe (Term, Term)
assoc [] _ = Nothing
assoc (firstSub : restSubs) x
    | fst firstSub == x = Just firstSub
    | otherwise = assoc restSubs x


-- unify "X" "apple" == Just[("X", "apple)]
unify :: Term -> Term -> Maybe Substitution
unify (TermVar x n) (TermVar y m) = Just [(TermVar x n, TermVar y m)]
unify (TermVar x n) y = Just [(TermVar x n, y)]
unify x (TermVar y m) = Just [(TermVar y m, x)]
unify (TermPredicate a xs) (TermPredicate b ys)
  | a == b = unifyArgs xs ys []
  | otherwise = Nothing

unifyArgs :: [Term] -> [Term] -> Substitution -> Maybe Substitution
unifyArgs [] _ s = Just s
unifyArgs (x:xs) (y:ys) subs = do
  s <- unify x y
  -- Replace recursive apply with fmap
  s' <- unifyArgs (apply s xs) (apply s ys)
  return (s ++ s')

-- solver --
-- [Clause] is ... Rules?
prove :: [Clause] -> [Term] -> [Substitution]
prove rules = find rules 1

find :: [Clause] -> Int -> [Term] -> [Substitution]
find _ _ [] = [true]
find rules i goals = do let rules' = rename rules i
                        (s, goals') <- branch rules' goals
                        solution <- find rules (i + 1) goals'
                        return (s ++ solution)

branch :: [Clause] -> [Term] -> [(Substitution, [Term])]
branch _ [] = error "a girl's gotta have goals."
branch rules (goal:goals) = do h :- body <- rules
                               s <- maybeToList (unify goal h)
                               return (s, apply s (body ++ goals))


rename :: [Clause] -> Int -> [Clause]
rename rules i = [ renameVar h :- renameVars body | h :- body <- rules]
  where renameVar (TermVar s _) = TermVar s i
        renameVar (TermPredicate s ts) = TermPredicate s (renameVars ts)
        renameVars ts = [renameVar t | t <- ts]

q :: Program
q = [Assertion $ p"mortal" ["X"] :- [p"man" ["X"]]
    ,Assertion $ p"man" ["sean"] :- []
    ,Query [p"mortal" ["X"]]]

clauses :: [Clause]
--clauses = [p"mortal" ["X"] :- [p"man" ["X"]] ,p"man" ["socrates"] :- []]
clauses = [
  p"edge" ["a", "b"] :- [],
  p"edge" ["b", "c"] :- [],
  p"edge" ["c", "d"] :- [],
  p"edge" ["d", "a"] :- [],
  p"path"["X", "Y"] :- [p"edge" ["X", "Y"]],
  p"path"["X", "Y"] :- [p"edge" ["X", "Z"], p"path"["Z", "Y"]]]

query :: [Term]
--query = [TermPredicate "mortal" ["Y"]]
query = [p"path" ["X", "Y"]]

main :: IO ()
main = print $ prove clauses query
