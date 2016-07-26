{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Datalog where

import Data.Text (Text, unpack)
import Data.String
import Data.Char (isUpper)
import Data.Maybe
import Data.List (intercalate)
import Control.Monad
import qualified Data.HashMap.Strict as Map

import Data.Typeable
import Data.Hashable

--import Data.Array


--import Debug.Trace

polyEq :: (Typeable a, Typeable b, Eq b) => a -> b -> Bool
polyEq a b = case cast a of
  Nothing -> False
  Just b' -> b' == b

--------------------------------
---- AST
--------------------------------
type Program = [Statement]

data Statement = Assertion Clause | Retraction Clause | Query Literal
  deriving (Show, Eq)

-- path(X, Y) :- edge(X, Y).
infix 6 :-
data Clause = Literal :- [Literal]
            | Fact Literal
  deriving (Show, Eq)

-- edge(a, b).
data Literal = AppliedPredicate Text [Term]
  deriving (Eq)

--a
--X

data Term where
  TermConstant :: (Show a, Eq a, Typeable a, Hashable a) => a -> Term
  TermVar      :: Text -> Int -> Term

-- Gotta be a better way?
instance Eq Term where
  TermConstant a == TermConstant b = polyEq a b
  TermVar t i    == TermVar t' i'  = (t, i) == (t', i')
  _ == _                           = False

instance Hashable Term where
  hashWithSalt salt (TermVar t i) = salt `hashWithSalt` t `hashWithSalt` i
  hashWithSalt salt (TermConstant x) = salt `hashWithSalt` x

-- I want simplification to be able to be inserted after the fact
-- Ideally, also unification on new data structures

------------------------------------------
---- DSL / Pretty syntax stuff
----------------------------------------

-- mostly handy for doing quick tests, but also used in the parser to
-- figure out if something should be a variable or a constant.
termFromString :: String -> Term
termFromString s@(x:_) | isUpper x = TermVar (fromString s) 0
termFromString s = TermConstant ((fromString s) :: Text)

instance IsString Term where
  fromString = termFromString

p :: String -> [Term] -> Literal
p s = AppliedPredicate (fromString s)

instance Show Term where
  show (TermVar t i)    = unpack t ++ show i
  show (TermConstant t) = show t

instance Show Literal where
  show (AppliedPredicate predName args) = show predName ++"(" ++ show args ++ ")"

------------------------------------------
---- Unification ----
------------------------------------------
class Substitutes a where
  substitute :: Substitution -> a -> a

type Substitution = Map.HashMap Term Term
true :: Substitution
true = Map.empty

findSub :: Substitution -> Term -> Maybe Term
findSub = flip Map.lookup

addSub :: Substitution -> (Term, Term) -> Substitution
addSub subs (key, val)
  | key /= val = Map.insert key val subs
  | otherwise = subs

newSub :: Term -> Term -> Substitution
newSub a b = addSub true (a, b)

class (Substitutes a, Substitutes b) => Unifies a b where
  unifyExpr :: a -> b -> Maybe Substitution

unify :: (Unifies a b, Substitutes a, Substitutes b) =>
         a -> b -> Substitution -> Maybe Substitution
unify lhs rhs subs =
  let lhs' = substitute subs lhs
      rhs' = substitute subs rhs
  in fmap (Map.union subs) $ unifyExpr lhs' rhs'

-- Move performing the substitution and adding new substitutions to the results
-- to a helper function? And keep the type class core here?

instance Unifies Term Term where
  unifyExpr (TermConstant a) (TermConstant b) | polyEq a b = Just true
  unifyExpr lhs@(TermVar _ _) rhs = return $ newSub lhs rhs
  unifyExpr _ _ = Nothing

instance Substitutes Term where
  substitute _ x@(TermConstant _) = x
  substitute s x@(TermVar _ _) = fromMaybe x $ do
    newVal <- findSub s x
    return $ substitute s newVal

instance Substitutes Literal where
  substitute s (AppliedPredicate predSym predArgs) =
       AppliedPredicate predSym $ substitute s predArgs

instance Unifies Literal Literal where
  unifyExpr (AppliedPredicate xPred xArgs) (AppliedPredicate yPred yArgs)
              | xPred == yPred = unifyExpr xArgs yArgs
  unifyExpr _ _ = Nothing -- I'm using Nothing for F (failure)

instance (Unifies a a) => Unifies [a] [a] where
  unifyExpr lhs rhs = foldM (\subs (l, r) -> unify l r subs) true $ zip lhs rhs

instance (Substitutes a) => Substitutes [a] where
  substitute subs = map (substitute subs)

someTests :: IO ()
someTests = do
  -- pred(roy, tim) = pred(X, tim)
  print $ unify (p"pred" ["roy", "tim"]) (p"pred" ["X", "tim"]) true
  -- p(X, X) = p(tim, tim)
  print $ unify (p"p" ["X", "X"]) (p"p" ["tim", "tim"]) true
  -- p(X, X) = p(tim, roy)
  print $ unify (p"p" ["X", "X"]) (p"p" ["tim", "roy"]) true
  -- f(X, X) = f(Y, 3)
  print $ unify (p"f" ["X", "X"]) (p"f" ["Y", "3"]) true
  -- f(Y, 3) = F(X, X)
  print $ unify (p"f" ["Y", "3"]) (p"f" ["X", "X"]) true

--------------------------------
---- MicroKanren?
--------------------------------
-- fresh, ===, disj, conj

type Goal = (Substitution, Int) -> Maybe (Substitution, Int)

liftG :: (Substitution -> Maybe Substitution) -> Goal
liftG f = \(subs, i) -> fmap (\subs' -> (subs', i)) $ f subs

(===) :: Unifies a b => a -> b -> Goal
a === b = liftG $ unify a b

-- Should I make a new type for Logic Variables so I don't let fresh
-- functions take constants?
fresh :: (Term -> Goal) -> Goal
fresh f (subs, idx) = (f (TermVar "" idx)) (subs, (idx + 1))

disj :: Goal -> Goal -> Goal
disj g1 g2 sc = mplus (g1 sc) (g2 sc)

conj :: Goal -> Goal -> Goal
conj g1 g2 sc = (g1 sc) >>= g2

--------------------------------
---- query time!
--------------------------------

{-
At its core, Datalog has a database of facts that are just predicates, often
applied to variables or constants.
> parent(john, douglas).

We want to query it with our own "facts" that are constructed in a similar way
but can have variable placeholders. Datalog will try to fill in these placeholders
with actual values that make it true.
-}

type Database = [Clause]

run :: Database -> [Literal] -> [Substitution]
run = go 0
  where go _ _ [] = [true]
        go i db goals = do
          let db' = map (rename i) db
          (subs, goals') <- branch db' goals
          solution <- go (i + 1) db goals'
          return (Map.union subs solution)

rename :: Int -> Clause -> Clause
rename i (h :- body) = renameLit h :- map renameLit body
  where renameTerm (TermVar name _) = TermVar name i
        renameTerm x = x
        renameLit (AppliedPredicate predName predArgs) =
          AppliedPredicate predName $ map renameTerm predArgs
rename _ x = x

branch :: Database -> [Literal] -> [(Substitution, [Literal])]
branch _ [] = error "no goals" -- []
branch db (goal:goals) = do
  h :- body <- db
  subs <- maybeToList (unify goal h true)
  return (subs, substitute subs (body ++ goals))

database :: Database
database = [
  p"edge" ["a", "b"] :- [],
  p"edge" ["b", "c"] :- [],
  p"edge" ["c", "d"] :- [],
  p"edge" ["d", "a"] :- [],
  p"path"["X", "Y"] :- [p"edge" ["X", "Y"]],
  p"path"["X", "Y"] :- [p"edge" ["X", "Z"], p"path"["Z", "Y"]]]

q :: Literal
q = p"path" ["X", "Y"]

getQuerySubs :: [Literal] -> Substitution -> [(Term, Term)]
getQuerySubs query subs=
  map findVar vars
  where isVar (TermVar _ _) = True
        isVar _ = False
        getVars (AppliedPredicate _ args) = filter isVar args
        --getVars (AppliedPredicate _ args) = args
        vars = concatMap getVars query
        findVar var = case Map.lookup var subs of
          Just v@(TermVar _ _) -> (var, snd $ findVar v)
          Just v@(TermConstant _) -> (var, v)
          Nothing -> error "lol"


subs2str :: [(Term, Term)] -> String
subs2str = unwords . map sub2str
  where sub2str (lhs, rhs) = show lhs ++ " = " ++ show rhs

printQuery :: Int -> IO ()
printQuery i = do
  let results = take i $ run database [q]
      results' = map (getQuerySubs [q]) results
  putStrLn $ intercalate "\n" $ map subs2str results'
