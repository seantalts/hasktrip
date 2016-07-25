{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Datalog where

import Data.Text (Text, unpack)
import Data.String
import Data.Char (isUpper)
import Data.Maybe
import Data.List (intercalate)
import Control.Monad
import Control.Monad.State
import qualified Data.Map.Strict as Map

--import Data.Array


--import Debug.Trace

--------------------------------
---- AST
--------------------------------
type Program = [Statement]

data Statement = Assertion Clause | Retraction Clause | Query Literal
  deriving (Show)

-- path(X, Y) :- edge(X, Y).
infix 6 :-
data Clause = Literal :- [Literal]
            | Fact Literal
  deriving (Show, Eq, Ord)

-- edge(a, b).
data Literal = AppliedPredicate Text [Term]
  deriving (Eq, Ord)

--a
--X
data Term = TermConstant Text
          | TermVar Text Int
            deriving (Eq, Ord)

------------------------------------------
---- DSL / Pretty syntax stuff
----------------------------------------

-- mostly handy for doing quick tests, but also used in the parser to
-- figure out if something should be a variable or a constant.
termFromString :: String -> Term
termFromString s@(x:_) | isUpper x = TermVar (fromString s) 0
termFromString s = TermConstant (fromString s)

instance IsString Term where
  fromString = termFromString

p :: String -> [Term] -> Literal
p s = AppliedPredicate (fromString s)

instance Show Term where
  show (TermVar t i) = unpack t ++ show i
  show (TermConstant t) = show t

instance Show Literal where
  show (AppliedPredicate predName args) = show predName ++"(" ++ show args ++ ")"

------------------------------------------
---- Unification ----
------------------------------------------

type Substitution = Map.Map Term Term -- [(Term, Term)]
true :: Substitution
true = Map.empty

findSub :: Substitution -> Term -> Maybe Term
findSub = flip Map.lookup

addSub :: Substitution -> (Term, Term) -> Substitution
addSub subs (key, val)
  | key /= val = Map.insert key val subs
  | otherwise = subs

class Unifies a where
  unify :: Substitution -> a -> a -> Maybe Substitution
  substitute :: Substitution -> a -> a

instance Unifies Term where
  substitute _ (TermConstant x) = TermConstant x
  substitute s x@(TermVar _ _) = fromMaybe x $ do -- better way to write this?
    newVal <- findSub s x
    return $ substitute s newVal
  unify subs lhs rhs =
    let lhs' = substitute subs lhs
        rhs' = substitute subs rhs
    in case (lhs', rhs') of
            (TermConstant _, TermConstant _)
              | lhs' == rhs' -> Just subs
            (TermVar _ _, _) -> return $ addSub subs (lhs', rhs')
             -- here, instead of creating a new variable, we replace one with the
             -- other. This is because I don't want to deal with the haskell state
             -- stuff required to generate a new unique variable, but that could
             -- end up being necessarrhs anrhswarhs.
            (_, _) -> Nothing

instance Unifies Literal where
  substitute s (AppliedPredicate predSym predArgs) =
     AppliedPredicate predSym $ substitute s predArgs
  unify subs (AppliedPredicate xPred xArgs) (AppliedPredicate yPred yArgs)
              | xPred == yPred = unify subs xArgs yArgs
  unify _ _ _ = Nothing -- I'm using Nothing for F (failure)

-- for each : list something might unify on the left or right, is that safe?
tryBothUnify :: Unifies a => Substitution -> (a, a) -> Maybe Substitution
tryBothUnify subs (left, right) = -- What is the actual coolest way to write this
  listToMaybe $ catMaybes [unify subs left right, unify subs right left]

instance (Unifies a) => Unifies [a] where
  substitute subs = map (substitute subs)
  unify subs lhs rhs = foldM tryBothUnify subs $ zip lhs rhs

someTests :: IO ()
someTests = do
  -- pred(roy, tim) = pred(X, tim)
  print $ unify true (p"pred" ["roy", "tim"]) (p"pred" ["X", "tim"])
  -- p(X, X) = p(tim, tim)
  print $ unify true (p"p" ["X", "X"]) (p"p" ["tim", "tim"])
  -- p(X, X) = p(tim, roy)
  print $ unify true (p"p" ["X", "X"]) (p"p" ["tim", "roy"])
  -- f(X, X) = f(Y, 3)
  print $ unify true (p"f" ["X", "X"]) (p"f" ["Y", "3"])
  -- f(Y, 3) = F(X, X)
  print $ unify true (p"f" ["Y", "3"]) (p"f" ["X", "X"])


--------------------------------
---- MicroKanren?
--------------------------------
-- fresh, ===, disj, conj

type Var = Int
type Goal = Substitution -> State Var (Maybe Substitution)

(===) :: Unifies a => a -> a -> Goal
(a === b) subs = return $ unify subs a b

fresh :: (Var -> Goal) -> Goal
fresh f subs = do
  varIndex <- get
  put (varIndex + 1)
  f varIndex subs

-- This is supposed to just be mplus (or mappend?)
addSubsToState :: State Var (Maybe Substitution) -> Maybe Substitution -> State Var (Maybe Substitution)
addSubsToState stateF Nothing = stateF
addSubsToState stateF (Just subs) = do
  subs2 <- stateF
  return $ Just $ fromMaybe subs $ fmap (Map.union subs) subs2

-- This is supposed to just be "bind"
subsBind :: State Var (Maybe Substitution) -> Maybe Substitution -> State Var (Maybe Substitution)
subsBind _ Nothing = return Nothing --state $ \s -> (Nothing, s)
subsBind stateF (Just subs) = do
  subs2 <- stateF
  return $ fmap (Map.union subs) subs2

disj :: Goal -> Goal -> Goal
disj g1 g2 subs = do
  let r1 = g1 subs
  let r2 = g2 subs
  r1 >>= (addSubsToState r2)

conj :: Goal -> Goal -> Goal
conj g1 g2 subs = do
  let r1 = g1 subs
  let r2 = g2 subs
  r1 >>= (subsBind r2)

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
  subs <- maybeToList (unify true goal h)
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
