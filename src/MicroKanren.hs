module MicroKanren where

import Data.List (transpose)
import Data.Maybe
import Control.Monad

type LVar = Int

data Term = Var LVar | Atom String
  deriving (Eq, Show)

------------------------------------------
---- Unification
------------------------------------------

type Substitution = [(Term, Term)]

walk :: Substitution -> Term -> Term
walk s x@(Var _) = fromMaybe x $ do
  newVal <- lookup x s
  return $ walk s newVal
walk _ x = x

unify :: Term -> Term -> Substitution -> Maybe Substitution
unify lhs rhs subs = fmap (++ subs) $ unifyExpr (walk subs lhs) (walk subs rhs)
  where unifyExpr (Atom a) (Atom b) | a == b = return []
        unifyExpr l@(Var _) r = return [(l, r)]
        unifyExpr l r@(Var _) = return [(r, l)]
        unifyExpr _ _ = Nothing

--------------------------------
---- MicroKanren
---- remarkably true to the paper: http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf
--------------------------------

type Goal = (Substitution, Int) -> [(Substitution, Int)]

(===) :: Term -> Term -> Goal
a === b = \(subs, c) -> case unify a b subs of
  Nothing -> mzero
  Just subs' -> return (subs', c)

fresh :: (Term -> Goal) -> Goal
fresh f (subs, idx) = (f (Var idx)) (subs, (idx + 1))

disj :: Goal -> Goal -> Goal
disj g1 g2 sc = (concat . transpose) [(g1 sc), (g2 sc)]

conj :: Goal -> Goal -> Goal
conj g1 g2 sc = (g1 sc) >>= g2

emptyState :: (Substitution, Int)
emptyState = ([], 0)

-------------------------------------
----- Tests
-------------------------------------

aAndB :: Goal
aAndB = conj a b
  where a = fresh (\q -> q === (Atom "7"))
        b = fresh (\q -> disj
                          (q === (Atom "5"))
                          (q === (Atom "6")))

fives :: Term -> Goal
fives x = disj (x === (Atom "5")) (fives x)

sixes :: Term -> Goal
sixes x = disj (x === (Atom "6")) (sixes x)

fivesOrSixes :: Goal
fivesOrSixes = fresh $ \x -> disj (fives x) (sixes x)

mkTests :: IO ()
mkTests = do
  print $ aAndB emptyState
  print $ take 4 $ (fives (Var 0)) emptyState
  print $ take 6 $ fivesOrSixes emptyState
