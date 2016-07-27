[MicroKanren](http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf)
is a "minimal functional core for relational programming." It's kind of
like an embedded DSL for expressing logical and relational constraints,
coupled with a simple mechanism to solve them. Implementing a
MicroKanren is a fantastic way to really internalize the fundamentals of
logic programming. Here I'm going to walk you through my implementation
in Haskell.

Let's get set up:

``` haskell
module MicroKanren where
import Data.List (transpose)
import Data.Maybe (fromMaybe)
```

These occur up at the front mostly for bookkeeping. I'll explain them
where they're used later. By the end of this, we'll be able to make
logic programs that look like the following:

``` haskell
aAndB :: Goal
aAndB = conj (fresh (\a -> a === (Atom "7")))
             (fresh (\b -> disj
                         (b === (Atom "5"))
                         (b === (Atom "6"))))
```

`aAndB` is a logic program that when run, will return assignments for
logic variables such that the logic variable `a` can be substituted with
7 and the second logic variable `b` will be substituted with either 5 or
6. This example is fairly primitive, and yet it includes the entire
microKanren API. As you can see, the only objects in microKanren are
either logic variables (`Var`s) or `Atom`s:

``` haskell
data Term = Var Int | Atom String
  deriving (Eq, Show)
```

Turns out all we need to represent a logic var is a kind of ID, which I
don't think makes for particularly pleasing output but the reduction
here helps illustrate the truly minimal core of microKanren.

``` haskell
type Substitution = [(Term, Term)]
```

Logic programs output pairs of variable bindings that satisfy the input
program (proram is another word here for list of equations or
constraints). We call a complete list of these satisfying some program a
Substitution.

``` haskell
walk :: Substitution -> Term -> Term
walk s x@(Var _) = fromMaybe x $ fmap (walk s) $ lookup x s
walk _ x = x
```

When we want to find out what a variable is referring to in our
substitution, we use walk. Walk is so-called because it recursively
looks up any transitive definitions, e.g. X = Y = Z, spitting out Z when
asked what X means. Here's an example:

    > walk [((Var 0), (Var 1)), ((Var 1), (Atom "3"))] (Var 0)
    Atom "3"

Given these substitutions, walk will determine that Var 0 has been
substituted with Atom 3.

Here's the first meaty bit! Hold on to your butts:

``` haskell
unify :: Term -> Term -> Substitution -> Maybe Substitution
unify lhs rhs subs = fmap (++ subs) $ unifyExpr (walk subs lhs) (walk subs rhs)
  where unifyExpr (Atom a) (Atom b) | a == b = return []
        unifyExpr l@(Var _) r = return [(l, r)]
        unifyExpr l r@(Var _) = return [(r, l)]
        unifyExpr _ _ = Nothing
```

At a high level, unification takes an equation (i.e. `===`) with a left
and right-hand side and tries to find substitutions for the variables in
each side that will satisfy the equation. That's it! The code in
unifyExpr at the bottom of this block tells us what to do with each
possible pairing. Atoms are equal if their contents are equal. If we
have a logic Var on either side, we try substituting the Var with its
pair on the right hand side. Anything else doesn't unify.

The line above unifyExpr starting with fmap is a little scary at first,
but bear with me. Furthest to the right we apply our substitutions to
the left and right hand sides with `walk`. This just gives us new terms
to give to unifyExpr. unifyExpr returns a Maybe Substitution, meaning we
might fail to unify with Nothing or we might return a new substitution.
We use fmap on the Maybe monad to add the new substitutions to the ones
returned by unifyExpr, if there were any.

MicroKanren has this big concept of a goal, defined here:

``` haskell
type Goal = (Substitution, Int) -> [(Substitution, Int)]
```

A goal is just a function that accepts a `Substitution` and an integer
representing the current logic variable depth and returns a list of
these. We will be composing goals in the future, so it's important that
they accept both our set of existing substitutions and our current logic
variable depth. Goals return a list of new substitutions that satisfy
the goal, along with their associated logic variable depths, which can
be used for further composition.

Now we get to the bread and butter of our API, `===`:

``` haskell
(===) :: Term -> Term -> Goal
(a === b) (subs, c) =
  case unify a b subs of
    Nothing -> []
    Just subs' -> return (subs', c)
```

`===` is used to set two sides of an equation equal to each other. Under
the hood, it then returns a Goal, which as we remember above is a
function from a substitution and logic variable depth to a list of
satisfying substitutions. If we fail to unify, we return an empty list
which the microKanren paper refers to as "mzero" (because apparently the
author is a Haskell person at heart and is referring to the
[MonadPlus](https://wiki.haskell.org/MonadPlus) instance for List. This
is the same as the mzero from Monoid, if that helps. My 2-second summary
is that MonadPlus has an additive identity called `mzero` and an
addition operation called `mplus`. For lists this is just empty list and
`++`, which concatenates one list with another).

``` haskell
fresh :: (Term -> Goal) -> Goal
fresh f (subs, idx) = (f (Var idx)) (subs, (idx + 1))
```

Fresh allows the user to introduce new logic variables. It ends up being
used like this:

    fresh (\newLvar -> <stuff with newLvar...>)

where that `\newLvar` syntax is just defining an anonymous function.

Disjunction and conjunction are the only two operators you need in
microKanren, and they just compose other goals with each other.
Disjunction (aka `or`) is interesting because the naive implementation
here would substitute `mplus` for `(concat . transpose)`. `mplus` is our
friend from MonadPlus above, and with lists just concatenates them
together. What this would do in this case is read all of the possible
substitutions from g1 (the first goal) and after that one is exhausted,
read all of the ones from g2. What we'd actually like to do though is
alternate between the two to give us behavior more similar to
breadth-first search. This way if we have some goals with infinite
possible substitutions, we still get to see examples from all of the
possible ways to satisfy a disjunction and not just the first way.

At this point the microKanren scheme implementation would introduce a
streams concept that they would use to represent infinite results.
Haskell is lazy by default though, so we don't have to do anything like
that. We just use normal list operations to achieve the same thing.
[`transpose`](https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-List.html#v:transpose)
does what it sounds like if you imagine that the list of goals as a 2D
array or matrix - it creates a list where the first element is a list of
all of the first elements from each list it was input, and the 2nd
element is a list of all of the 2nd elements, and so on. We then concat
all of these together to get a list of alternating goal-satisfying
substitutions

``` haskell
disj :: Goal -> Goal -> Goal
disj g1 g2 sc = (concat . transpose) [(g1 sc), (g2 sc)]
```

Conjunction just feeds the resultant substitutions from g1 into g2 with
the `bind` (`>>=`) operator. This is why we needed both the substitution
and the logic variable depth returned from all goals - we want to sort
of continue the process on in further goals. Each goal is a valid logic
program by itself and you need its progress in logic variable bindings
in order to compose them.

``` haskell
conj :: Goal -> Goal -> Goal
conj g1 g2 sc = g1 sc >>= g2
```

Here we create the traditional empty state we can pass to goals, and
we're ready to start running tests!

``` haskell
emptyState :: (Substitution, Int)
emptyState = ([], 0)

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
```

This prints out the following:

    [([(Var 1,Atom "5"),(Var 0,Atom "7")],2),([(Var 1,Atom "6"),(Var 0,Atom "7")],2)]
    [([(Var 0,Atom "5")],0),([(Var 0,Atom "5")],0),([(Var 0,Atom "5")],0),([(Var 0,Atom "5")],0)]
    [([(Var 0,Atom "5")],1),([(Var 0,Atom "6")],1),([(Var 0,Atom "5")],1),([(Var 0,Atom "6")],1),([(Var 0,Atom "5")],1),([(Var 0,Atom "6")],1)]

The first result we talked about above at the definition of `aAndB`. The
next one successfully takes the first 4 substitutions (all the same)
from a list of infinite substitutions generated by the `fives` goal.

The last one demonstrates our nifty BFS search strategy - it alternates
between solutions that set Var 0 to 5 and solutions that set Var 0 to 6.

I hope you enjoyed; feel free to submit pull requests or otherwise
comment on this! This file was generated from [this literate Haskell
file](../src/MicroKanren.lhs)
