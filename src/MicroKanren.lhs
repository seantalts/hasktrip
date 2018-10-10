Introduction
==============

[MicroKanren](http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf) is a "minimal functional core for relational programming." It's kind of like an embedded DSL for expressing logical and relational constraints, coupled with a simple mechanism to solve them. Implementing a MicroKanren is a fantastic way to really internalize the fundamentals of logic programming. Here I'm going to walk you through my implementation in Haskell.

Let's get set up:

> module MicroKanren where
> import Data.List (transpose)

These occur up at the front mostly for bookkeeping. I'll explain them where they're used later.

By the end of this, we'll be able to make logic programs that look like the following:

> aAndB :: Goal
> aAndB = conj (fresh (\a -> a === (Atom "7")))
>              (fresh (\b -> disj
>                          (b === (Atom "5"))
>                          (b === (Atom "6"))))

`aAndB` is a logic program that when run, will return assignments for logic variables such that the logic variable `a` can be substituted with 7 and the second logic variable `b` will be substituted with either 5 or 6. This example is fairly primitive, and yet it includes the entire microKanren API. As you can see, the only objects in microKanren are either logic variables (`Var`s) or `Atom`s:

> data Term = Var Int | Atom String
>   deriving (Eq, Show)

Turns out all we need to represent a logic var is a kind of ID, which I don't think makes for particularly pleasing output but the reduction here helps illustrate the truly minimal core of microKanren.

> type Substitution = [(Term, Term)]

Logic programs output pairs of variable bindings that satisfy the input program (proram is another word here for list of equations or constraints). We call a complete list of these satisfying some program a Substitution. You can think of this as an associative list, where each pair is the first element set equal to the second element.

> walk :: Substitution -> Term -> Term
> walk s x@(Var _) = maybe x (walk s) (lookup x s)
> walk _ x = x

When we want to find out what a variable is referring to in our substitution, we use walk. Walk is so-called because it recursively looks up any transitive definitions, e.g. X = Y = Z, spitting out Z when asked what X means. Here's an example:

    > walk [((Var 0), (Var 1)), ((Var 1), (Atom "3"))] (Var 0)
    Atom "3"

Given these substitutions, walk will determine that Var 0 has been substituted with Atom 3.

Unification
=================

Here's the first meaty bit! Hold on to your butts:

> unify :: Term -> Term -> Substitution -> Maybe Substitution
> unify lhs rhs subs = (++ subs) <$> unifyExpr (walk subs lhs) (walk subs rhs)
>   where unifyExpr (Atom a) (Atom b) | a == b = return []
>         unifyExpr l@(Var _) r = return [(l, r)]
>         unifyExpr l r@(Var _) = return [(r, l)]
>         unifyExpr _ _ = Nothing

Okay, let's step back for a second. We'll take the 30,000 foot view and then drill up from the bottom and hope we meet in the middle.

At a high level, unification takes an equation (e.g. `X === 7`) with a left and right-hand side and tries to find substitutions for the variables in each side that will satisfy the equation. That's it! The code in `unifyExpr` at the bottom of this block tells us what to do with each possible pairing. Atoms are equal if their contents are equal. If we have a logic Var on either side, we try substituting the Var with its pair on the other side. Anything fails to unify, meaning we couldn't find a way to make the two sides of the equation equal to each other.

The line above `unifyExpr` starting with `(++ subs)` is a little scary at first, but bear with me. Furthest to the right we apply our substitutions to the left and right hand sides with `walk`. This just gives us new terms to give to `unifyExpr`. This returns a `Maybe Substitution`, meaning we might fail to unify with `Nothing` or we might return a new substitution. We use `<$>` (which is basically the Control.Applicative version of `fmap`) on the Maybe monad to add the new substitutions to the ones returned by `unifyExpr`, if there were any. The way `fmap` and `<$>` work, if we're dealing with `Nothing` then we just pass Nothing right along, and we only add the new substitutions to the existing substitutions if we found some set of substitutions that satisfied our equation.

MicroKanren has this big concept of a goal, used to denote basically an additional constraint that, given some pre-existing context for the logical program, can generate additional possible (i.e. satisfying) contexts. A goal is defined here:

> type Goal = (Substitution, Int) -> [(Substitution, Int)]

As you can see, a goal is just a function that accepts a `Substitution` and an integer representing the index of the next available logic variable and returns a list of these. We will be composing goals in the future, so it's important that they accept both our set of existing substitutions and our current logic variable index. Goals return a list of new substitutions that satisfy the goal, along with their respective logic variable indices, which can be used for further composition. We will see this further composition with `conj`.

Short interlude into logic variable numberings
-----------------------------------------------

We're passing around these logic variable indices because as these integers are our only method of identifying logic variables, when we use `fresh` we will need to create a new logic variable and we have to know what numbers are available for its assignment. In a less functional approach (in a less functional language) you could imagine this being a global variable that is automatically incremented when new logic variables are created, much like an auto-increment integer primary key id in a relational database. The semantics are not exactly the same (as you may have noticed, our indices are dependent on scope, which is how `disj` returns multiple bindings for the same logic variable. More on that later!

API
====

Now we get to the bread and butter of our API, `===`:

> (===) :: Term -> Term -> Goal
> (a === b) (subs, c) =
>   case unify a b subs of
>     Nothing -> []
>     Just subs' -> return (subs', c)

`===` is used to set two sides of an equation equal to each other. Under the hood, it then returns a Goal, which as we remember above is a function from a substitution and logic variable index to a list of satisfying substitutions. If we fail to unify, we return an empty list which the microKanren paper refers to as "mzero" (because apparently the author is a Haskell person at heart and is referring to the [MonadPlus](https://wiki.haskell.org/MonadPlus) instance for List. This is the same as the mzero from Monoid, if that helps. My 2-second summary is that MonadPlus has an additive identity called `mzero` and an addition operation called `mplus`. For lists this is just empty list and `++`, which concatenates one list with another).

> fresh :: (Term -> Goal) -> Goal
> fresh f (subs, idx) = (f (Var idx)) (subs, (idx + 1))

Fresh allows the user to introduce new logic variables. It ends up being used like this:

    fresh (\newLvar -> <stuff with newLvar...>)

where that `\newLvar` syntax is just defining an anonymous function.

Disjunction and conjunction are the only two operators you need in microKanren, and they just compose other goals with each other. Disjunction (aka `or`) is interesting because the naive implementation here would substitute `mplus` for `(concat . transpose)`. `mplus` is our friend from MonadPlus above, and with lists just concatenates them together. What this would do in this case is read all of the possible substitutions from g1 (the first goal) and after that one is exhausted, read all of the ones from g2. What we'd actually like to do though is alternate between the two to give us behavior more similar to breadth-first search. This way if we have some goals with infinite possible substitutions, we still get to see examples from all of the possible ways to satisfy a disjunction and not just the first way.

At this point the microKanren scheme implementation would introduce a streams concept that they would use to represent infinite results. Haskell is lazy by default though, so we don't have to do anything like that. We just use normal list operations to achieve the same thing. [`transpose`](https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-List.html#v:transpose) does what it sounds like if you imagine that the list of goals as a 2D array or matrix - it creates a list where the first element is a list of all of the first elements from each list it was input, and the 2nd element is a list of all of the 2nd elements, and so on. We then concat all of these together to get a list of alternating goal-satisfying substitutions from each of the two goals g1 and g2.

> disj :: Goal -> Goal -> Goal
> disj g1 g2 sc = (concat . transpose) [(g1 sc), (g2 sc)]

Conjunction just feeds the resultant substitutions from g1 into g2 with the `bind` (`>>=`) operator. This is why we needed both the substitution and the logic variable index returned from all goals - we want to sort of continue the process on in further goals. Each goal is a valid logic program by itself and you need its progress in logic variable bindings in order to compose them.

> conj :: Goal -> Goal -> Goal
> conj g1 g2 sc = g1 sc >>= g2

Tests and Examples
====================

Here we create the traditional empty state we can pass to goals, and we're ready to start running tests!

> emptyState :: (Substitution, Int)
> emptyState = ([], 0)
>
> fives :: Term -> Goal
> fives x = disj (x === (Atom "5")) (fives x)
>
> sixes :: Term -> Goal
> sixes x = disj (x === (Atom "6")) (sixes x)
>
> fivesOrSixes :: Goal
> fivesOrSixes = fresh $ \x -> disj (fives x) (sixes x)
>
> mKTests :: IO ()
> mKTests = do
>   print $ aAndB emptyState
>   print $ take 4 $ (fives (Var 0)) emptyState
>   print $ take 6 $ fivesOrSixes emptyState

This prints out the following:

    [([(Var 1,Atom "5"),(Var 0,Atom "7")],2),([(Var 1,Atom "6"),(Var 0,Atom "7")],2)]
    [([(Var 0,Atom "5")],0),([(Var 0,Atom "5")],0),([(Var 0,Atom "5")],0),([(Var 0,Atom "5")],0)]
    [([(Var 0,Atom "5")],1),([(Var 0,Atom "6")],1),([(Var 0,Atom "5")],1),([(Var 0,Atom "6")],1),([(Var 0,Atom "5")],1),([(Var 0,Atom "6")],1)]

The first result we talked about above at the definition of `aAndB`. The next one successfully takes the first 4 substitutions (all the same) from a list of infinite substitutions generated by the `fives` goal.

The last one demonstrates our nifty BFS search strategy - it alternates between solutions that set Var 0 to 5 and solutions that set Var 0 to 6.

I hope you enjoyed; feel free to submit pull requests or otherwise comment on this! This file was generated from [this literate Haskell file](../src/MicroKanren.lhs), which looks super ugly on github but is rendered using [this pandoc Makefile](../Makefile) into this pretty markdown file :)
