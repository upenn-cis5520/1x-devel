{-
---
fulltitle: "Optional exercise: DFS using the state monad"
---
-}

module Graph where

{-
In this module we'll look at the depth-first search algorithm on arbitrary graphs as
an example of using the State Monad. Often, when traversing a graph, you need to keep
track of what nodes in the graph that you have already seen so that you can avoid
cycles. This is a perfect opportunity to use `State`.

For these examples, we'll use finite sets and finite maps. The Haskell
`containers` library has efficient implementations of both of these as purely
functional data structures that we can import.
-}

import Control.Applicative
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust, fromMaybe)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import State (State, evalState, get, modify)

{-
Nodes in our graphs will be just identification numbers today, for simplicity.
(In a more general library they could store other sorts of information.)
-}

type Node = Int

{-
DFS trees
---------

As a warm-up, let's review depth-first searching a tree structure
for a particular node identifier. This data structure for trees below associates a node identifier with each `B`ranch and lets
that branch have *any* number of children.
-}

data Tree = B Node [Tree] deriving (Eq, Show)

{-
If the list is empty in a branch, then it represents a leaf node, with no children. Otherwise the list contains all of the subtrees of the given branch.

Here's an example tree:
-}

tree :: Tree
tree = B 1 [B 2 [B 6 [B 9 [], B 5 [B 10 []]]], B 3 []]

{-
Searching this tree for a particular node requires two mutually
recursive helper functions: one for trees and one for lists of
trees. Note that this `search` operation stops as soon as it finds
the goal node.
-}

-- >>> dfsTree tree 10
-- True

-- >>> dfsTree tree 4
-- False

dfsTree :: Tree -> Node -> Bool
dfsTree t goal = search t
  where
    search :: Tree -> Bool
    search (B v ws) = v == goal || searchList ws

    searchList :: [Tree] -> Bool
    searchList [] = False
    searchList (w : ws) = search w || searchList ws

{-
NOTE: we could replace `searchList` by `any search`, but we'll
keep it this way for comparison with the code below.

Depth-first search for trees makes elegant use of tree recursion. We don't need to keep track of where we are during the search because that
information is automatically stored on the call stack during the
recursive traversal of the tree. As we consider depth-first search of graphs below, we'll want to keep this behavior and use recursion to track
our progress through the graph traversal.

Representing graphs using adjacency lists
-----------------------------------------

Now let's switch to graphs.
We'll use an *adjacency list* representation.

A (directed) graph is then just a finite map that records all of the adjacent
nodes for each node in the graph.
-}

type Graph = Map Node [Node]

{-
For example, we can construct a graph with 12 nodes as follows. Each of these
nodes has 1, 2, or 3 neighbors.  If you look closely you can get from 1 to 10, but
you cannot get from 1 to 4.
-}

graph :: Graph
graph =
  Map.fromList
    [ (1, [2, 3]),
      (2, [6, 5, 1]),
      (3, [1]),
      (4, [7, 8]),
      (5, [9, 10, 2]),
      (6, [2, 9, 5]),
      (7, [4, 11, 12]),
      (8, [4]),
      (9, [6]),
      (10, [5]),
      (11, [7]),
      (12, [7])
    ]

{-
To find the list of adjacent nodes in a graph, we can use the `lookup` function
from the finite map library. If a node is not found in the map, we'll just
say that it has no adjacent nodes.
-}

-- >>> adjacent graph 5
-- [9,10,2]
adjacent :: Graph -> Node -> [Node]
adjacent g n = fromMaybe [] (Map.lookup n g)

{-

Now, here is the pseudocode for depth-first search from [wikipedia (recursive version)](https://en.wikipedia.org/wiki/Depth-first_search).
This pseudocode traverses the graph, but doesn't compute anything interesting.

            procedure DFS(G, v) is
                label v as discovered
                for all directed edges from v to w that are in G.adjacentEdges(v) do
                    if vertex w is not labeled as discovered then
                        recursively call DFS(G, w)

We can modify this pseudocode so that it searches for a "goal" node and then returns whether
it has found that node. We also want it to stop as soon as the goal is found. Here it looks,
still in pseudocode.

            procedure DFS(G, v) is
                if v is the goal, return true
                label v as discovered
                for all directed edges from v to w that are in G.adjacentEdges(v) do
                    if vertex w is not labeled as discovered && we haven't yet found the goal
                        recursively call DFS(G, w)

Often at this point, descriptions of DFS algorithms introduce a stack data structure as part
of their implementation and rephrase the code using a loop instead of recursion. However,
this data structure is not necessary: the call stack in the recursive implementation plays
the same role. In the rest of this module, we'll use the `State` monad to implement
a recursive implementation of the pseudocode shown above.

Keeping track of discovered nodes
---------------------------------

The state that we need to keep track of is the set of nodes that we have discovered.
Let's define that type plus some associated operations.
-}

type Store = Set Node

-- | The initial store, a set that contains just the root node
initStore :: Node -> Store
initStore = Set.singleton

-- | Mark a node as discovered in the store
label :: Node -> Store -> Store
label = Set.insert

-- | Find out whether we have labeled a node
isLabeled :: Node -> Store -> Bool
isLabeled = Set.member

{-
Here is our first implementation DFS. The action is in the recursive
function `search` that begins the search from a vertex v,
along with its helper `searchList` that goes through all
vertices adjacent to v.
-}

-- >>> dfs graph 1 10
-- True

-- >>> dfs graph 1 4
-- False

-- | Depth-first search for a goal node in a graph
-- with store passing
dfs :: Graph -> Node -> Node -> Bool
dfs g root goal = fst (search root (initStore root))
  where
    search :: Node -> Store -> (Bool, Store)
    search v s =
      if v == goal
        then (True, s)
        else
          let s' = label v s
           in searchList (adjacent g v) s'

    searchList :: [Node] -> Store -> (Bool, Store)
    searchList [] s = (False, s)
    searchList (w : ws) s =
      if isLabeled w s
        then (False, s) -- already searched here
        else
          let (b, s') = search w s
           in if b
                then (True, s') -- found it in recursive call
                else searchList ws s' -- search other children

{-
At this point, make sure that you understand why we need to pass
the state through the computation. What happens if the recursive call
to `searchList` uses state `s` instead of `s'`?

Now, let's revise the above using the State monad. To make our
code simpler, we can define the following helper function. This
function lets us ask questions about the current store.
-}

-- | Find out a fact about the current state
query :: (Store -> Bool) -> State Store Bool
query f = f <$> get

{-
Use `do`-notation, `query` and `modify` to make state passing implicit.
-}

-- >>> dfsState graph 1 10

-- >>> dfsState graph 1 4

dfsState :: Graph -> Node -> Node -> Bool
dfsState g root goal = evalState (search root) (initStore root)
  where
    search :: Node -> State Store Bool
    search = undefined

    searchList :: [Node] -> State Store Bool
    searchList = undefined

{-
Now refactor the `dfs` implementation again, this time
using the short-circuiting boolean operations, defined below, that
work in any monad. These operators should replace uses of
`if-then-else` in your implementation above.

-}

(<||>) :: Monad m => m Bool -> m Bool -> m Bool
m1 <||> m2 = do
  b <- m1
  if b then return True else m2

(<&&>) :: Monad m => m Bool -> m Bool -> m Bool
m1 <&&> m2 = do
  b <- m1
  if b then m2 else return False

{-
(Aside, you might be tempted to define these operations using `liftA2`
from the `Applicative` class. However, the applicative function is not
short-circuiting.)
-}

-- >>> dfsState2 graph 1 10
-- True

-- >>> dfsState2 graph 1 4
-- False

dfsState2 :: Graph -> Node -> Node -> Bool
dfsState2 g root goal = evalState (search root) (initStore root)
  where
    search :: Node -> State Store Bool
    search = undefined
    searchList :: [Node] -> State Store Bool
    searchList = undefined

-- >>> :t foldM @[] @(State Store)
-- foldM @[] @(State Store) :: (b -> a -> State Store b) -> b -> [a] -> State Store b

{-
Dfs applications: Spanning Tree
-------------------------------

For any depth-first search, we can return a trace of the search as a
spanningTree (also called a [Trémaux tree](https://en.wikipedia.org/wiki/Tr%C3%A9maux_tree)).
For example, if we start with node `1`, the trace that corresponds to a
full depth first search is the tree that we saw above.
-}

-- >>> spanningTree graph 1
-- B 1 [B 2 [B 6 [B 9 [],B 5 [B 10 []]]],B 3 []]

{-
Use the `State` monad to define the `spanningTree` function so that it
searches the reachable part of a graph from a specified node and
returns all found nodes in a tree.

Hint: I found it nice to define a monadic version of the (:)
data constructor to use in my solution.
-}

(<:>) :: Monad f => f a -> f [a] -> f [a]
(<:>) = liftM2 (:)

spanningTree :: Graph -> Node -> Tree
spanningTree = undefined

{-
Connected components
--------------------

Now let's use depth-first search to find the connected
components of the graph. In this operation, we'll want to
visit every single node in the graph and separate them into
groups that are connected (not strongly) with eachother.

The key insight for our implementation below is that we need to both
keep track of which nodes have been visited *and* quickly find one
that we have not yet done. What this means is that we'll use the same
type of store in our algorithm, but this time we'll start with all of the
nodes in the graph as the initial store and remove them as we go.
-}

-- | initialize the store with *all* nodes in the graph
initWorkList :: Graph -> Store
initWorkList = Map.keysSet

-- | mark a node as finished by *removing* it from the store
markDone :: Node -> Store -> Store
markDone = Set.delete

-- | a node has been processed if it is no longer in the store
isDone :: Node -> Store -> Bool
isDone n s = not (Set.member n s)

{-
Now, finish the implementation of the connected component algorithm.
-}

-- >>> connected graph
-- [B 1 [B 2 [B 6 [B 9 [],B 5 [B 10 []]]],B 3 []],B 4 [B 7 [B 11 [],B 12 []],B 8 []]]

connected :: Graph -> [Tree]
connected g = evalState loop (initWorkList g)
  where
    -- loop through all nodes in the graph until they have all
    -- been visited.
    loop :: State Store [Tree]
    loop = do
      p <- get
      case Set.elems p of
        [] -> return []
        (n : _) -> visit n <:> loop

    visit :: Node -> State Store Tree
    visit = undefined

    visitList :: [Node] -> State Store [Tree]
    visitList = undefined

{-
Now modify the above function so that it returns the two
subgraphs instead of the spanning trees of the connected
components.
-}

-- >>> connectedGraph graph
-- [fromList [(1,[2,3]),(2,[6,5,1]),(3,[1]),(5,[9,10,2]),(6,[2,9,5]),(9,[6]),(10,[5])],fromList [(4,[7,8]),(7,[4,11,12]),(8,[4]),(11,[7]),(12,[7])]]

connectedGraph :: Graph -> [Graph]
connectedGraph g = evalState loop (initWorkList g)
  where
    -- loop through all nodes in the graph until they have all
    -- been visited.
    loop :: State Store [Graph]
    loop = do
      p <- get
      case Set.elems p of
        [] -> return []
        (n : _) -> visit n <:> loop

    visit :: Node -> State Store Graph
    visit = undefined

    visitList :: [Node] -> State Store Graph
    visitList = undefined

{-
DAGs and Topological sorting
----------------------------

The wikipedia article on topological sorting provides this pseudo code
for a dfs-based algorithm.

        procedure Toposort(graph):
            L ← Empty list that will contain the sorted nodes
            while exists nodes without a permanent mark do
                select an unmarked node n
                visit(n)

            function visit(node n)
                if n has a permanent mark then
                    return
                if n has a temporary mark then
                    stop   (graph has at least one cycle)

                mark n with a temporary mark

                for each node m with an edge from n to m do
                    visit(m)

                remove temporary mark from n
                mark n with a permanent mark
                add n to head of L

This code appears quite complex and very stateful: we need two sorts of marks
plus a mutable list in the implementation.  The permanent marks keep track of
whether the node has been visited and already appears in the output
(note that we add the mark for n at the same time as we add it to the list).
The temporary marks track the nodes that we have see in the current traversal
in a stack-based order: note how they are marked before the recursive call
to the children and unmarked after the recursive call finishes. These temporary
marks identify back edges in the traversal, so that the algorithm can detect cycles.

On closer examination, the only state that is really needed for this
algorithm is the permanent marks that detect cycles. The temporary marks
can be represented with an extra argument on the call stack and the
list can be constructed as the result of the computation.

As a warm-up to see how this might work, let's write a function that
detects whether a given graph is a DAG.
-}

dag :: Graph
dag =
  Map.fromList
    [ (1, [2, 3]),
      (2, [6, 5]),
      (3, []),
      (4, [7, 8]),
      (5, [9, 10]),
      (6, [9]),
      (7, [11, 12]),
      (8, []),
      (9, []),
      (10, []),
      (11, []),
      (12, [])
    ]

-- >>> isDag graph
-- False

-- >>> isDag dag
-- True

{-
Like the `connectedGraph` function above, the `isDag` operation below uses the
store to maintain a working set of nodes that need to be visited.

New this time is that the visit function has an extra parameter:
the set of nodes that we've seen on this iteration of the loop.
When we visit a node, we need to first check if we have already
seen it---if so, we've found a back edge in the graph and need to
return false. If we haven't seen the node before and we haven't
yet processed it, we need to visit all of its neighbors,
remember that we've seen it in this call.

Unlike our previous traversals, we cannot mark this node as done until
we have checked all of its adjacent nodes: we are looking for a back edge.
-}

isDag :: Graph -> Bool
isDag g = evalState loop (initWorkList g)
  where
    loop :: State Store Bool
    loop = do
      p <- get
      case Set.elems p of
        [] -> return True
        (n : _) -> visit Set.empty n <&&> loop

    visit :: Set Node -> Node -> State Store Bool
    visit seen v
      | Set.member v seen = return False -- back edge, it's not a DAG
      | otherwise =
        visitList (Set.insert v seen) (adjacent g v)
          <* modify (markDone v)

    visitList :: Set Node -> [Node] -> State Store Bool
    visitList seen [] = return True
    visitList seen (w : ws) = do
      (query (isDone w) <||> visit seen w) <&&> visitList seen ws

{-
Now, given this structure, see if you can modify it to
define a topological sort. In the case that the input is *not* a dag,
you can use the "error" function to fail.
In the case that the input is a dag, this function should return each node
in sequence.
-}

-- >>> topoSort dag
-- [1,2,6,9,5,10,3,4,7,11,12,8]

topoSort :: Graph -> [Node]
topoSort = undefined

{-
For more in-depth functional approach to Graph algorithms, see the draft book
"Algorithms: Parallel and Sequential" by Umut A. Acar and Guy E. Blelloch
available at this url: https://sites.google.com/site/alphalambdabook/
-}
