-- Inf2d Assignment 1 2019-2020
-- Matriculation number: s1803764
-- {-# OPTIONS -Wall #-}


module Inf2d1 where

import Data.Maybe --imported by me
import Data.List (sortBy, elemIndices, elemIndex, nub)
import ConnectFourWithTwist




{- NOTES:

-- DO NOT CHANGE THE NAMES OR TYPE DEFINITIONS OF THE FUNCTIONS!
You can write new auxillary functions, but don't change the names or type definitions
of the functions which you are asked to implement.

-- Comment your code.

-- You should submit this file when you have finished the assignment.

-- The deadline is the  10th March 2020 at 3pm.

-- See the assignment sheet and document files for more information on the predefined game functions.

-- See the README for description of a user interface to test your code.

-- See www.haskell.org for haskell revision.

-- Useful haskell topics, which you should revise:
-- Recursion
-- The Maybe monad
-- Higher-order functions
-- List processing functions: map, fold, filter, sortBy ...

-- See Russell and Norvig Chapters 3 for search algorithms,
-- and Chapter 5 for game search algorithms.

-}

-- Section 1: Uniform Search

-- The Node type defines the position of the agent on the graph.
-- The Branch type synonym defines the branch of search through the graph.
type Node = Int
type Branch = [Node]
type Graph= [Node]

numNodes::Int
numNodes = 4

-- The next function should return all the possible continuations of input search branch through the graph.
-- Your function should return an empty list if the input search branch is empty.
-- This implementation of next function does not backtrace branches.
next::Branch -> Graph ->  [Branch]
next [] _ = []
next _ [] = []
next (b:br) (g:gs)
  | b < g = nub ((g:b:br) : next (b:br) gs)   -- nub function used to eliminate any duplicate branch continuations
  | b > g = nub ((g:b:br) : next (b:br) gs)   -- nub function used to eliminate any duplicate branch continuations
  | otherwise = next (b:br) gs


next1::Branch -> Graph -> [Branch]
next1 [] _ = []
next1 _ [] = []
next1 branch graph = expandBranches [branch] graph (exploredNodes branch)


-- ***Still need to account for whether the given transition is valid or not
-- ***Also need to check whether the tail or the head of a given branch is relevant

-- |The checkArrival function should return true if the current location of the robot is the destination, and false otherwise.
checkArrival::Node-> Node -> Bool
checkArrival destination curNode
  | destination == curNode = True
  | otherwise = False


-- Section 3 Uninformed Search
-- | Breadth-First Search
-- The breadthFirstSearch function should use the next function to expand a node,
-- and the checkArrival function to check whether a node is a destination position.
-- The function should search nodes using a breadth first search order.

breadthFirstSearch::Graph -> Node->(Branch ->Graph -> [Branch])->[Branch]->[Node]->Maybe Branch
breadthFirstSearch [] _ _ _ _ = Nothing
breadthFirstSearch _ _ _ [] _ = Nothing
breadthFirstSearch g dest next branchList exploredList = bfs g dest next (parseSAInputs branchList g) exploredList


bfs::Graph -> Node ->(Branch -> Graph -> [Branch]) -> [Branch] -> [Node] -> Maybe Branch
bfs [] _ _ _ _ = Nothing
bfs _ _ _ [] _ = Nothing
bfs graph destN next branchList exploredList
  | branchArrived branchList destN /= Nothing = Just (reverse (tupleToList (flatten (findTransitions (maybeToBranch (branchArrived branchList destN)))) 0))
  | looping branchList graph exploredList = Nothing
  | otherwise = bfs graph destN next (expandBranches branchList graph exploredList) (totENodes (expandBranches branchList graph exploredList))



-- | Depth-Limited Search
-- The depthLimitedSearch function is similiar to the depthFirstSearch function,
-- except its search is limited to a pre-determined depth, d, in the search tree.
depthLimitedSearch::Graph ->Node->(Branch ->Graph-> [Branch])->[Branch]-> Int->[Node]-> Maybe Branch
depthLimitedSearch [] _ _ _ _ _ = Nothing
depthLimitedSearch _ _ _ [] _ _ = Nothing
depthLimitedSearch g destN next branches d exploredList = dfs g destN next (parseSAInputs branches g) d exploredList


dfs::Graph ->Node->(Branch ->Graph-> [Branch])->[Branch]-> Int->[Node]-> Maybe Branch
dfs [] _ _ _ _ _ = Nothing
dfs _ _ _ [] _ _ = Nothing
dfs graph destN next (b:branchList) depth exploredList
  | branchArrived (b:branchList) destN /= Nothing = Just (reverse (tupleToList (flatten (findTransitions (maybeToBranch (branchArrived (b:branchList) destN )))) 0)) --Checks if branch has arrived at destination node
  | otherwise = dfs graph destN next (ullUpdate (expPoss b graph depth exploredList) (branchList)) depth (nub ((totENodes (b:branchList)) ++ exploredList))


-- | Section 4: Informed search


-- | AStar Helper Functions

-- | The cost function calculates the current cost of a trace. The cost for a single transition is given in the adjacency matrix.
-- The cost of a whole trace is the sum of all relevant transition costs.
cost :: Graph ->Branch  -> Int
cost [] _ = 0
cost _ [] = 0
cost gr branch = sum (filter (/= 0) branch)


-- | The getHr function reads the heuristic for a node from a given heuristic table.
-- The heuristic table gives the heuristic (in this case straight line distance) and has one entry per node. It is ordered by node (e.g. the heuristic for node 0 can be found at index 0 ..)
getHr:: [Int]->Node->Int
getHr [] _ = -1
getHr hrTable node = hrTable !! node


-- | A* Search
-- The aStarSearch function uses the checkArrival function to check whether a node is a destination position,
---- and a combination of the cost and heuristic functions to determine the order in which nodes are searched.
---- Nodes with a lower heuristic value should be searched before nodes with a higher heuristic value.

aStarSearch::Graph->Node->(Branch->Graph -> [Branch])->([Int]->Node->Int)->[Int]->(Graph->Branch->Int)->[Branch]-> [Node]-> Maybe Branch
aStarSearch [] _ _ _ _ _ _ _ = Nothing
aStarSearch _ _ _ _ [] _ _ _ = Nothing
aStarSearch _ _ _ _ _ _ [] _ = Nothing
aStarSearch g destN next getHr hrTable cost branches exploredList = ass g destN next getHr hrTable cost (parseSAInputs branches g) exploredList

--REQUESTED A* ALGORITHM IMPLEMENTATION (returns the predicted most optimal trace)
ass::Graph->Node-> (Branch->Graph->[Branch]) -> ([Int]->Node->Int) ->[Int]-> (Graph->Branch->Int) ->[Branch]->[Node]-> Maybe Branch
ass [] _ _ _ _ _ _ _ = Nothing
ass _ _ _ _ [] _ _ _ = Nothing
ass _ _ _ _ _ _ [] _ = Nothing
ass g destN next getHr hrTable cost (b:branchList) eNodes
  | branchArrived (b:branchList) destN /= Nothing = Just (reverse (tupleToList (flatten (findTransitions (maybeToBranch (branchArrived (b:branchList) destN)))) 0))
  | orderedBranchExpansions b g eNodes hrTable /= [] = ass g destN next getHr hrTable cost ((orderedBranchExpansions b g eNodes hrTable) ++ (branchList)) eNodes
  | otherwise = ass g destN next getHr hrTable cost branchList eNodes


--TYPICAL A* ALGORITHM IMPLEMENTATION (returns the overall optimal trace)
assMinCost::Graph->Node->[Int]->[Branch]->[Node]-> Maybe Branch
assMinCost [] _ _ _ _ = Nothing
assMinCost _ _ [] _ _ = Nothing
assMinCost _ _ _ [] _ = Nothing
assMinCost g destN hrTable branchList eNodes = Just (cheapestTrace (ass1 g destN hrTable branchList eNodes) (costList (ass1 g destN hrTable branchList eNodes)))



-- *** does not give the overall the most efficient trace, but the predicted most efficient from the first state


-- | Section 5: Games
-- See ConnectFourWithTwist.hs for more detail on  functions that might be helpful for your implementation.



-- | Section 5.1 Connect Four with a Twist



-- The function determines the score of a terminal state, assigning it a value of +1, -1 or 0:
eval :: Game -> Int
eval game
  | checkWin game maxPlayer = 1
  | checkWin game minPlayer = -1
  | otherwise = 0


-- | The alphabeta function should return the minimax value using alphabeta pruning.
-- The eval function should be used to get the value of a terminal state.
alphabeta:: Role -> Game -> Int
alphabeta  player game = undefined



-- | OPTIONAL!
-- You can try implementing this as a test for yourself or if you find alphabeta pruning too hard.
-- If you implement minimax instead of alphabeta, the maximum points you can get is 10% instead of 15%.
-- Note, we will only grade this function IF YOUR ALPHABETA FUNCTION IS EMPTY.
-- The minimax function should return the minimax value of the state (without alphabeta pruning).
-- The eval function should be used to get the value of a terminal state.
minimax:: Role -> Game -> Int -- predicted best NEXT move based on brute force probability
minimax player game
  | terminal game = eval game
  | checkWin game (switch player) = switch player
  | otherwise = minimax (switch player) (findBestMove player game)


{- Auxiliary Functions
-- Include any auxiliary functions you need for your algorithms below.
-- For each function, state its purpose and comment adequately.
-- Functions which increase the complexity of the algorithm will not get additional scores
-}

-- CONNECT FOUR HELPER FUNCTIONS

findBestMove::Role->Game->Game
findBestMove _ [] = []
findBestMove player game = findBM player (moveOptions (movesAndTurns game player) (switch player))

findBM::Role->[(Game,Double)]->Game --loopIndex input starts at 0,
findBM _ [] = []
findBM player moves
  | player == 1 = findBMMAX player moves (-2) []
  | player == 0 = findBMMIN player moves (2) []

findBMMAX::Role->[(Game,Double)]->Double->Game->Game
findBMMAX _ [] _ bstGame = bstGame
findBMMAX player (m:ms) maxVal bstGame
  | (snd m) > maxVal = findBMMAX player ms (snd m) (fst m)
  | otherwise = findBMMAX player ms maxVal bstGame

findBMMIN::Role->[(Game,Double)]->Double->Game->Game
findBMMIN _ [] _ bstGame = bstGame
findBMMIN player (m:ms) minVal bstGame
  | (snd m) < minVal = findBMMIN player ms (snd m) (fst m)
  | otherwise = findBMMIN player ms minVal bstGame

averageScore::[Int]->Double
averageScore [] = 0
averageScore xs = (fromIntegral (sum xs)) / (fromIntegral (length xs))

moveOptions::[Game]->Role->[(Game,Double)]
moveOptions [] _ = []
moveOptions (m:ms) player
  | (length (iterateTillTerm (movesAndTurns m player) (switch player))) == 0 = moveOptions ms player
  | otherwise = (m, averageScore (iterateTillTerm (movesAndTurns m player) (switch player))) : moveOptions ms player

iterateTillTerm::[Game]->Role->[Int]
iterateTillTerm [] _ = []
iterateTillTerm (g:gs) player
  | terminal g = eval g : iterateTillTerm gs player
  | checkWin g (switch player) = switch player : iterateTillTerm gs player
  | otherwise = iterateTillTerm (movesAndTurns g player) (switch player) ++ iterateTillTerm gs player

evalMove::Role->Game->Int
evalMove _ [] = 0
evalMove player game
  | terminal game = eval game
  | checkWin game player = player
  | otherwise = 0






-- BRANCH INPUT & OUTPUT PARSING : I orginally thought the input and output branches were represented as adjacency matrices
-- So instead of rewriting all my functions I created parsers to convert input and output values.
-- This is why there are supplementary functions in each search algorithm section.

tupleToList::[(Node,Node)]->Int->[Node] --Parsing correct node list outputs from branch adjacency matrix
tupleToList [] _ = []
tupleToList (n:ns) i
  | i == 0 = fst n : snd n : tupleToList ns 1
  | otherwise = snd n : tupleToList ns 1

parseSAInputs::[[Node]]->Graph->[Branch] --Parsing nodelist inputs into branch adjacency matrices
parseSAInputs [] _ = []
parseSAInputs _ [] = []
parseSAInputs (n:ns) graph
  | parseSAInput n == [] = fillBranch graph : parseSAInputs ns graph
  | otherwise = updateBranchIList graph (fillBranch graph) (turnTuplesIntoIndexes graph (parseSAInput n)) : parseSAInputs ns graph

parseSAInput::[Node]->[(Node,Node)] --Parsing nodelist inputs into list of tuple transitions
parseSAInput [] = []
parseSAInput [x] = []
parseSAInput (n1:n2:ns)
  | ns == [] = [(n1,n2)]
  | otherwise = (n1,n2) : parseSAInput (n2:ns)



-- A* SEARCH HELPER FUNCTIONS

cheapestTrace::[Branch]->[Int]->Branch
cheapestTrace [] _ = []
cheapestTrace _ [] = []
cheapestTrace branchList costList = branchList !! maybeToInt (elemIndex (minimum costList) costList)

costList::[Branch]->[Int]
costList [] = []
costList (b:bs) = (cost b b) : costList bs

ass1::Graph->Node->[Int]->[Branch]->[Node]-> [Branch]
ass1 [] _ _ _ _ = []
ass1 _ _ [] _ _ = []
ass1 _ _ _ [] _ = []
ass1 g destN hrTable (b:branchList) eNodes
  | branchArrived (b:branchList) destN /= Nothing = maybeToIntList (branchArrived (b:branchList) destN) : ass1 g destN hrTable (agUp branchList (maybeToIntList (branchArrived (b:branchList) destN))) eNodes
  | orderedBranchExpansions b g eNodes hrTable /= [] = ass1 g destN hrTable ((orderedBranchExpansions b g eNodes hrTable) ++ (branchList)) eNodes
  | otherwise = ass1 g destN hrTable branchList eNodes

agUp::[Branch] -> Branch -> [Branch]
agUp [] _ = []
agUp b [] = b
agUp (b:bs) result
  | (cost b b) + 1 >= (cost result result) = agUp bs result
  | otherwise = b : agUp bs result

orderedBranchExpansions:: Branch -> Graph -> [Node] -> [Int] -> [Branch]
orderedBranchExpansions [] _ _ _ = []
orderedBranchExpansions _ [] _ _ = []
orderedBranchExpansions _ _ _ [] = []
orderedBranchExpansions branch graph eNodes hrTable
  | expandBranch branch graph eNodes == [branch] = []
  | otherwise = orderByCost (expandBranch branch graph eNodes) (totCost (expandBranch branch graph eNodes) hrTable)

orderByCost:: [Branch] -> [Int] -> [Branch]
orderByCost [] _ = []
orderByCost _ [] = []
orderByCost branchList costList = branchList !! (maybeToInt (elemIndex (minimum costList) costList)) : orderByCost (deleteListEl branchList (maybeToInt (elemIndex (minimum costList) costList))) (deleteListEl costList (maybeToInt (elemIndex (minimum costList) costList)))

deleteListEl:: [a] -> Int -> [a] -- removes a list element at a given index
deleteListEl [] _ = []
deleteListEl list index = (take index list) ++ (drop (index+1) list)

totCost:: [Branch] -> [Int] -> [Int]
totCost [] _ = []
totCost _ [] = []
totCost (b:bs) hrTable = (cost b b) + (getHr hrTable (maybeToInt (findBranchEnd b))) : totCost bs hrTable



-- DFS HELPER FUNCTIONS

ullUpdate::Maybe [Branch] -> [Branch] -> [Branch] -- Updates use-later list. takes input of expPoss OUTPUT and use-later list.
ullUpdate Nothing [] = []
ullUpdate Nothing ull = backtrackUseLaterList ull
ullUpdate (Just expansions) uselaterList = expandUseLaterList expansions uselaterList

expPoss::Branch -> Graph -> Int -> [Node] -> Maybe [Branch] -- returns nothing if path can't be continued, otherwise returns a list of branch expansion possibilities (USE-LATER list).
expPoss [] _ _ _ = Nothing
expPoss _ [] _ _ = Nothing
expPoss branch graph depth exploredList
  | length (filter (/= 0) branch) >= depth = Nothing
  | findGraphNode (maybeToInt (findBranchEnd branch)) graph == Nothing = Nothing
  | (expandBranch branch graph exploredList) == [branch] = Nothing
  | otherwise = Just (expandBranch branch graph exploredList)


expandUseLaterList::[Branch] -> [Branch] -> [Branch]
expandUseLaterList (branchList) uselaterList = branchList ++ uselaterList

backtrackUseLaterList::[Branch] -> [Branch]
backtrackUseLaterList [] = []
backtrackUseLaterList (t:ts) = ts





-- BFS HELPER FUNCTIONS

looping::[Branch] -> Graph -> [Node] -> Bool -- returns True if branches are looping (cannot be expanded anymore)
looping [] _ _ = False
looping branchList graph nodeList
  | nub (branchList) == nub (expandBranches branchList graph nodeList) = True
  | otherwise = False

branchArrived::[Branch] -> Node -> Maybe Branch
branchArrived [] _ = Nothing
branchArrived (b:bs) destN
  | arrived b destN = Just b
  | otherwise = branchArrived bs destN

arrived::Branch -> Node -> Bool
arrived [] _ = False
arrived branch destination
  | checkArrival destination (maybeToInt (findBranchEnd branch)) = True
  | otherwise = False




-- TESTING VARIABLES:
b3::Branch
b3 = [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
g3::Graph
g3 = [0,1,0,0,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0]

b::Branch
b = [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
g::Graph
g = [0,1,1,0,0,0,0,1,0,0,0,0,0,0,0,0]

b2::Branch
b2 = [0,1,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0]
b1::Branch
b1 = [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
g1::Graph
g1 = [0,1,0,0,0,0,0,1,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0]

g2::Graph
g2 = [0,1,0,0,0,0,0,1,0,0,0,0,0,1,1,0,0,0,0,0,1,0,0,0,0]

--A* variables
g1A::Graph
g1A = [0,2,1,0,0,0,0,5,0,0,0,3,0,0,0,0]
b1A::Branch
b1A = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
b1A2::Branch
b1A2 = [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0]
b1A1::Branch
b1A1 = [0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
hrT1::[Int]
hrT1 = [5,4,4,0]

--ConnectFourVariables
gc0::Game
gc0 = [-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1]
gc1::Game
gc1 = [-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,1,1,1,1]

gc2::Game
gc2 = [-1,-1,-1,-1,0,1,-1,-1,0,0,1,-1,0,0,1,1]

gc3::Game
gc3 = [-1,-1,-1,-1,0,-1,0,1,1,-1,1,1,1,-1,0,0]

gcf::Game
gcf = [-1,-1,-1,-1,1,0,1,0,0,1,0,1,1,0,0,1]


-- NODE INFORMATION FUNCTIONS

getNode::Branch->Node --Retrieves first node in a given branch
getNode (b:bs) = b

totalNodes::Graph -> Int --
totalNodes [] = 0
totalNodes g = round (sqrt (fromIntegral (length g)))


-- PARSING GRAPH INTO TUPLE TRANSITIONS       tuple = (startNode,destNode)

sortGraph::Graph -> Node -> [[Node]]    -- Sorts graph into node rows (takes input of graph and number of nodes)
sortGraph [] _ = []
sortGraph g n = (take n g) : sortGraph (drop n g) n

findTrans::[[Node]] -> Node -> [[(Node,Node)]] --Sorts node rows into tuple transitions (representing row and column indexes), takes input of node rows and 0 (as a starting row index)
findTrans [] _  = []
findTrans (n:ns) i = ((join i (filterList n 0)) : findTrans ns (i+1))  --filter (not . null)

filterList::[Node] -> Int -> [Node] --Returns indexes of nodes which are not equal to 0 (int input is always 0 to represent current index and allow looping)
filterList [] _ = []
filterList (n:ns) index
  | n /= 0 = index : filterList ns (index+1)
  | otherwise = filterList ns (index+1)

join::Node -> [Node] -> [(Node,Node)]  --Tuple creating helper function for 'findTrans'
join i [] = []
join i (n:ns) = (i,n) : join i ns

findTransitions::Graph -> [[(Node,Node)]] --Returns a list of tuple transitions from the given graph
findTransitions [] = []
findTransitions g = (findTrans (sortGraph g (totalNodes g)) 0) --flatten


--MAYBE TYPE CONVERSIONS (self-explanatory)

maybeToBranch:: Maybe Branch -> Branch
maybeToBranch Nothing = []
maybeToBranch (Just b) = b

maybeToBranchList::Maybe [Branch] -> [Branch]
maybeToBranchList Nothing = []
maybeToBranchList (Just []) = []
maybeToBranchList (Just (b:bs)) = b : maybeToBranchList (Just bs)

maybeToIntList::Maybe [Int] -> [Int]
maybeToIntList Nothing = []
maybeToIntList (Just []) = []
maybeToIntList (Just (x:xs)) = x : maybeToIntList (Just xs)

maybeToInt::Maybe Int -> Int
maybeToInt Nothing = 0
maybeToInt (Just x) = x


--TUPLE TRANSITION PARSING FUNCTIONS

turnTupleIntoIndex::Graph -> (Node,Node) -> Int --Turns a given tuple transitions into its original graph index
--turnTupleIntoIndex [] _ = Nothing
turnTupleIntoIndex graph tuple = (((fst tuple)*(totalNodes graph)) + snd tuple)

turnTuplesIntoIndexes::Graph -> [(Node,Node)] -> [Int] --Turns a list of given tuple transitions into its original graph index
turnTuplesIntoIndexes graph (t:tupleList)
  | tupleList /= [] = (turnTupleIntoIndex graph t) : turnTuplesIntoIndexes graph tupleList
  | otherwise = [turnTupleIntoIndex graph t]

getTuple::[(Node,Node)] -> (Node,Node) --Returns first tuple in tuple list (tuples used to represent graph transitions ie (startNode,endNode) )
getTuple (t:tupleList) = t

flatten::[[(Node,Node)]] -> [(Node,Node)] --Flattens a nested list of tuples
flatten [] = []
flatten (n:ns) = n ++ flatten ns

--FILL BRANCH WITH VALS

fillBranch::Graph -> Branch
fillBranch [] = []
fillBranch (g:gs) = 0 : fillBranch gs

--EXPLORED NODE LIST HELPER FUNCTIONS

-- not explored = False
explored::Node-> [Node] ->Bool -- Boolean function that checks if a given node has been explored yet (is in the list of explored nodes)
explored _ [] = False
explored point (n:ns)
  | point == n = True
  | otherwise = explored point ns

explListUpdate::Node -> [Node] -> [Node] -- Update the list of explored nodes
explListUpdate point explList
  | explored point explList = explList
  | otherwise = [point] ++ explList

exploredNodes::Branch -> [Node] -- Return the list of explored nodes from a given branch
exploredNodes [] = []
exploredNodes branch = elemIndices 1 branch


--EXPLORED NODE LIST CALCULATION FUNCTIONS

totENodes::[Branch] -> [Node] -- Return the list total explored nodes from a list of branches (iterates over exploredNodes)
totENodes [] = []
totENodes (b:bs) = exploredNodes b ++ totENodes bs

totENodesMB::Maybe [Branch] -> [Node] -- Same functionality as totENodes for handling Maybe types
totENodesMB Nothing = []
totENodesMB (Just (branches)) = totENodes branches


--BRANCH EXPANSION FUNCTIONS

expandBranch::Branch -> Graph -> [Node] -> [Branch] -- Expands a given branch if the related graph and list of explored nodes allow it
expandBranch [] _ _ = []
expandBranch b [] _ = [b]
expandBranch branch graph exploredNodes
  | findBranchEnd branch == Nothing = [branch]
  | findGraphNode (fromMaybe 0 (findBranchEnd branch)) graph == Nothing = [branch]
  | otherwise = updateBranches graph branch (maybeToIntList (findGraphNode (maybeToInt (findBranchEnd branch)) graph)) exploredNodes

expandBranches::[Branch] -> Graph -> [Node] -> [Branch] -- Expands a list of branches by iterating over expandBranch
expandBranches [] _ _ = []
expandBranches _ [] _ = []
expandBranches (b:bs) graph exploredNodes = expandBranch b graph exploredNodes ++ expandBranches bs graph exploredNodes


--UPDATE BRANCH FUNCTIONS

updateBranches::Graph -> Branch -> [Int] -> [Node] -> [Branch]
updateBranches [] _ _ _ = []
updateBranches _ [] _ _ = []
updateBranches _ _ [] _ = []
updateBranches graph branch (x:xs) exploredList
  | explored x exploredList == True = updateBranches graph branch xs (explListUpdate x exploredList)
  | otherwise = updateBranch graph branch x : updateBranches graph branch xs exploredList

updateBranchIList::Graph->Branch->[Int]->Branch
updateBranchIList [] _ _ = []
updateBranchIList _ [] _ = []
updateBranchIList _ b [] = b
updateBranchIList graph branch (x:xs) = updateBranchIList graph (updateBranch graph branch x) xs

updateBranch::Graph -> Branch -> Int -> Branch
updateBranch [] _ _ = []
updateBranch _ [] _ = []
updateBranch graph branch index = (take index branch) ++ [(graph !! index)] ++ (drop (index+1) branch)


--FIND BRANCH END FUNCTIONS

findBranchEnd::Branch -> Maybe Int --Returns the leaf of a branch (represented as the destination Node row Index)
findBranchEnd [] = Nothing
findBranchEnd branch = findBEnd1 0 (findTransitions branch)

findBEnd1::Int -> [[(Node,Node)]] -> Maybe Int --findBranchEnd helper function 1 (1st row is default branch end as it will always exist)
findBEnd1 _ [] = Nothing
findBEnd1 rIndex transList
  | rIndex >= (length transList) = findBEnd1 0 transList
  | (transList !! rIndex) /= [] = findBEnd1 (findBEnd2 (transList !! rIndex)) transList
  | otherwise = Just(rIndex)

findBEnd2::[(Node,Node)] -> Int -- findBranchEnd helper function 2
findBEnd2 (tuple:tupleList) = (snd tuple)


--GRAPH SEARCH FUNCTIONS

findGraphNode::Int -> Graph -> Maybe [Int] --returns a list of indexes of node transitions for a given row in the graph
findGraphNode _ [] = Nothing
findGraphNode rowIndex graph
  | ((findTransitions graph) !! (rowIndex)) == [] = Nothing
  | otherwise = Just (turnTuplesIntoIndexes graph (flatten (drop rowIndex (take (rowIndex+1) (findTransitions graph)))))


findGRowNode::Int -> Int -> [(Node,Node)] -> Maybe Int --Returns the indexes of graph transitions
findGRowNode _ _ [] = Nothing
findGRowNode rIndex tNodes (g:gs) = Just((rIndex*tNodes) + snd g)
