{- 
   DomsMatch: code to play a dominoes match between two players.
   
   The top level function is domsMatch - it takes five arguments:
       games - the number of games to play
       target - the target score to reach
       player1, player2 - two DomsPlayer functions, representing the two players
       seed - an integer to seed the random number generator
   The function returns a pair showing how many games were won by each player.

   The functions of type DomsPlayer must take four arguments:
       The current Hand
       The current Board
       The Player (which will be one of P1 or P2)
       The current Scores
   The function returns a tuple containing the Domino to play and End to play it on.

   Stub with types provided by Emma Norling (October 2023).

   You should add your functions and any additional types that you require to your own copy of
   this file. Before you submit, make sure you update this header documentation to remove these
   instructions and replace them with authorship details and a brief summary of the file contents.

   Similarly, remember you will be assessed not *just* on correctness, but also code style,
   including (but not limited to) sensible naming, good functional decomposition, good layout,
   and good comments.
 -}

module DomsMatch where
    import System.Random
    import Data.List
    import Data.Ord (comparing)


    -- types used in this module
    type Domino = (Int, Int) -- a single domino
    {- Board data type: either an empty board (InitState) or the current state as represented by
        * the left-most domino (such that in the tuple (x,y), x represents the left-most pips)
        * the right-most domino (such that in the tuple (x,y), y represents the right-most pips)
        * the history of moves in the round so far
     -}
    data Board = InitState | State Domino Domino History deriving (Eq, Show)
    {- History should contain the *full* list of dominos played so far, from leftmost to
       rightmost, together with which player played that move and when they played it
     -}
    type History = [(Domino, Player, MoveNum)]
    data Player = P1 | P2 deriving (Eq, Show)
    data End = L | R deriving (Eq, Show)
    type Scores = (Int, Int) -- P1’s score, P2’s score
    type MoveNum = Int
    type Hand = [Domino]
    {- DomsPlayer is a function that given a Hand, Board, Player and Scores will decide
       which domino to play where. The Player information can be used to "remember" which
       moves in the History of the Board were played by self and which by opponent
     -}
    type DomsPlayer = Hand -> Board -> Player -> Scores -> (Domino, End)

    {- domSet: a full set of dominoes, unshuffled -}
    domSet = [ (l,r) | l <- [0..6], r <- [0..l] ]

    {- shuffleDoms: returns a shuffled set of dominoes, given a number generator
       It works by generating a random list of numbers, zipping this list together
       with the ordered set of dominos, sorting the resulting pairs based on the random
       numbers that were generated, then outputting the dominos from the resulting list.
     -}
    shuffleDoms :: StdGen -> [Domino]
    shuffleDoms gen = [ d | (r,d) <- sort (zip (randoms gen :: [Int]) domSet)]

    {- domsMatch: play a match of n games between two players,
        given a seed for the random number generator
       input: number of games to play, number of dominos in hand at start of each game,
              target score for each game, functions to determine the next move for each
              of the players, seed for random number generator
       output: a pair of integers, indicating the number of games won by each player
     -}
    domsMatch :: Int -> Int -> Int -> DomsPlayer -> DomsPlayer -> Int -> (Int, Int)
    domsMatch games handSize target p1 p2 seed
        = domsGames games p1 p2 (mkStdGen seed) (0, 0)
          where
          domsGames 0 _  _  _   wins               = wins
          domsGames n p1 p2 gen (p1_wins, p2_wins)
            = domsGames (n-1) p1 p2 gen2 updatedScore
              where
              updatedScore
                | playGame handSize target p1 p2 (if odd n then P1 else P2) gen1 == P1 = (p1_wins+1,p2_wins)
                | otherwise                                            = (p1_wins, p2_wins+1)
              (gen1, gen2) = split gen
              {- Note: the line above is how you split a single generator to get two generators.
                 Each generator will produce a different set of pseudo-random numbers, but a given
                 seed will always produce the same sets of random numbers.
               -}

    {- playGame: play a single game (where winner is determined by a player reaching
          target exactly) between two players
       input: functions to determine the next move for each of the players, player to have
              first go, random number generator 
       output: the winning player
     -}
    playGame :: Int -> Int -> DomsPlayer -> DomsPlayer -> Player -> StdGen -> Player
    playGame handSize target p1 p2 firstPlayer gen
        = playGame' p1 p2 firstPlayer gen (0, 0)
          where
          playGame' p1 p2 firstPlayer gen (s1, s2)
            | s1 == target = P1
            | s2 == target = P2
            | otherwise   
                = let
                      newScores = playDomsRound handSize target p1 p2 firstPlayer currentG (s1, s2)
                      (currentG, nextG) = split gen
                  in
                  playGame' p1 p2 (if firstPlayer == P1 then P2 else P1) nextG newScores

    {- playDomsRound: given the starting hand size, two dominos players, the player to go first,
        the score at the start of the round, and the random number generator, returns the score at
        the end of the round.
        To complete a round, turns are played until either one player reaches the target or both
        players are blocked.
     -}
    playDomsRound :: Int -> Int -> DomsPlayer -> DomsPlayer -> Player -> StdGen -> (Int, Int) -> (Int, Int)
    playDomsRound handSize target p1 p2 first gen scores
        = playDomsRound' p1 p2 first (hand1, hand2, InitState, scores)
          where
          -- shuffle the dominoes and generate the initial hands
          shuffled = shuffleDoms gen
          hand1 = take handSize shuffled
          hand2 = take handSize (drop handSize shuffled)
          {- playDomsRound' recursively alternates between each player, keeping track of the game state
             (each player's hand, the board, the scores) until both players are blocked -}
          playDomsRound' p1 p2 turn gameState@(hand1, hand2, board, (score1,score2))
            | (score1 == target) || (score2 == target) || (p1_blocked && p2_blocked) = (score1,score2)
            | turn == P1 && p1_blocked = playDomsRound' p1 p2 P2 gameState
            | turn == P2 && p2_blocked = playDomsRound' p1 p2 P1 gameState
            | turn == P1               = playDomsRound' p1 p2 P2 newGameState
            | otherwise                = playDomsRound' p1 p2 P1 newGameState
              where
              p1_blocked = blocked hand1 board
              p2_blocked = blocked hand2 board
              (domino, end)          -- get next move from appropriate player
                  | turn == P1 = p1 hand1 board turn (score1, score2)
                  | turn == P2 = p2 hand2 board turn (score1, score2)
                                     -- attempt to play this move
              maybeBoard             -- try to play domino at end as returned by the player
                  | turn == P1 && not (elem domino hand1) = Nothing -- can't play a domino you don't have!
                  | turn == P2 && not (elem domino hand2) = Nothing
                  | otherwise = playDom turn domino board end
              newGameState           -- if successful update board state (exit with error otherwise)
                 | maybeBoard == Nothing = error ("Player " ++ show turn ++ " attempted to play an invalid move.")
                 | otherwise             = (newHand1, newHand2, newBoard,
                                              (limitScore score1 newScore1, limitScore score2 newScore2))
              (newHand1, newHand2)   -- remove the domino that was just played
                 | turn == P1 = (hand1\\[domino], hand2)
                 | turn == P2 = (hand1, hand2\\[domino])
              score = scoreBoard newBoard (newHand1 == [] || newHand2 == [])
              (newScore1, newScore2) -- work out updated scores
                 | turn == P1 = (score1+score,score2)
                 | otherwise  = (score1,score2+score)
              limitScore old new     -- make sure new score doesn't exceed target
                 | new > target = old
                 | otherwise    = new
              Just newBoard = maybeBoard -- extract the new board from the Maybe type

    -- returns the points scored based on the two ends of the passed in board
    scoreBoard :: Board -> Bool -> Int
    scoreBoard InitState _ = 0 -- no points if nothing is on the board
    scoreBoard (State (ll,lr) (rl,rr) h) lastDomino
      -- calculates score based off game rules
      | edgeSum `mod` 3 == 0 && edgeSum `mod` 5 == 0 = edgeSum `div` 3 + edgeSum `div` 5 + lastDomBonus
      | edgeSum `mod` 3 == 0                         = edgeSum `div` 3 + lastDomBonus
      | edgeSum `mod` 5 == 0                         = edgeSum `div` 5 + lastDomBonus
      | otherwise                                    = 0 + lastDomBonus
      where
        lastDomBonus = if lastDomino then 1 else 0 
        edgeSum
          | ll == lr && rl == rr = ll + lr + rl + rr -- both end dominos are doubles
          | ll == lr             = ll + lr + rr -- furthest left is a double
          | rl == rr             = ll + rl + rr -- furthest right is a double
          | otherwise            = ll + rr -- neither end dominos are doubles

    -- included in addition to blocked, since passing in an End made higher up functions easier
    canPlay :: Domino -> Board -> End -> Bool
    canPlay _ InitState _ = True
    canPlay (l,r) (State (ll,lr) (rl,rr) h) L
      | l == ll || r == ll = True
      | otherwise          = False
    canPlay (l,r) (State (ll,lr) (rl,rr) h) R
      | l == rr || r == rr = True
      | otherwise          = False

    blocked :: Hand -> Board -> Bool
    blocked [] _ = True
    blocked _ InitState = False
    blocked ((l,r):xs) board@(State (ll,lr) (rl,rr) h)
      | l == ll || r == ll || l == rr || r == rr = False
      | otherwise                                = blocked xs board
       
    -- adds domino to the history, returns the updated history
    updateHistory :: Player -> Domino -> History -> History
    updateHistory player dom [] = [(dom, player, 1)]
    updateHistory player dom h = h ++ [(dom, player, 1 + length h)]

    -- plays domino on the board and updates the history, returns Nothing if the domino cannot be played
    playDom :: Player -> Domino -> Board -> End -> Maybe Board
    playDom player (a,b) InitState _ = Just (State (a,b) (a,b) (updateHistory player (a,b) []) )
    playDom player (l,r) b@(State (ll,lr) rightDom h) L
      | canPlay dom b L = Just (State dom rightDom (updateHistory player (l,r) h))
      | otherwise       = Nothing
      where
        dom = if r == ll then (l,r) else (r,l) -- flips dom before playing if needed
    playDom player (l,r) b@(State leftDom (rl,rr) h) R
      | canPlay dom b R = Just (State leftDom dom (updateHistory player (l,r) h))
      | otherwise       = Nothing
      where
        dom = if l == rr then (l,r)  else (r,l)

    -- returns true if the domino has already been played on the board
    played :: Domino -> History -> Bool
    played _ [] = False
    played dom ((histDom, p, n):xs)
      | dom == histDom = True 
      | otherwise      = played dom xs

    -- returns the pip totals needed to obtain n points
    getPipTotal :: Int -> [Int]
    getPipTotal n
      | n == 1    = [3,5]
      | n == 2    = [6,10]
      | n == 3    = [9]
      | n == 4    = [12,20]
      | n == 6    = [18]
      | n == 8    = [15]
      | otherwise = []

    -- doms2scoreN: given a Board and an Int n, return all the Dominos not already played which could be
    -- played to give a fives-and-threes score of n and the End at which to play each one
    doms2scoreN :: Board -> Int -> Maybe [(Domino, End)]
    doms2scoreN InitState n
      | length possPlays == 0 = Nothing
      | otherwise             = Just possPlays
      where 
        possPlays    = [((l,r),L) | l <- [0..6], r <- [0..6], x <- (getPipTotal n), x == l+r]   
    doms2scoreN (State (ll,lr) (rl,rr) h) n
      | length possPlays == 0 = Nothing
      | otherwise             = Just possPlays
      where
        pipsToScoreN  = getPipTotal n -- number of pips needed to get 'n' points
        rDomScore     = if rl == rr then rl + rr else rr -- score of the domino further right on the board
        lDomScore     = if ll == lr then ll + lr else ll
        lPipList      = filter (\n -> n/=ll) [0..6] -- filters out ll as left pip since it would score double
        rPipList      = filter (\n -> n/=rr) [0..6] 
        lDouble       = [((ll,ll),L) | n <- pipsToScoreN, n == (ll*2 + rDomScore) && played (ll,ll) h == False]
        rDouble       = [((rr,rr),R) | n <- pipsToScoreN, n == (rr*2 + lDomScore) && played (rr,rr) h == False]
        lPlayablePips = [l | l <- lPipList, n <- pipsToScoreN, n == l+rDomScore]
        rPlayablePips = [r | r <- rPipList, n <- pipsToScoreN, n == r+lDomScore]
        possPlays     = [((x,ll),L) | x <- lPlayablePips, played (x,ll) h == False] ++
                        [((ll,x),L) | x <- lPlayablePips, played (ll,x) h == False] ++
                        [((rr,x),R) | x <- rPlayablePips, played (rr,x) h == False] ++
                        [((x,rr),R) | x <- rPlayablePips, played (x,rr) h == False] ++
                        lDouble ++ rDouble -- will be [] if they cannot be played to score n

    -- function is only called if there is at least one playable domino in the hand
    simplePlayer :: DomsPlayer
    simplePlayer hand InitState _ _ = (head hand, L)
    simplePlayer (x:xs) board player scores 
      | canPlay x board L = (x,L)
      | canPlay x board R = (x,R)
      | otherwise         = simplePlayer xs board player scores

    smartPlayer :: DomsPlayer
    smartPlayer hand InitState player scores
      | score > 52        = endGame score hand InitState -- tactics for winning the game
      | (5,4) `elem` hand = ((5,4),L)
      | (4,5) `elem` hand = ((4,5),L)
      | otherwise         = playHighestScoringDom hand InitState
      where
        score = if player == P1 then fst scores else snd scores
    smartPlayer hand board player scores
      | score > 52                       = endGame score playableDoms board
      | count > 4 && possPlay /= Nothing = play -- play a dom with a pip we have lots of
      | otherwise                        = playHighestScoringDom playableDoms board 
      where
        score              = if player == P1 then fst scores else snd scores
        playableDoms       = [n | n <- hand, canPlay n board L || canPlay n board R]
        maxPipCount [x]    = x
        maxPipCount (x:xs) = (\ i@(a,b) j@(c,d) -> if d>4 && d>b then j else i) x (maxPipCount xs)
        (pip, count)       = maxPipCount(abundantPips(unzip hand))
        possPlay           = playDomWithPipN playableDoms board pip -- playable dom with pip we have lots of
        Just (play)        = possPlay

    -- returns a list of tuples of (pip, number of occurances of pip in the hand)
    abundantPips :: ([Int],[Int]) -> [(Int,Int)]
    abundantPips (x,y) = pipsOccurances
      where
        listOfPips      = x ++ y
        totalOfPip x xs = (length.filter (== x)) xs
        pipsOccurances  = [(n, totalOfPip n listOfPips) | n <- [0..6]]

    -- returns Just a play that is possible and has the desired pip, or Nothing
    playDomWithPipN :: [Domino] -> Board -> Int -> Maybe (Domino, End)
    playDomWithPipN [] _ _ = error "There should always be a playable domino in this function call"
    playDomWithPipN playableDoms b pip
      | doms == [] = Nothing
      | otherwise  = Just ((head doms),end)
      where
        doms = [n | n <- playableDoms, pip == fst n || pip == snd n]
        end  = if canPlay (head doms) b L then L else R -- this works since doms passed in can all be played

    -- function always called with at least 1 playable domino
    playHighestScoringDom :: [Domino] -> Board -> (Domino, End)
    maxScorer [x]    = x
    maxScorer (x:xs) = (\i@(d,e,m) j@(a,b,n) -> if n>m then j else i) x (maxScorer xs)
    playHighestScoringDom [] board = error "There should always be a playable domino in this function call"
    playHighestScoringDom playableDoms board = (dom,end)
      where
        domsEndsScores    = calcScore playableDoms board -- [(Domino, End, Int)]
        (dom, end, score) = maxScorer domsEndsScores

    -- attaches a score to each play
    calcScore :: [Domino] -> Board -> [(Domino, End, Int)]
    calcScore [] _ = []
    calcScore (x:xs) InitState =  [(x, L, scoreBoard (State x (0,0) []) False)] ++ calcScore xs InitState
    calcScore ((l,r):xs) b@(State (ll,lr) (rl,rr) h) = list ++ calcScore xs b
      where 
        list       = leftSide ++ rightSide
        leftSide   = if canPlay (l,r) b L then lCheckFlip else [] -- score depends on if the domino is flipped
        rightSide  = if canPlay (l,r) b R then rCheckFlip else []
        lCheckFlip = if r == ll then [((l,r), L, scoreBoard (State (l,r) (rl,rr) []) False)] 
                                else [((l,r), L, scoreBoard (State (r,l) (rl,rr) []) False)]
        rCheckFlip = if l == rr then [((l,r), R, scoreBoard (State (ll,lr) (l,r) []) False)] 
                                else [((l,r), R, scoreBoard (State (ll,lr) (r,l) []) False)]
    
    -- Attempts to find a play that will win the game, then one that gets 2 points away
    endGame :: Int -> [Domino] -> Board -> (Domino, End)
    endGame _ [] board = error "There should always be a playable domino in this function call"
    endGame _ [x] board 
      | canPlay x board L = (x,L)
      | otherwise         = (x,R)
    endGame score playableDoms board
      | length winningPlays > 0 = head winningPlays -- play domino that wins
      | twoAway /= Nothing      = twoPtsOff -- play domino that gets 2 points off win
      | otherwise               = playHighestScoringDom playableDoms board
      where
        -- mark scheme says it should work for different targets (not just 61) but domsPlayer isn't given a 
        -- target as input, so I asked Emma Norling and she said we can assume 61 is always the target score
        doms2win         = doms2scoreN board (61-score) -- list of (dom,end) that can win
        Just (winners)   = doms2win
        domsEnds         = if doms2win == Nothing then [] else winners
        winningPlays     = [(dom,end) | dom <- playableDoms, (winDom,end) <- domsEnds, dom == winDom]
        twoAway          = get2away score playableDoms board
        Just (twoPtsOff) = twoAway

    -- returns Just a play that will get 2 points off winning, or Nothing
    get2away :: Int -> [Domino] -> Board -> Maybe (Domino, End)
    get2away _ [] board = error "There should always be a playable domino in this function call"
    get2away score playableDoms board
      | length possPlays == 0 = Nothing
      | otherwise             = Just (head possPlays)
      where
        -- hard coded 59 because I was told we can assume target is always 61, hence 59 is 2 off
        doms2off     = doms2scoreN board (59-score)
        Just (plays) = doms2off
        domsEnds     = if doms2off == Nothing then [] else plays
        possPlays    = [(dom,end) | dom <- playableDoms, (twoAwayDom,end) <- domsEnds, dom == twoAwayDom]

