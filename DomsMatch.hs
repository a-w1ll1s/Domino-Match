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

   The first type of DomsPlayer provided is simplePlayer. 
   It plays the first valid domino with no strategy. 
   
   The second type of DomsPlayer is smartPlayer. 
   It applies strategies for the first move, middle of the game and when the player
   or the opponent nears the target. 

   These DomsPlayers can play against each other in any combination in domsMatch. 

   scoreBoard, blocked, playDom and both DomsPlayers and their relevant functions 
   provided by Adam Willis (November 2023).
 -}

module DomsMatch where
    import System.Random
    import Data.List
    import Data.Ord (comparing)
    import Data.Maybe

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

    {- scoreBoard: Takes a Board and Boolean that describes whether the domino placed was the last in the hand.
       It returns the score of the move that created the current board. 
       
       If it is the initial state of the board before a domino has been placed then the score is trivially 0.
       Otherwise, the score is found - including +1 if it was the last domino in the hand.
    -}
    scoreBoard :: Board -> Bool -> Int
    scoreBoard InitState _ = 0 --no dominos on the board
    scoreBoard (State left right history ) final = findScore left right + (if final then 1 else 0)
      where
      findScore (l1,l2) (r1,r2)
        | divBy3 && divBy5 = total `div` 3 + total `div` 5
        | divBy3           = total `div` 3
        | divBy5           = total `div` 5
        | otherwise        = 0
          where
          divBy3 = total `mod` 3 == 0
          divBy5 = total `mod` 5 == 0 
          total --checks for double dominos and for the first played domino
            | (l1,l2) == (r1,r2) = l1 + l2
            | r1==r2 && l1==l2   = 2*(r2 + l1)
            | r1==r2             = 2*r2 + l1
            | l1==l2             = r2 + 2*l1
            | otherwise          = l1 + r2

    {- blocked - takes a Hand and a Board state and outputs True if the player is blocked.
       A player is blocked if there are no Dominos in their Hand that they can play on
       the Board. 
       A player can play a Domino if either end of it matches with the leftmost pips or
       the rightmost pips (the same works even if the left and right ends are doubles).
    -}
    blocked :: Hand -> Board -> Bool
    blocked _ InitState = False -- cannot be blocked at the start of the game
    blocked dominos (State (l1,l2) (r1,r2) history) = not (any matches dominos)
      where
      matches (a,b) = or [a==r2,a==l1,b==r2,b==l1] --at least one valid play

    {- playDom - takes a player, domino, state of the board and an end to play the domino on.
       
       It returns a new state of the board with an updated history if it a legal play, 
       otherwise it returns Nothing. 
    -}
    playDom :: Player -> Domino -> Board -> End -> Maybe Board
    playDom player dom InitState _ = Just (State dom dom [(dom,player,1)])
    playDom player (a, b) (State (l1, l2) (r1, r2) history) end
      | valid && end==R = Just (State (l1,l2) domino updateHistory)
      | valid && end==L = Just (State domino (r1,r2) updateHistory)
      | otherwise       = Nothing
        where
        valid = or [a==r2,a==l1,b==r2,b==l1]
        domino --orientation of the domino
          | a==r2 || b==l1 = (a,b)
          | a==l1 || b==r2 = (b,a)
        updateHistory
          | end==R = history ++ [(domino,player,length history +1)]
          | end==L = (domino,player,length history +1) : history

    {- simplePlayer takes a Hand, a Board, the Player and the scores and returns
       a domino and where to play it.
       
       It filters the players hand for valid dominos, and then chooses the first one.
       It does not include any strategy or reasoning.    
    -}
    simplePlayer :: Hand -> Board -> Player -> Scores -> (Domino, End)
    simplePlayer (dom:dominos) InitState _ _ = (dom,R)
    simplePlayer dominos state@(State (l1,l2) (r1,r2) history) player scores
      = head (mapMaybe (`canPlay` state) dominos)

    {- canPlay takes a domino and a board and returns the domino and the end to
       play it if it is a valid move. Otherwise, Nothing is returned. 
    -}
    canPlay :: Domino -> Board -> Maybe (Domino, End)
    canPlay dom InitState = Just (dom, R) 
    canPlay (a,b) (State (l1,l2) (r1,r2) history)
      | a == r2 || b == r2 = Just ((a,b),R)
      | a == l1 || b == l1 = Just ((a,b),L)
      | otherwise          = Nothing

    {- smartPlayer takes a Hand, a Board, the Player and the scores and returns
       a domino and where to play it.

       STRATEGIES:
       firstDrop (first move):
       - See if the hand contains (5,4) as this is the best opening move due to
         the opponent not being able to counter the points gained.
       - If not, play a domino from the biggest suit to keep all options open. 

       continueGame (neither players are close to the target):
       - Play the highest scoring domino from the biggest suit in the hand to gain
         points while avoiding knocking. 
       - If there are no valid dominos, play the highest scoring domino in the hand. 

       stitchGame (opponent is close to the target):
       - Play a domino from the opponents worst suit to increase the chances of the
         opponent knocking or stitching the game. 
       - If there are no valid dominos, play the highest scoring domino in the hand. 

       endGame (player is close to the target):
       - Play a domino that will score enough to reach the target and win the game. 
       - If there are no valid dominos, play a domino that will score enough to get
         within 2 of the target, as that is the easiest amount to score. 
       - If there are no valid dominos, play the highest scoring domino in the hand. 
    -}
    smartPlayer :: Hand -> Board -> Player -> Scores -> (Domino,End)
    smartPlayer dominos InitState _ _ = firstDrop
      where
      firstDrop
        | (5,4) `elem` dominos = ((5,4),R)
        | otherwise            = (head (biggestSuit dominos), R)
    smartPlayer dominos state player (score1,score2)
      | 61 - playerScore <= 10 = endGame
      | 61 - opponentScore <= 10 = stitchGame
      | otherwise = continueGame
        where
        (playerScore, opponentScore) 
          | player == P1 = (score1,score2)
          | otherwise    = (score2,score1)
        endGame
          | isJust (getDomino (61 - playerScore)) = fromJust (getDomino (61 - playerScore))
          | isJust (getDomino (59 - playerScore)) = fromJust (getDomino (59 - playerScore))
          | otherwise                             = fromJust (highestScorer dominos state) 
            where
            getDomino = doms2ScoreN dominos state
        stitchGame
          | isJust getDomino = fromJust getDomino
          | otherwise        = fromJust (highestScorer dominos state)
            where 
            getDomino = worstSuit dominos state player
        continueGame 
          | isJust getDomino = fromJust getDomino
          | otherwise        = fromJust (highestScorer dominos state)
            where
            getDomino = highestScorer (biggestSuit dominos) state

    {- biggestSuit takes a Hand of dominos and returns the subset of the Hand that
       contains dominos that are a part of the largest Suit in the Hand.
       
       It recurses through each suit and finds how many dominos in the hand are part of it. 
       The suit with the most dominos is chosen and returned as a subset of the hand. 
    -}
    biggestSuit :: Hand -> Hand
    biggestSuit dominos = inSuit largest
      where
      inSuit suit = filter (\(a,b) -> (a==suit) || (b==suit)) dominos
      largest     = head (elemIndices (maximum suitList) suitList)
      suitList    = map (length . inSuit) [0..6] --length = how many dominos in that suit

    {- doms2ScoreN takes a Hand of dominos, the current state of the board and a goal value. 
       If the hand does not contain a domino that can score the goal value, it returns Nothing.
       If there is a valid domino in the hand, it returns that domino and its valid end. 
       
       It takes the list of dominos, gets the list of scores and playable dominos and checks if 
       there is a valid domino. 
    -}
    doms2ScoreN :: Hand -> Board -> Int -> Maybe (Domino,End)  
    doms2ScoreN dominos state goal
      | dominos == [] = Nothing
      | otherwise     = dom2Play
        where
        dom2Play
          | goalIndices == [] = Nothing
          | otherwise         = Just (validHand' !! head goalIndices)
            where
            goalIndices = elemIndices goal scoreList'
            scoreList'  = scoreList dominos state
            validHand'  = validHand dominos state

    {- validHand takes a hand of dominos and the current state of the board and returns
       the list of playable dominos and their valid end.
    -}
    validHand :: Hand -> Board -> [(Domino,End)]
    validHand dominos state = mapMaybe (`canPlay` state) dominos 

    {- scoreList takes a hand of dominos, the current state of the board and returns 
       the list of scores that the playable dominos in the hand would produce. 
    -}
    scoreList :: Hand -> Board -> [Int]
    scoreList dominos state = map (`scoreBoard` False) validBoards
      where
      validBoards = mapMaybe (\(dom, end) -> playDom P1 dom state end) validHand' --player is unimportant
      validHand'  = validHand dominos state

    {- highestScorer takes a Hand of dominos and the current State of the Board and returns
       the highest scoring valid play in the form (Domino, End).
       
       It takes the list of dominos, gets the maximum valid score and returns
       the highest scoring domino and the valid end - if there are any valid dominos.
    -}
    highestScorer :: Hand -> Board -> Maybe (Domino,End)
    highestScorer dominos state 
      | dominos == [] = Nothing
      | otherwise     = doms2ScoreN dominos state highest
        where
        highest = maximum (scoreList dominos state)

    {- worstSuit takes a Hand of dominos, the current state of the board and the current player. 
       It returns a domino that is part of the opponents worst suit and the end to play it
       - if there is a valid domino. 
      
       It takes the history of the round, finds the dominos played by the opponent and the smallest 
       suit in that hand. Then the hand of the current player is filtered to contain only the dominos
       that are part of that suit. The first of this subset is returned if there are valid dominos.  
    -}
    worstSuit :: Hand -> Board -> Player -> Maybe (Domino,End)
    worstSuit dominos state@(State left right history) currentPlayer
      | validDominos == [] = Nothing
      | otherwise          = Just (head validDominos)
        where
        validDominos = mapMaybe (`canPlay` state) filteredHand
        filteredHand = filter (\(a,b) -> a==worstSuit || b==worstSuit) dominos
        worstSuit    = smallestSuitNum opponentHand
        opponentHand = mapMaybe getOpponentHand history  
          where
          getOpponentHand (domino,player,end)
            | currentPlayer==player = Nothing
            | otherwise             = Just domino

    {- smallestSuitNum takes a hand of dominos and returns the suit number that is the smallest. 
       It recurses through the suits and finds the size of each according to the hand. The smallest 
       suit is then chosen and returned.
    -}
    smallestSuitNum :: Hand -> Int 
    smallestSuitNum dominos = smallest
      where
      smallest    = head (elemIndices (minimum suitList) suitList)
      suitList    = map (length . inSuit) [0..6] --length = how many dominos in that suit
      inSuit suit = filter (\(a,b) -> (a==suit) || (b==suit)) dominos
