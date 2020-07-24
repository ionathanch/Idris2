module Core.UConstraints

import Core.Core
import Core.TT

import Data.List
import Data.SortedSet
import Data.SortedMap

%default total

-- Is it possible to use a type synonym in a dot pattern?
-- e.g. Set.toList rather than SortedSet.toList.
Set : Type -> Type
Map : Type -> Type -> Type
Set = SortedSet
Map = SortedMap

data Var = MkVar String Int
data Domain = MkDomain Int Int
data Queue = Q (List UConstraintFC) (Set UConstraint)

Eq Var where
  (MkVar s i) == (MkVar t j) = s == t && i == j

Ord Var where
  compare (MkVar s i) (MkVar t j) =
    case compare s t of
      GT => GT
      LT => LT
      EQ => compare i j

record SolverState where
  constructor MkSolverState
  queue : Queue
  domainStore : Map Var (Domain, Set UConstraintFC)
  consLHS : Map Var (Set UConstraintFC)
  consRHS : Map Var (Set UConstraintFC)

data SS : Type where


-- This function is why all subsequent functions
-- have to be marked as `partial`.
partial
find : k -> Map k v -> v
find k m =
  let Just v = lookup k m
  in v

asPair : Domain -> (Int, Int)
asPair (MkDomain l u) = (l, u)

isWipedOut : Domain -> Bool
isWipedOut (MkDomain l u) = l > u

uvarToVar : UExp -> Maybe Var
uvarToVar (UVar ns v) = Just $ MkVar ns v
uvarToVar _ = Nothing

-- For some reason the list comprehension version isn't convering:
-- [ MkVar ns v | UVar ns v <- [a,b] ]
varsIn : UConstraint -> List Var
varsIn (ULT x y) = mapMaybe uvarToVar [x, y]
varsIn (ULE x y) = mapMaybe uvarToVar [x, y]


dropUnused : Set UConstraintFC -> Set UConstraintFC
dropUnused xs =
  let cs = SortedSet.toList xs
      onLHS = countLHS cs empty
  in addIfUsed onLHS cs empty
  where
    getLHS : UConstraint -> UExp
    getLHS (ULT x _) = x
    getLHS (ULE x _) = x

    getRHS : UConstraint -> UExp
    getRHS (ULT _ y) = y
    getRHS (ULE _ y) = y

    countLHS : List UConstraintFC -> Map UExp Int -> Map UExp Int
    countLHS [] ms = ms
    countLHS (c :: cs) ms =
      let lhvar = getLHS c.uconstraint
          num = case lookup lhvar ms of
                  Nothing => 1
                  Just v => v + 2 in
          countLHS cs (insert lhvar num ms)
    
    addIfUsed : Map UExp Int -> List UConstraintFC -> Set UConstraintFC -> Set UConstraintFC
    addIfUsed lhs [] cs' = cs'
    addIfUsed lhs (c :: cs) cs' =
      let rhvar = getRHS c.uconstraint in
      case lookup rhvar lhs of
        Nothing => addIfUsed lhs cs cs'
        Just _ => addIfUsed lhs cs (insert c cs')

initSolverState : Int -> Set UConstraintFC -> SolverState
initSolverState maxULevel ucs =
  let inpConstraints = SortedSet.toList $ ucs
      (initUnaryQueue, initQueue) = partition (\c => length (varsIn c.uconstraint) == 1) inpConstraints
      queue = Q (initUnaryQueue ++ initQueue) (fromList (map uconstraint (initUnaryQueue ++ initQueue)))
      domainStore = fromList
        [ (v, (MkDomain 0 maxULevel, empty))
        | v <- ordNub [ v
                      | MkUConstraintFC c _ <- inpConstraints
                      , v <- varsIn c
                      ]
        ]
      consLHS = fromListWith SortedSet.union
        [ (v, singleton (MkUConstraintFC c fc))
        | (MkUConstraintFC c fc) <- inpConstraints
        , let vars = varsIn c
        , length vars > 1
        , v <- vars
        , lhs c == Just v
        ]
      consRHS = fromListWith SortedSet.union
        [ (v, singleton (MkUConstraintFC c fc))
        | (MkUConstraintFC c fc) <- inpConstraints
        , let vars = varsIn c
        , length vars > 1
        , v <- vars
        , lhs c == Just v
        ]
  in MkSolverState queue domainStore consLHS consRHS
  where
    ordNub : Ord k => List k -> List k
    ordNub = SortedSet.toList . SortedSet.fromList

    lhs : UConstraint -> Maybe Var
    lhs (ULT (UVar ns x) _) = Just (MkVar ns x)
    lhs (ULE (UVar ns x) _) = Just (MkVar ns x)
    lhs _ = Nothing

    rhs : UConstraint -> Maybe Var
    rhs (ULT _ (UVar ns x)) = Just (MkVar ns x)
    rhs (ULE _ (UVar ns x)) = Just (MkVar ns x)
    rhs _ = Nothing

partial
updateUpperBoundOf : {auto ss : Ref SS SolverState} -> UConstraintFC -> UExp -> Int -> Core ()
updateUpperBoundOf _ (UVal _) _ = pure ()
updateUpperBoundOf suspect (UVar ns var) upper = do
  doms <- domainStore <$> get SS
  let (oldDom@(MkDomain lower _), suspects) = find (MkVar ns var) doms
  let newDom = MkDomain lower upper
  when (isWipedOut newDom) $ throw $
    UniverseError
      (ufc suspect) (UVar ns var)
      (asPair oldDom) (asPair newDom)
      (suspect :: SortedSet.toList suspects)
  let domainStore = insert (MkVar ns var) (newDom, insert suspect suspects) doms
  modify SS $ \ss : SolverState => record { domainStore = domainStore } ss
  addToQueueRHS (uconstraint suspect) (MkVar ns var)
  where
    addToQueueRHS : UConstraint -> Var -> Core ()
    addToQueueRHS thisCons var = do
      crhs <- consRHS <$> get SS
      case lookup var crhs of
        Nothing => pure ()
        Just cs => do
          Q list set <- queue <$> get SS
          let set' = insert thisCons set
          let newCons = [ c | c <- SortedSet.toList cs, not $ contains c.uconstraint set' ]
          if isNil newCons
            then pure ()
            else do
              let queue = Q (list ++ newCons) (foldr insert set (map uconstraint newCons))
              modify SS $ \ss : SolverState => record { queue = queue } ss

partial
updateLowerBoundOf : {auto ss : Ref SS SolverState} -> UConstraintFC -> UExp -> Int -> Core ()
updateLowerBoundOf _ (UVal _) _ = pure ()
updateLowerBoundOf suspect (UVar ns var) lower = do
  doms <- domainStore <$> get SS
  let (oldDom@(MkDomain _ upper), suspects) = find (MkVar ns var) doms
  let newDom = MkDomain lower upper
  when (isWipedOut newDom) $ throw $
    UniverseError
      (ufc suspect) (UVar ns var)
      (asPair oldDom) (asPair newDom)
      (suspect :: SortedSet.toList suspects)
  let domainStore = insert (MkVar ns var) (newDom, insert suspect suspects) doms
  modify SS $ \ss : SolverState => record { domainStore = domainStore } ss
  addToQueueLHS (uconstraint suspect) (MkVar ns var)
  where
    addToQueueLHS : UConstraint -> Var -> Core ()
    addToQueueLHS thisCons var = do
      clhs <- consLHS <$> get SS
      case lookup var clhs of
        Nothing => pure ()
        Just cs => do
          Q list set <- queue <$> get SS
          let set' = insert thisCons set
          let newCons = [ c | c <- SortedSet.toList cs, not $ contains c.uconstraint set' ]
          if isNil newCons
            then pure ()
            else do
              let queue = Q (list ++ newCons) (foldr insert set (map uconstraint newCons))
              modify SS $ \ss : SolverState => record { queue = queue } ss

-- If not for `find`, `propagate` would actually be covering,
-- but not inferrably total.
partial
propagate : {auto ss : Ref SS SolverState} -> Core ()
propagate = do
  mcons <- nextConstraint
  case mcons of
    Nothing => pure ()
    Just (MkUConstraintFC cons fc) => do
      case cons of
        ULE a b => do
          MkDomain lowerA upperA <- domainOf a
          MkDomain lowerB upperB <- domainOf b
          when (upperB < upperA) $ updateUpperBoundOf (MkUConstraintFC cons fc) a upperB
          when (lowerA > lowerB) $ updateLowerBoundOf (MkUConstraintFC cons fc) b lowerA
        ULT a b => do
          MkDomain lowerA upperA <- domainOf a
          MkDomain lowerB upperB <- domainOf b
          let upperB_pred = upperB - 1
          let lowerA_succ = lowerA + 1
          when (upperB_pred < upperA) $ updateUpperBoundOf (MkUConstraintFC cons fc) a upperB_pred
          when (lowerA_succ > lowerB) $ updateLowerBoundOf (MkUConstraintFC cons fc) b lowerA_succ
      propagate
  where
    partial
    domainOf : UExp -> Core Domain
    domainOf (UVar ns var) = fst . (find $ MkVar ns var) . domainStore <$> get SS
    domainOf (UVal val) = pure (MkDomain val val)

    nextConstraint : Core (Maybe UConstraintFC)
    nextConstraint = do
      Q list set <- queue <$> get SS
      case list of
        [] => pure Nothing
        (q :: qs) => do
          modify SS $ \ss : SolverState => record { queue = Q qs (delete q.uconstraint set) } ss
          pure (Just q)

partial
solve : Int -> Set UConstraintFC -> Core (Map Var Int)
solve maxULevel ucs = do
  ss <- newRef SS $ initSolverState maxULevel ucs
  propagate
  extractSolution
  where
    extractSolution : {auto ss : Ref SS SolverState} -> Core (Map Var Int)
    extractSolution = map (\((MkDomain x _), _) => x) . domainStore <$> get SS

export partial
ucheck : Set UConstraintFC -> Core ()
ucheck ucs = do -- Why is the maximum universe level set to 10?
  solve 10 . filter (not . ignore) . dropUnused $ ucs
  pure ()
  where
    ignore : UConstraintFC -> Bool
    ignore (MkUConstraintFC (ULE a b) _) = a == b
    ignore _ = False
