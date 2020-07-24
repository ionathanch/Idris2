module Core.UConstraints

import Core.Core
import Core.TT

import Data.List
import Data.SortedSet
import Data.SortedMap

%default total

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

varsIn : UConstraint -> List Var -- TODO
-- varsIn (ULT x y) = [ MkVar ns v | UVar ns v <- [x, y] ]
-- varsIn (ULE x y) = [ MkVar ns v | UVar ns v <- [x, y] ]

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

solve : Int -> Set UConstraintFC -> Core ()
solve maxULevel ucs = do
  ss <- newRef SS $ initSolverState maxULevel ucs
  pure () -- TODO

-- When does UConstraints turn into Set UConstraintFC?
export
ucheck : Set UConstraintFC -> Core ()
ucheck ucs = do -- Why is the maximum universe level set to 10?
  solve 10 . filter (not . ignore) . dropUnused $ ucs
  where
    ignore : UConstraintFC -> Bool
    ignore (MkUConstraintFC (ULE a b) _) = a == b
    ignore _ = False
