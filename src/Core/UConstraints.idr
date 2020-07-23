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

initSolverState : Int -> Set UConstraintFC -> SolverState
initSolverState maxULevel ucs =
  let inpConstraints = sort . SortedSet.toList $ ucs
      (initUnaryQueue, initQueue) = partition (\c => length (varsIn c.uconstraint) == 1) inpConstraints
      queue = Q (initUnaryQueue ++ initQueue) (fromList (map uconstraint (initUnaryQueue ++ initQueue)))
      domainVars = nub . concat $ map (varsIn . uconstraint) inpConstraints
      domainStore = fromList $ map (\v => (v, (MkDomain 0 maxULevel, empty))) domainVars
      consLHS = empty -- TODO
      consRHS = empty -- TODO
  in MkSolverState queue domainStore consLHS consRHS

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

solve : Int -> Ref SS SolverState -> Set UConstraintFC -> Core ()
-- TODO

-- When does UConstraints turn into Set UConstraintFC?
export
ucheck : Set UConstraintFC -> Core ()
ucheck ucs = do
  let maxULevel = 10
  ss <- newRef SS $ initSolverState maxULevel ucs
  solve maxULevel ss . filter (not . ignore) . dropUnused $ ucs
  where
    ignore : UConstraintFC -> Bool
    ignore (MkUConstraintFC (ULE a b) _) = a == b
    ignore _ = False
