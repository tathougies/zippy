module Database.Zippy.Containers.Treap where

import Database.Zippy.Types

import Prelude hiding (mapM)

import Control.Monad hiding (mapM)
import Control.Applicative

import Data.Word
import Data.Int
import Data.Maybe
import Data.Traversable (mapM)
import qualified Data.Vector as V

data TreapFoundResult = Found | NotFound
                        deriving Show

treapLeafTag, treapBranchTag :: Word16
treapLeafTag = 0
treapBranchTag = 1

treapBranchKey, treapBranchValue, treapBranchLeft, treapBranchRight :: Int
treapBranchKey = 0
treapBranchValue = 1
treapBranchPrio = 2
treapBranchLeft = 3
treapBranchRight = 4

treapLeaf :: InMemoryD
treapLeaf = InMemoryD (CompositeD treapLeafTag V.empty)
treapLeafS :: SZippyD
treapLeafS = eraseInMemoryD treapLeaf
treapBranch :: Int64 -> InMemoryD -> InMemoryD -> SZippyD -> SZippyD -> InMemoryD
treapBranch prio !key !val !left !right =
    InMemoryD (CompositeD treapBranchTag (V.fromList [eraseInMemoryD key, eraseInMemoryD val, SZippyD (IntegerD prio), left, right]))

-- Two possibilities... We're at a branch, or we're at a leaf
treapFind :: Int -> Tx Ordering -> Tx (Int, TreapFoundResult)
treapFind !lvl keyCmp =
    do res <- cur
       case res of
         CurHasTag tag
             | tag == treapLeafTag -> return (lvl, NotFound)
             | tag == treapBranchTag ->
                 do move (Down treapBranchKey)
                    nextDir <- keyCmp
                    move Up
                    case nextDir of
                      LT -> do move (Down treapBranchLeft)
                               treapFind (lvl + 1) keyCmp
                      GT -> do move (Down treapBranchRight)
                               treapFind (lvl + 1) keyCmp
                      EQ -> return (lvl, Found)
         CurIsAtom _ -> fail "treapFind: Atom found where composite expected"

treapCheckLeftOrRight :: Tx (Either () ())
treapCheckLeftOrRight =
    do argHole <- parentArgHole
       if argHole == Just treapBranchLeft then return (Left ()) else return (Right ())

replaceArgs :: InMemoryD -> [(Int, SZippyD)] -> InMemoryD
replaceArgs (InMemoryD (CompositeD tag args)) replace =
    InMemoryD (CompositeD tag (args V.// replace))
replaceArgs x _ = x

-- curCopy :: [(Int, SZippyD)] -> Tx InMemoryD
-- curCopy argsToReplace = go
--     where go = do (ty, _) <- curTy
--                   case ty of
--                     SimpleT _ -> do CurIsAtom (InMemoryAtomD simple) <- cur
--                                     return (InMemoryD simple)
--                     AlgebraicT (ZippyAlgebraicT _ cons) ->
--                         do CurHasTag tag <- cur
--                            let ZippyTyCon _ args = cons V.! fromIntegral tag
--                            args' <- mapM goArg (V.indexed args)
--                            return (InMemoryD (CompositeD tag (args' V.// argsToReplace)))

--           goArg (i, _)
--               | any ((== i) . fst) argsToReplace = return undefined
--           goArg (i, Left _) = fromJust <$> childRef i
--           goArg (i, Right simpleTy)
--               | simpleTy == IntegerT || simpleTy == FloatingT =
--                   do move (Down i)
--                      CurIsAtom (InMemoryAtomD simple) <- cur
--                      move Up
--                      return (SZippyD simple)
--               -- Text and Binary might get really big, so just copy references...
--               | otherwise = fromJust <$> childRef i

curCopy left right = do CurIsAtom (InMemoryAtomD key) <- move (Down treapBranchKey) *> cur <* move Up
                        valueRef <- fromJust <$> childRef treapBranchValue
                        CurIsAtom (InMemoryAtomD prio) <- move (Down treapBranchPrio) *> cur <* move Up
                        l <- case left of
                               Nothing -> fromJust <$> childRef treapBranchLeft
                               Just l -> return l
                        r <- case right of
                               Nothing -> fromJust <$> childRef treapBranchRight
                               Just r -> return r
                        return (InMemoryD (CompositeD treapBranchTag (V.fromList [SZippyD key, valueRef, SZippyD prio, l, r])))

treapChildRef which =
    do CurHasTag i <- cur
       if i == treapBranchTag then fromJust <$> childRef which else return treapLeafS

rotateMeRight, rotateMeLeft :: Tx ()
rotateMeRight = do
  move (Down treapBranchLeft)
  leftRightRef <- treapChildRef treapBranchRight

  leftCopy <- curCopy Nothing Nothing
  move Up
  parentCopy <- curCopy (Just leftRightRef) Nothing
  let leftCopy' = replaceArgs leftCopy [(treapBranchRight, eraseInMemoryD parentCopy)]
  move (Replace leftCopy')
  return ()

rotateMeLeft = do
  move (Down treapBranchRight)
  rightLeftRef <- treapChildRef treapBranchLeft

  rightCopy <- curCopy Nothing Nothing
  move Up
  parentCopy <- curCopy Nothing (Just rightLeftRef)
  let rightCopy' = replaceArgs rightCopy [(treapBranchLeft, eraseInMemoryD parentCopy)]
  move (Replace rightCopy')
  return ()

checkTreapProperty :: Tx Bool
checkTreapProperty =
    do move (Down treapBranchPrio)
       CurIsAtom (InMemoryAtomD (IntegerD ourPrio)) <- cur
       move Up
       move Up
       move (Down treapBranchPrio)
       CurIsAtom (InMemoryAtomD (IntegerD parentPrio)) <- cur
       move Up -- Move back to parent
       return (parentPrio > ourPrio)

rotateTreap :: Int -> Tx ()
rotateTreap 0 = return () -- At root, so we're done!
rotateTreap lvl =
    do whichChild <- treapCheckLeftOrRight
       hasTreapProperty <- checkTreapProperty -- Checks treap property and moves up
       if hasTreapProperty then replicateM_ (lvl - 1) (move Up)
          else do case whichChild of
                    Left () -> do rotateMeRight
                                  rotateTreap (lvl - 1)
                    Right () -> do rotateMeLeft
                                   rotateTreap (lvl - 1)

treapInsert :: Int64 -> InMemoryD -> InMemoryD -> Tx ()
treapInsert newPrio key val =
    do (lvl, _) <- treapFind 0 (atomCmp key)
       res <- cur
       case res of
         CurHasTag tag
             | tag == treapLeafTag ->
                 do -- Now we're at a point in the tree where we could place our new branch...
                   move (Replace (treapBranch newPrio key val treapLeafS treapLeafS))
                   -- Now we're going to restore the heap property by doing rotations...
                   rotateTreap lvl
             | tag == treapBranchTag ->
                 -- We could only get here if the key is equal to the current node, so just replace the value...
                 do move (Down treapBranchValue)
                    move (Replace val)
                    move Up
                    replicateM_ lvl (move Up)

atomCmp :: InMemoryD -> Tx Ordering
atomCmp x = do res <- cur
               case res of
                 CurIsAtom (InMemoryAtomD atom) -> return (compare (eraseInMemoryD x) (SZippyD atom))
                 CurHasTag _ -> fail "atomCmp: Expecting atom for value"
