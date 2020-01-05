{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Lib where

import qualified Data.Map as M
import qualified Data.Set as S
import Graphics.Scad
import Linear.V2
import Linear.V3
import Protolude

putTxtLn :: (MonadIO m) => Text -> m ()
putTxtLn = putStrLn

paths :: [[V3 Int]]
paths =
  let c = V3 0 1 0
      p1 = mkList <$> mkPaths c (M.fromList [(V3 0 0 0, 0), (c, 1)])
      p2 =
        filter (maybe False notCorner . lastMay) $
          mkList
            <$> mkPaths
              c
              (M.fromList [(V3 1 1 0, 0), (c, 1)])
   in p1 <> p2
  where
    isValid (V3 x y z) = x >= 0 && x < 3 && y >= 0 && y < 3 && z >= 0 && z < 3
    notCorner (V3 x y z) = x == 1 || y == 1 || z == 1
    nextPos (V3 x y z) =
      filter
        isValid
        [ V3 (x + 1) y z,
          V3 (x - 1) y z,
          V3 x (y + 1) z,
          V3 x (y - 1) z,
          V3 x y (z + 1),
          V3 x y (z - 1)
        ]
    mkPaths _ p | M.size p == 27 = pure p
    mkPaths cur p = do
      nxt <- nextPos cur
      guard (M.notMember nxt p)
      mkPaths nxt (M.insert nxt (M.size p) p)
    mkList = fmap fst . sortOn snd . M.toList

countStraight :: [V3 Int] -> Int
countStraight = go 0
  where
    go n (a : rs@(b : c : _))
      | a - b == b - c = go (n + 1) rs
      | otherwise = go n rs
    go n _ = n

nicePaths :: [[V3 Int]]
nicePaths = filter ((<= 2) . countStraight) paths

data Block
  = End
  | Straight
  | Corner
  | BendUp
  | BendDown
  deriving (Show, Eq, Ord)

isBend :: Block -> Bool
isBend BendUp = True
isBend BendDown = True
isBend _ = False

toBlocks :: [V3 Int] -> [Block]
toBlocks (a : rs@(b : c : _))
  | a - b == b - c = Straight : toBlocks rs
  | otherwise = Corner : toBlocks rs
toBlocks _ = []

toBlocks' :: [Int] -> [V3 Int] -> [Block]
toBlocks' = go 0 Nothing
  where
    go i (Just a) (j : js) (b : rs@(c : d : _))
      | i == j =
        let v = triple (b - a) (c - b) (d - c)
            tl = go (i + 1) (Just b) js rs
         in -- traceShow (v, b - a, c - b, d - c) $
            if
              | v > 0 -> BendUp : tl
              | v < 0 -> BendDown : tl
              | otherwise -> if b - c == c - d then Straight : tl else Corner : tl
    go i _ js (b : rs@(c : d : _)) =
      let tl = go (i + 1) (Just b) js rs
       in if b - c == c - d then Straight : tl else Corner : tl
    go _ _ _ _ = []

hasBend :: [Block] -> Bool
hasBend = or . fmap isBend

bends :: [V3 Int] -> [Int]
bends p = filter (\j -> hasBend $ toBlocks' [j] p) [1 .. 26]

-- myPath = nicePaths !! 3
myPath :: [V3 Int]
myPath =
  [ V3 0 0 0,
    V3 0 1 0,
    V3 1 1 0,
    V3 1 2 0,
    V3 2 2 0,
    V3 2 1 0,
    V3 2 0 0,
    V3 1 0 0,
    V3 1 0 1,
    V3 2 0 1,
    V3 2 0 2,
    V3 2 1 2,
    V3 2 1 1,
    V3 2 2 1,
    V3 2 2 2,
    V3 1 2 2,
    V3 0 2 2,
    V3 0 1 2,
    V3 1 1 2,
    V3 1 0 2,
    V3 0 0 2,
    V3 0 0 1,
    V3 0 1 1,
    V3 1 1 1,
    V3 1 2 1,
    V3 0 2 1,
    V3 0 2 0
  ]

myBlocks :: [Block]
myBlocks = End : toBlocks' [9, 19] myPath <> [End]

findFlat :: [Block] -> [[V2 Int]]
findFlat = let o = V2 0 0 in go (S.singleton o) [] o
  where
    z0 (V2 x y) = V3 x y 0
    go :: Set (V2 Int) -> [V2 Int] -> V2 Int -> [Block] -> [[V2 Int]]
    go _ path cur [] = [reverse (cur : path)]
    go past path@(p1 : p2 : _) cur (k : ks) | isBend k = do
      let d1 = cur - p1
          d2 = p1 - p2
          sgn = case k of
            BendUp -> 1
            _ -> -1
      guard (sgn * triple (z0 d2) (z0 d1) (V3 0 0 1) > 0)
      nxt <- [cur + d1]
      guard $ S.notMember nxt past
      go (S.insert nxt past) (cur : path) nxt ks
    go past path@(p : _) cur (k : ks) = do
      let d = cur - p
      nxt <- case k of
        Corner -> [cur + perp d, cur - perp d]
        _ -> [cur + d]
      guard $ S.notMember nxt past
      go (S.insert nxt past) (cur : path) nxt ks
    go past path cur (_ : ks) = do
      nxt <- [V2 0 1]
      go (S.insert nxt past) (cur : path) nxt ks

eps :: Double
eps = 1e-3

tol :: Double
tol = 0.2

block :: Double -> Form'
block w = cube (w - 2 * tol)

pivot' :: Double -> Form'
pivot' w =
  let h = 0.1 * w
      r = 0.4 * w
   in -- rotate'
      --  (V3 (pi / 2) 0 0)
      ( ( translate
            (V3 0 0 (- (w / 2 - h) + eps))
            ( cylinder2'
                (h - tol + 2 * eps)
                (r - h - tol - eps, r - 2 * tol + eps)
            )
            <#> ( translate
                    ( V3
                        0
                        (- r + h + tol + w * (1 + 1 / sqrt 2))
                        (- (w / 2 - h) + w * (1 - 1 / sqrt 2))
                    )
                    . rotate' (V3 (- pi / 4) 0 0)
                    . rotate' (V3 0 (pi / 4) 0)
                    $ cube (2 * w)
                )
          -- (translate (V3 0 (-r + h + tol + w / sqrt 2) (-(w / 2 - h) - w / sqrt 2)) .
          --  rotate' (V3 (pi/4) 0 0) $
          --  cube (2 * w))
          -- (translate (V3 0 0 (-w / 2 + h)) .
          --  rotate' (V3 (-pi / 4) 0 0) . scale (V3 1 (1 / sqrt 2) 1) $
          --  cylinder w (r - h - tol))
        )
          <+> translate
            (V3 0 0 (- (w / 2) - eps - tol))
            (cylinder2' (h + 2 * eps + tol) (r + eps, r - h - eps - tol))
          <+> hidden
            ( block w
                <-> translate
                  (V3 0 0 (- (w / 2 - h) - eps))
                  ( cylinder2'
                      (h + tol + eps)
                      (r - h + tol - eps, r + 2 * tol)
                  )
                <-> translate
                  (V3 0 0 (- (w / 2) - eps))
                  ( cylinder2'
                      (h + 2 * eps)
                      (r + tol + eps, r - h + tol - eps)
                  )
            )
      )

pivot :: Double -> Form'
pivot w =
  let h = 0.3 * w
      r = 0.45 * w
   in rotate'
        (V3 (pi / 2) 0 0)
        ( ( ( translate
                (V3 0 0 (- (w / 2 + tol) + eps))
                (cylinder2' (h + tol + eps) (r - h - 3 * tol - eps, r - 2 * tol))
                <+> translate
                  (V3 0 (- tol) (- (w / 2) + tol - eps))
                  (cylinder (4 * tol + eps) (r - h))
            )
              <#> ( translate
                      ( V3
                          0
                          (- r + h - tol + w * (1 + 1 / sqrt 2))
                          (- (w / 2 + tol) + w * (1 - 1 / sqrt 2))
                      )
                      . rotate' (V3 (- pi / 4) 0 0)
                      . rotate' (V3 0 (pi / 4) 0)
                      $ cube (2 * w)
                  )
          )
            <+> ( block w
                    <-> translate
                      (V3 0 0 (- (w / 2 - tol) - eps))
                      ( cylinder w r
                          <#> cylinder2' (h + tol + eps) (r - h + tol - eps, r + 2 * tol)
                      )
                )
        )

hinge :: Double -> Form'
hinge w = _

snake :: Form'
snake =
  -- block 10
  fn 200 (translate (V3 0 10 0) (block 10) <+> pivot 10)
    <#> translate (V3 25 0 0) (cube 50)

someFunc :: IO ()
someFunc = do
  putTxtLn "snake"
  putTxtLn ""
  let (path : _) = findFlat myBlocks
  print path
  putTxtLn ""
  printScad snake
  putTxtLn ""
  writeScad "snake.scad" snake
  putErrText ("Helloworld")
