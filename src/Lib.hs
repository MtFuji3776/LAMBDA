{-# LANGUAGE OverloadedLists #-}
module Lib
    ( encodePair
    , encodePair'
    , decodePair
    , encodeFinSet
    , decodeFinSet
    ) where

import Data.Set (Set)
import qualified Data.Set as S

-- ℕの二項積からℕへの全単射。幅優先探索式に添字付けするのがミソ
encodePair :: (Num a, Integral a) => a -> a -> a
encodePair n m = 
    let k = n + m
        k' = div (k * (k+1)) 2
    in k' + m

-- encodePairのuncurry化
encodePair' :: (Num a,Integral a) => (a,a) -> a
encodePair' = uncurry encodePair

-- encodePair'関数の逆写像
decodePair :: (Num a,Integral a) => a -> (a,a)
decodePair 1 = (1,0) --これだけ二分探索をしくじるので基底で定義しておく
decodePair x =
    let cond1 n k = let k'  = div (k*(k+1)) 2 in k' <= n
        cond2 n k = let k'' = div (k*(k+3)) 2 in n  <= k''
        binSearch n l r -- 二分探索。nは基準となる数、lとrは探索区間。
            | cond1 n m && cond2 n m = m -- 指定した区間にnが属する時には区間の中点が解
            | cond1 n m              = binSearch n m r -- nが区間の上界に来る時には探索区間を右に寄せる
            | otherwise              = binSearch n l m -- nが区間の下界に来る時には探索区間を左に寄せる
                    where m = div (l+r) 2
        k = binSearch x 0 x -- x = 1の場合を除き上手くいくことが数学的に示せる
        k' = div (k*(k+1)) 2
        m = x - k' -- encodePairの定義式を同値変形したもの
        n = k - m  -- 今、k = n + mという条件式が成り立っている。これは幅優先探索によるもの。
    in (n,m)

-- ℕの有限部分集合の全体とℕとを一対一で結ぶ全単射
    -- ℕの有限部分集合の特性関数を考えて、さらにその特性関数を2進数と見做した時の値を割り当てる。
encodeFinSet :: (Num a, Integral a) => Set a -> a
encodeFinSet s
    | S.null s = 0
    | otherwise = S.foldr (+) 0 $ S.map (\x -> product (replicate (fromIntegral x) 2)) s

-- encodeFinSetの逆写像。
    -- 自然数値を受け取ると、それを二進数展開した時に1になる桁の位をSetにまとめて返す。
decodeFinSet :: (Num a,Integral a) => a -> Set a
decodeFinSet n = 
    let decodeFinSet_ :: (Num a,Integral a) => a -> a -> Set a -> Set a
        decodeFinSet_ 0 c s = s
        decodeFinSet_ m c s
            | even m    = decodeFinSet_ (div m 2) (c+1) s
            | otherwise = decodeFinSet_ (m-1) c (S.insert c s)
    in decodeFinSet_ n 0 S.empty

-- ℕの冪集合上のScott連続関数は、写像としてのグラフを介して自然数の冪集合の元と標準的に同一視できる
    -- この関数は各自然数n毎にグラフの部分集合を返す関数。[0..]にでもmapすればgraphの全体が得られる
    -- f e_nが無限集合の場合はこの関数でも無限ループする
graphN :: (Num a,Integral a) => (Set a -> Set a) -> a -> Set a
graphN f n = 
    let e_n = decodeFinSet n
        es   = S.toList . f $ e_n
    in S.fromList [encodePair n m | m <- es]

fun :: (Num a , Integral a) => Set a -> (Set a -> Set a)
fun u x =
    let x' = S.map decodePair x -- まずxの元をペアに変換
        isIncluded v (n,m) =    -- 集合vとペア(n,m)を渡すと、e_nがvに含まれるかどうか判定する述語
            let e_n = decodeFinSet n
            in S.isSubsetOf e_n v
        x'' = S.filter (isIncluded u) x' -- x'の元のうち、ペアの第一成分のdecodeがuに含まれているものだけ残す
    in S.map snd x'' -- 第二成分だけ取り出して所望の集合を得る
-- ℕの部分集合はℕ上の二項関係と自然に同一視できる、という性質とfunの定義が関係している気がする。

--fun u x = S.fromList [m | e_n <- S.toList (S.powerSet u), let n = encodeFinSet e_n,   m <- S.toList $ S.filter (\t -> S.member (encodePair n t) x) [0..n] ]