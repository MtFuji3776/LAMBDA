module Main where

import Lib

main :: IO ()
main = 
    let xs = map decodePair [0..300]
    in mapM_ print xs
