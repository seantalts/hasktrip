module Main where

import Lib

main :: IO ()
main = do
    r <- getData
    putStrLn "Data loaded"
    putStrLn $ take 200 $ show r

