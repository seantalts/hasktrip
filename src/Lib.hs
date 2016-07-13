module Lib
    ( getData
    ) where

import Data.RDF

parse :: String -> IO (Either ParseFailure HashMapS)
parse = parseURL (TurtleParser Nothing Nothing)

getData :: IO HashMapS
getData = do
    r <- parse "http://wikidata.dbpedia.org/downloads/sample/wikidatawiki-20150330-raw-reified.ttl"
    return $ fromEither r
