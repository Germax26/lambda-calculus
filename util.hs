-- Utilily module with functions used in the rest of the program, yet aren't
-- sepecific to the program, and might as well be used in any other program.

-- They are here and not in the files in which they are used in order to not
-- clutter the code with general functions that are used in various unrelated
-- places throughout a file.

-- I am unaware if these are already implemented in the Haskell prelude or
-- standard library. If they are, then I will use the already implenented 
-- one and I will remove its implementation from here. If all functions here
-- get removed, then I will remove this module.

module Util ( module Util ) where

joinByMap :: (a -> [b]) -> [a] -> [b] -> [b]
joinByMap _ [] _ = []
joinByMap f (x:xs) s = f x ++ concatMap ((s ++).f) xs

joinBy :: [[a]] -> [a] -> [a]
joinBy = joinByMap id