{-# LANGUAGE ViewPatterns #-}
module Expr ( module Expr ) where

import Util ( joinByMap, joinBy )

data Combinator = I | M | K | KI | C deriving (Eq, Show)

data Expr = Var Int | Appl [Expr] | Abs [String] Expr | Builtin Combinator
    deriving (Eq)

-- please ignore all constants and functions that start with "abstract". 
-- They look dumb and they are, but it works and it allows
-- me to quickly change the representation of functions.

abstractFront :: [Char]
abstractFront = "λ" -- can be "\\" to mimic Haskell's lambda syntax
abstractBack :: [Char]
abstractBack = "." -- can be " -> " to mimic Haskell's lambda syntax
abstractMiddle :: [Char]
abstractMiddle = abstractBack ++ abstractFront
-- abstractMiddle = ","  -- represent uncurried functions with a comma seperating the parameters. i.e. λx,y.x 

showApplicant :: (Expr -> String) -> Expr -> String
showApplicant f (Appl xs) = "(" ++ f (Appl xs) ++ ")"
showApplicant f (Abs heads body) = "(" ++ f (Abs heads body) ++ ")"
showApplicant f x = f x

showHeads :: [String] -> String
showHeads [] = ""
showHeads xs = abstractFront ++ xs `joinBy` abstractMiddle ++ abstractBack

showExpr :: [String] -> Expr -> String
showExpr heads (Var x)
    | x <= 0 = error "TODO: Nonpositive indices"
    | x > len = error "TODO: Show free variables"
    | otherwise = heads !! (len - x)
    where len = length heads
showExpr heads (Appl xs) = joinByMap (showApplicant $ showExpr heads) xs " "
showExpr heads (Abs new_heads body) = showHeads new_heads ++ showExpr (heads ++ new_heads) body
showExpr _ (Builtin x) = show x

instance Show Expr where show x = showExpr [] x

expandBuiltin :: Combinator -> Expr
expandBuiltin I = Abs ["x"] $ Var 1
expandBuiltin M = Abs ["x"] $ Appl [Var 1, Var 1]
expandBuiltin K = Abs ["x", "y"] $ Var 2
expandBuiltin KI = Abs ["x", "y"] $ Var 1
expandBuiltin C = Abs ["f", "a", "b"] $ Appl [Var 3, Var 1, Var 2]

simplifyBuiltin :: Expr -> Expr
simplifyBuiltin (Var x) = Var x
simplifyBuiltin (Appl xs) = Appl $ map simplifyBuiltin xs
simplifyBuiltin (Abs heads body) = Abs heads $ simplifyBuiltin body
simplifyBuiltin (Builtin x) = expandBuiltin x

shift :: Int -> [Expr]
shift x = map Var [x+1..]

substitute :: [Expr] -> Expr -> Expr
substitute xs (Var x)  = xs !! (x - 1)
substitute xs (Appl ys) = Appl $ map (substitute xs) ys
substitute xs (Abs [] body) = substitute xs body
substitute xs (Abs (param:heads) body) = Abs [param] $ substitute sigmas gamma
    where sigmas = Var 1 : map (substitute (shift 1)) xs
          gamma = Abs heads body
-- A builtin combinator should never have any free variables
substitute xs (Builtin x) = Builtin x

isFreeAt :: Expr -> Int -> Bool
isFreeAt (Var x) y = x /= y
isFreeAt (Appl xs) x = all (`isFreeAt` x) xs
isFreeAt (Abs heads ys) x = ys `isFreeAt` (x + length heads) 
isFreeAt (Builtin x) _ = True

simplify :: Expr -> Expr
simplify (Var x) = Var x
simplify (Appl []) = error "unreachable"
simplify (Appl [x]) = simplify x
simplify (Appl (Var x:xs)) = Appl (Var x:xs)
simplify (Appl (Appl xs:ys)) = simplify $ Appl (xs ++ ys)
simplify (Appl (Abs [] body:xs)) = simplify $ Appl (body:xs)
simplify (Appl (Abs [_] body:arg:xs)) = simplify $ Appl $ substitute (arg : shift 0) body : xs
simplify (Appl (Abs (param:heads) body:xs)) = simplify $ Appl $ Abs [param] (Abs heads body) : xs
simplify (Appl (Builtin x:xs)) = simplify $ Appl $ expandBuiltin x:xs
simplify (Abs heads body) = case body of
    (Appl [Var 1]) -> Builtin I
    (Appl (reverse -> (Var 1:xs@(_:_)))) -- Eta Reduction
        | Appl xs `isFreeAt` 1 -> simplify $ substitute (shift (-1)) (Appl $ reverse xs)
    _ -> (if null heads then id else Abs heads) $ simplify body
simplify (Builtin x) = Builtin x

flatten :: Expr -> Expr
flatten (Var x) = Var x
flatten (Appl (Appl xs:ys)) = flatten $ Appl $ xs ++ ys
flatten (Appl xs) = Appl $ map flatten xs
flatten (Abs [] body) = flatten body
flatten (Abs heads1 (Abs heads2 body)) = flatten $ Abs (heads1 ++ heads2) body
flatten (Abs heads body) = Abs heads $ flatten body
flatten (Builtin x) = Builtin x

_I :: Expr
_I = Builtin I

_M :: Expr
_M = Builtin M

_OMEGA :: Expr
_OMEGA = Appl [_M, _M]

_K :: Expr
_K = Builtin K

_KI :: Expr
_KI = Builtin KI

_C :: Expr
_C = Builtin C