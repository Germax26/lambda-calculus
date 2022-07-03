{-# LANGUAGE ViewPatterns #-}
module Expr ( module Expr ) where

import Util ( joinByMap )

type Variable = (String, Int)

data Combinator = I | M | K | KI | C | B deriving (Eq, Show)

data Expr = Var Int | Appl [Expr] | Abs [Variable] Expr | Builtin Combinator
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

showHead :: Variable -> String
showHead ("_", _) = "_"
showHead (x, y)
    | y < 0 = x
    | otherwise = x ++ show y

showHeads :: [Variable] -> String
showHeads [] = ""
showHeads xs = abstractFront ++ joinByMap showHead xs abstractMiddle ++ abstractBack
-- I'm quite sad that my elegent xs `joinBy` abstractMiddle is gone. :(
-- Sadly, all good things must come to an end. You'll be missed, `joinBy`.

addVariables :: [Variable] -> Variable -> [Variable]
addVariables heads x@(base, n)
    | base /= "_" && x `elem` heads = addVariables heads (base, n + 1)
    | otherwise = heads ++ [x]

addTo :: [Variable] -> [Variable] -> [Variable]
addTo = foldl addVariables

showExpr :: [Variable] -> Expr -> String
showExpr heads (Var x)
    | x <= 0 = error "TODO: Nonpositive indices"
    | x > len = error "TODO: Show free variables"
    | otherwise = showHead $ heads !! (len - x)
    where len = length heads
showExpr heads (Appl (Appl xs:ys)) = showExpr heads $ Appl $ xs ++ ys
showExpr heads (Appl xs) = joinByMap (showApplicant $ showExpr heads) xs " "
showExpr heads1 (Abs [] body) = showExpr heads1 body
showExpr heads1 x@(Abs [head] body)
    = showHeads [last new_heads] ++ 
    showExpr (if x `isFreeAt` 0 then heads1 ++ [("_",0)] else new_heads) body
        where new_heads = heads1 `addTo` [head]
showExpr heads1 (Abs (head:heads2) body) = showExpr heads1 $ Abs [head] $ Abs heads2 body
showExpr _ (Builtin x) = show x

instance Show Expr where show x = showExpr [] x

expandBuiltin :: Combinator -> Expr
expandBuiltin I = Abs [("x", -1)] $ Var 1
expandBuiltin M = Abs [("x", -1)] $ Appl [Var 1, Var 1]
expandBuiltin K = Abs [("x", -1), ("y", -1)] $ Var 2
expandBuiltin KI = Abs [("x", -1), ("y", -1)] $ Var 1
expandBuiltin C = Abs [("f", -1), ("a", -1), ("b", -1)] $ Appl [Var 3, Var 1, Var 2]
expandBuiltin B = Abs [("f", -1), ("g", -1), ("b", -1)] $ Appl [Var 3, Appl [Var 2, Var 1]]

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
    Var 1 -> Builtin I
    (Appl [Var 1]) -> Builtin I
    (Appl (reverse -> (Var 1:xs@(_:_)))) -- Eta Reduction
        | Appl xs `isFreeAt` 1 -> simplify $ substitute (shift (-1)) (Appl $ reverse xs)
    _ -> let new_body = simplify body in
        (if new_body == body then id else simplify) $
        (case heads of
            [] -> id
            (_:rest)| Abs heads body `isFreeAt` 0 -> Abs $ ("_",0) : rest
                    | otherwise -> Abs heads
        ) new_body
        -- TODO: Reduce clarifying numbers as much as possible.
        -- This may require changing simplify to take a list of heads, like showExpr
        -- or at least having a simplifyImpl that does, and simplify is just a wrapper
        -- for simplifyImpl [], which just means that no heads have been encountered at
        -- the top level of the expression.

simplify (Builtin x) = Builtin x

flatten :: Expr -> Expr
flatten (Var x) = Var x
flatten (Appl (Appl xs:ys)) = flatten $ Appl $ xs ++ ys
flatten (Appl [x]) = flatten x
flatten (Appl xs) = Appl $ map flatten xs
flatten (Abs [] body) = flatten body
flatten (Abs heads1 (Abs heads2 body)) = flatten $ Abs (heads1 `addTo` heads2) body
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

_B :: Expr
_B = Builtin B