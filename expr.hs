{-# LANGUAGE ViewPatterns #-}
module Expr ( module Expr ) where

import Data.List ( elemIndex )
import Util ( joinByMap )
import Lexer
    ( Token(tokenContents, tokenKind),
      TokenKind(Lambda, Dot, Open, Close, Star, Ident, End),
      LexerMethodWith,
      tokenError,
      parserNext,
      parserPeek,
      parserExpect,
      parserParseDoWhile )

type Variable = (String, Int)

data Combinator = I | M | K | KI | C | B deriving (Eq, Show)

data Expr = Var Int | Free String | Appl [Expr] | Abs [Variable] Expr | Builtin Combinator
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
    | y <= 0 = x
    | otherwise = x ++ show (y - 1)

showHeads :: [Variable] -> String
showHeads [] = ""
showHeads xs = abstractFront ++ joinByMap showHead xs abstractMiddle ++ abstractBack
-- I'm quite sad that my elegent xs `joinBy` abstractMiddle is gone. :(
-- Sadly, all good things must come to an end. You'll be missed, `joinBy`.

invVar :: Variable -> Variable
invVar (base, n) = (base, -n-1)

var :: String -> Variable
var s = (s,0)

addVariables :: [Variable] -> Variable -> [Variable]
addVariables heads x@(base, n)
    | base /= "_" && x `elem` heads = addVariables heads (base, n + 1)
    | otherwise = heads ++ [x]

addTo :: [Variable] -> [Variable] -> [Variable]
addTo = foldl addVariables

showExpr :: [Variable] -> Expr -> String
showExpr heads (Var x)
    | x > 0 || x <= len = showHead $ heads !! (len - x)
    | otherwise = error "unreachable"
    where len = length heads
showExpr heads (Free x) = case last $ heads `addTo` [var x] of
    (_,n) | n > snd (var x) || invVar (var x) `elem` heads -> '*':x
          | otherwise -> x
showExpr heads (Appl (Appl xs:ys)) = showExpr heads $ Appl $ xs ++ ys
showExpr heads (Appl xs) = joinByMap (showApplicant $ showExpr heads) xs " "
showExpr heads1 (Abs [] body) = showExpr heads1 body
showExpr heads1 x@(Abs [head] body)
    = showHeads [last new_heads] ++
    showExpr (if x `isFreeAt` 0 then heads1 ++ [invVar head] else new_heads) body
        where new_heads = heads1 `addTo` [head]
showExpr heads1 (Abs (head:heads2) body) = showExpr heads1 $ Abs [head] $ Abs heads2 body
showExpr _ (Builtin x) = show x

instance Show Expr where show x = showExpr [] x

expandBuiltin :: Combinator -> Expr
expandBuiltin I = Abs [var "x"] $ Var 1
expandBuiltin M = Abs [var "x"] $ Appl [Var 1, Var 1]
expandBuiltin K = Abs [var "x", var "y"] $ Var 2
expandBuiltin KI = Abs [var "x", var "y"] $ Var 1
expandBuiltin C = Abs [var "f", var "a", var "b"] $ Appl [Var 3, Var 1, Var 2]
expandBuiltin B = Abs [var "f", var "g", var "b"] $ Appl [Var 3, Appl [Var 2, Var 1]]

simplifyBuiltin :: Expr -> Expr
simplifyBuiltin (Var x) = Var x
simplifyBuiltin (Free x) = Free x
simplifyBuiltin (Appl xs) = Appl $ map simplifyBuiltin xs
simplifyBuiltin (Abs heads body) = Abs heads $ simplifyBuiltin body
simplifyBuiltin (Builtin x) = expandBuiltin x

shift :: Int -> [Expr]
shift x = map Var [x+1..]

substitute :: [Expr] -> Expr -> Expr
substitute xs (Var x)  = xs !! (x - 1)
substitute xs (Free x) = Free x
substitute xs (Appl ys) = Appl $ map (substitute xs) ys
substitute xs (Abs [] body) = substitute xs body
substitute xs (Abs (param:heads) body) = Abs [param] $ substitute sigmas gamma
    where sigmas = Var 1 : map (substitute (shift 1)) xs
          gamma = Abs heads body
-- A builtin combinator should never have any free variables
substitute xs (Builtin x) = Builtin x

isFreeAt :: Expr -> Int -> Bool
isFreeAt (Var x) y = x /= y
isFreeAt (Free x) y = True
isFreeAt (Appl xs) x = all (`isFreeAt` x) xs
isFreeAt (Abs heads ys) x = ys `isFreeAt` (x + length heads)
isFreeAt (Builtin x) _ = True

simplify :: Expr -> Expr
simplify (Var x) = Var x
simplify (Free x) = Free x
simplify (Appl []) = error "unreachable"
simplify (Appl [x]) = simplify x
simplify (Appl (Var x:xs)) = Appl (Var x:xs)
simplify (Appl (Free x:xs)) = Appl (Free x:xs)
simplify (Appl (Appl xs:ys)) = simplify $ Appl (xs ++ ys)
simplify (Appl (Abs [] body:xs)) = simplify $ Appl (body:xs)
simplify (Appl (Abs [_] body:arg:xs)) = simplify $ Appl $ substitute (arg : shift 0) body : xs
simplify (Appl (Abs (param:heads) body:xs)) = simplify $ Appl $ Abs [param] (Abs heads body) : xs
simplify (Appl (Builtin x:xs)) = simplify $ Appl $ expandBuiltin x:xs
simplify (Abs [] body) = simplify body
simplify (Abs [head] body) = case simplify body of
    Var 1 -> Builtin I
    (Appl [Var 1]) -> Builtin I
    (Appl (reverse -> (Var 1:xs@(_:_)))) -- Eta Reduction
        | Appl xs `isFreeAt` 1 -> simplify $ substitute (shift (-1)) (Appl $ reverse xs)
    _ -> let new_body = simplify body in
        (if new_body == body then id else simplify) $
        (if Abs [head] body `isFreeAt` 0 then Abs [var "_"] else Abs [head])
        new_body
        -- TODO: Reduce clarifying numbers as much as possible.
        -- This may require changing simplify to take a list of heads, like showExpr
        -- or at least having a simplifyImpl that does, and simplify is just a wrapper
        -- for simplifyImpl [], which just means that no heads have been encountered at
        -- the top level of the expression.
simplify (Abs (head:heads) body) = simplify $ Abs [head] $ Abs heads body
simplify (Builtin x) = Builtin x

flatten :: Expr -> Expr
flatten (Var x) = Var x
flatten (Free x) = Free x
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

-- Parsing Methods

exprParseSingle :: [String] -> LexerMethodWith Expr
exprParseSingle heads parser = do
    (tok, parser) <- parserNext parser
    case tokenKind tok of
        Lambda -> do
            (tok, parser) <- parserExpect Ident parser
            let head = tokenContents tok
            (_, parser) <- parserExpect Dot parser
            (expr, parser) <- exprParseImpl (head : heads) parser
            return (Abs [var head] expr, parser)
        Open -> do
            (expr, parser) <- exprParseImpl heads parser
            (_, parser) <- parserExpect Close parser
            return (expr, parser)
        Star -> do
            (tok, parser) <- parserExpect Ident parser
            return (Free $ tokenContents tok, parser)
        Ident -> case x `elemIndex` heads of
            Nothing -> return (Free x, parser)
            Just n -> return (Var (n + 1), parser)
            where x = tokenContents tok
        -- String -> error "TODO: Parse strings" -- TODO: Make string a type of expression
        _ -> tokenError ("Expected expression, but got " ++ show tok) tok

shouldContParsingExprs :: LexerMethodWith Bool
shouldContParsingExprs parser = do
    (tok, parser) <- parserPeek parser
    let kind = tokenKind tok
    return (kind /= Close && kind /= End, parser)

exprParseImpl :: [String] -> LexerMethodWith Expr
exprParseImpl heads parser = do
    (exprs, parser) <- parserParseDoWhile (exprParseSingle heads) shouldContParsingExprs parser
    case exprs of
        [] -> error "unreachable"
        [expr] -> return (expr, parser)
        _ -> return (Appl exprs, parser)

exprParse :: LexerMethodWith Expr
exprParse = exprParseImpl []