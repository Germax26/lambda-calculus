module Main where

data Combinator = I | M | K | KI | C deriving (Eq, Show)

data Expr = Var String | Appl [Expr] | Abs [String] Expr | Builtin Combinator
    deriving (Eq)

joinByMap :: (a -> [b]) -> [a] -> [b] -> [b]
joinByMap _ [] _ = []
joinByMap f (x:xs) s = f x ++ concatMap ((s ++).f) xs

joinBy :: [[a]] -> [a] -> [a]
joinBy = joinByMap id

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

abstract :: [String] -> String
abstract [] = error "unreachable"
abstract xs = abstractFront ++ xs `joinBy` abstractMiddle ++ abstractBack

instance Show Expr where
    show (Var x) = x
    show (Appl []) = error "unreachable"
    show (Appl [x]) = show x
    show (Appl xs) = joinByMap showApplicant xs " "
        where showApplicant :: Expr -> String
              showApplicant (Appl xs) = "(" ++ show (Appl xs) ++ ")"
              showApplicant (Abs heads body) = "(" ++ show (Abs heads body) ++ ")"
              showApplicant x = show x
    show (Abs [] body) = show body
    show (Abs heads body) = abstract heads ++ show body
    show (Builtin x) = show x

betaReduce :: Expr -> String -> Expr -> Expr
betaReduce (Var x) y z = if y == x then z else Var x
betaReduce (Appl xs) y z = Appl $ map (\x -> betaReduce x y z) xs
betaReduce (Abs heads body) y z = if y `elem` heads then Abs heads body else Abs heads $ betaReduce body y z
betaReduce (Builtin x) y z = Builtin x

expandBuiltin :: Combinator -> Expr
expandBuiltin I = Abs ["x"] $ Var "x"
expandBuiltin M = Abs ["x"] $ Appl [Var "x", Var "x"]
expandBuiltin K = Abs ["x", "y"] $ Var "x"
expandBuiltin KI = Abs ["x", "y"] $ Var "y"
expandBuiltin C = Abs ["f", "a", "b"] $ Appl [Var "f", Var "b", Var "a"]

simplifyBuiltin :: Expr -> Expr
simplifyBuiltin (Var x) = Var x
simplifyBuiltin (Appl xs) = Appl $ map simplifyBuiltin xs
simplifyBuiltin (Abs heads body) = Abs heads $ simplifyBuiltin body
simplifyBuiltin (Builtin x) = expandBuiltin x

simplify :: Expr -> Expr
simplify (Var x) = Var x
simplify (Appl []) = error "unreachable"
simplify (Appl [x]) = simplify x
simplify (Appl (Var x:xs)) = Appl (Var x:xs)
simplify (Appl (Appl xs:ys)) = simplify $ Appl (xs ++ ys)
simplify (Appl (Abs [] body:xs)) = simplify $ Appl (body:xs)
simplify (Appl (Abs (param:heads) body:arg:xs)) = simplify $ Appl $ simplify (Abs heads $ betaReduce body param arg) : xs
simplify (Appl (Builtin x:xs)) = simplify $ Appl $ expandBuiltin x:xs
simplify (Abs heads body) = (if null heads then id else Abs heads) $ simplify body
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

main :: IO ()
main = undefined