module Lexer ( Lexer, Error, lexerTokens, lexStr, repl ) where

import Data.Either ()
import Data.Char ( isAlpha, isSpace )
import System.IO ( hFlush, stdout )

data Loc = Loc{
    locFilepath::String,
    locRow::Integer,
    locCol::Integer
} deriving Eq

instance Show Loc where
    show Loc{
        locFilepath=path,
        locRow=row,
        locCol=col
    } = path ++ ":" ++ show row ++ ":" ++ show col

showLoc :: Bool -- for debugging
showLoc = False

showLocIfWanted :: Loc -> String
showLocIfWanted loc
    | showLoc = show loc ++ ": "
    | otherwise = ""

newLoc :: Loc
newLoc = Loc{locFilepath="",locRow=1,locCol=1}

advanceLocCol :: Loc -> Loc
advanceLocCol loc = loc{locCol=locCol loc + 1}

advanceLocRow :: Loc -> Loc
advanceLocRow loc = loc{locCol=locCol newLoc, locRow=locRow loc + 1}

getLocAdvancer :: Char -> Loc -> Loc
getLocAdvancer c = if c == '\n' then advanceLocRow else advanceLocCol

data Error = Error{
    errMessage::String,
    errLoc::Loc
}

newError :: String -> Loc -> Error
newError msg loc = Error{errMessage=msg,errLoc=loc}

instance Show Error where
    show Error{errMessage=msg,errLoc=loc} = show loc ++ ": ERROR: " ++ msg

data TokenKind = Lambda | Dot | Open | Close | Ident | String deriving Show

data Token = Token{
    tokenKind::TokenKind,
    tokenContents::String,
    tokenLoc::Loc
}

instance Show Token where
    show Token{
        tokenKind=kind,
        tokenContents=contents,
        tokenLoc=loc
    } = show kind ++ "(" ++ showLocIfWanted loc ++ "'" ++ contents ++ "')"

data Lexer = Lexer{
    lexerSource::String,
    lexerTokens::[Token],
    lexerLoc::Loc,
    lexerStartLoc::Loc,
    lexerCurrent::String
}

instance Show Lexer where
    show Lexer{
        lexerSource=source,
        lexerTokens=tokens,
        lexerLoc=loc,
        lexerStartLoc=start,
        lexerCurrent=curr
    } = "{" ++ show tokens ++ " " ++ (if start /= loc then showLocIfWanted start ++ "'" ++ curr ++ "' " else "") ++ showLocIfWanted loc ++ "'" ++ source ++ "'}"

newLexer :: String -> Lexer
newLexer s = Lexer{
    lexerSource=s,
    lexerTokens=[],
    lexerLoc=newLoc,
    lexerStartLoc=newLoc,
    lexerCurrent=""
}

type LexerResult = Either Error Lexer
err :: Error -> LexerResult
err = Left

lexErr :: String -> Lexer -> LexerResult
lexErr msg = err . newError msg . lexerLoc

lexErrStartLoc :: String -> Lexer -> LexerResult
lexErrStartLoc msg = err . newError msg . lexerStartLoc

-- Lexer Methods

lexerExhausted :: Lexer -> Bool
lexerExhausted lexer = null $ lexerSource lexer

lexerAdvance :: Lexer -> LexerResult
lexerAdvance lexer = case lexerSource lexer of
    [] -> lexErr "Unexpected EOF" lexer
    (c:rest) -> return lexer{
            lexerSource=rest,
            lexerLoc=getLocAdvancer c $ lexerLoc lexer,
            lexerCurrent=lexerCurrent lexer ++ [c]
    }

lexerSkip :: Lexer -> LexerResult
lexerSkip lexer = case lexerSource lexer of
    [] -> lexErr "Unexpected EOF" lexer
    (c:rest) -> return lexer{
            lexerSource=rest,
            lexerLoc=getLocAdvancer c $ lexerLoc lexer
    }

lexerExpect :: (Char -> Bool) -> String -> Lexer -> LexerResult
lexerExpect f msg lexer = case lexerSource lexer of
    [] -> lexErr ("Expected `"++msg++"`, got EOF") lexer
    c:_ -> if f c
        then lexerAdvance lexer
        else lexErr ("Expected `"++msg++"`, got `"++[c]++"`") lexer

lexerExpectChar :: Char -> Lexer -> LexerResult
lexerExpectChar c = lexerExpect (== c) [c]

lexerAssert :: (Char -> Bool) -> String -> Lexer -> LexerResult
lexerAssert f msg lexer = case lexerSource lexer of
    [] -> lexErr ("Expected `"++msg++"`, got EOF") lexer
    c:_ -> if f c
        then lexerSkip lexer
        else lexErr ("Expected `"++msg++"`, got `"++[c]++"`") lexer

lexerAssertChar :: Char -> Lexer -> LexerResult
lexerAssertChar c = lexerAssert (==c) [c]

lexerPeek :: Lexer -> Char
lexerPeek lexer
    | lexerExhausted lexer = error "Lexer is exhausted"
    | otherwise = head $ lexerSource lexer

takeCharsWhile :: (Char -> Bool) -> (String, String, Loc) -> (String, String, Loc)
takeCharsWhile f (curr, "", loc) = (curr, "", loc)
takeCharsWhile f (curr, c:r, loc) = if f c
    then takeCharsWhile f (curr ++ [c], r, getLocAdvancer c loc)
    else (curr, c:r, loc)

lexerAdvanceWhile :: (Char -> Bool) -> Lexer -> LexerResult
lexerAdvanceWhile f lexer =
    case takeCharsWhile f ("", lexerSource lexer, lexerLoc lexer) of
        (chars, rest, loc) -> return lexer{
            lexerSource=rest,
            lexerLoc=loc,
            lexerCurrent=lexerCurrent lexer ++ chars
        }

lexerFlush :: Lexer -> LexerResult
lexerFlush lexer = return lexer{
    lexerStartLoc=lexerLoc lexer,
    lexerCurrent=""
}

lexerGetCurrent :: Lexer -> (String, Loc)
lexerGetCurrent Lexer{lexerStartLoc=loc,lexerCurrent=curr} = (curr, loc)

-- Lexer Methods that add Tokens

appendToken :: Token -> Lexer -> LexerResult
appendToken tok lexer = return lexer{lexerTokens=lexerTokens lexer ++ [tok]}

appendTokenFromFlush :: TokenKind -> Lexer -> LexerResult
appendTokenFromFlush kind lexer = do
    let (curr, loc) = lexerGetCurrent lexer
    lexer <- appendToken (Token kind curr loc) lexer
    lexerFlush lexer

-- Lexer Methods for differnt tokens

lexIdent :: Lexer -> LexerResult
lexIdent lexer = case lexerSource lexer of
    [] -> lexErr "Expected Identifier, got EOF" lexer
    c:_ | isAlpha c -> do
            lexer <- lexerAdvanceWhile isAlpha lexer
            appendTokenFromFlush Ident lexer
        | otherwise -> lexErr "Invalid character for identifier" lexer

lexString :: Lexer -> LexerResult
lexString lexer = case lexerSource lexer of
    [] -> lexErr "Expected String, got EOF" lexer
    c:_ -> do
        lexer <- lexerAssertChar '"' lexer
        let loc = lexerLoc lexer
        lexer <- lexerAdvanceWhile (/= '"') lexer
        case lexerSource lexer of
            [] -> lexErrStartLoc "Unterminal string literal" lexer
            c:_ -> do
                lexer <- lexerAssertChar '"' lexer
                appendTokenFromFlush String lexer

-- Main Lexer method

λlex :: Lexer -> LexerResult
λlex lexer = do
    lexer <- lexerFlush lexer
    lexer <- case lexerSource lexer of
        [] -> lexErr "Empty expression" lexer
        c:_ | c == 'λ' || c == '\\' -> do
                lexer <- lexerAdvance lexer
                appendTokenFromFlush Lambda lexer
            | c == '.' -> do
                lexer <- lexerAdvance lexer
                appendTokenFromFlush Dot lexer
            | c == '-' -> do
                lexer <- lexerAdvance lexer
                lexer <- lexerExpectChar '>' lexer
                appendTokenFromFlush Dot lexer
            | c == '(' -> do
                lexer <- lexerAdvance lexer
                appendTokenFromFlush Open lexer
            | c == ')' -> do
                lexer <- lexerAdvance lexer
                appendTokenFromFlush Close lexer
            | c == '"' -> lexString lexer
            | isAlpha c -> lexIdent lexer
            | isSpace c -> lexerAdvanceWhile isSpace lexer
            | otherwise -> lexErr ("Invalid character `"++[c]++"`") lexer
    if null $ lexerSource lexer then return lexer else λlex lexer

lexStr :: String -> LexerResult
lexStr = λlex . newLexer

-- REPL

replRec :: IO ()
replRec = do
    putStr "lexer> "
    hFlush stdout -- prevents buffering issues
    line <- getLine
    either print (print . lexerTokens) $ lexStr line
    replRec

repl :: IO ()
repl = do
    putStrLn "Lambda Calculus lexer."
    putStrLn "Will display all tokens used in parsing given an input string."
    putStrLn "Use ^C to quit.\n"
    replRec