module Lexer ( module Lexer ) where

import Data.Either ()
import Data.Maybe ( isJust, fromJust )
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

type Possible a = Either Error a

err :: Error -> Possible a
err = Left

data TokenKind = Lambda | Dot | Open | Close | Star | Ident | String | End deriving (Eq, Show)

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
    lexerCurrent::String,
    parserPeeked:: Maybe Token
}

instance Show Lexer where
    show Lexer{
        lexerSource=source,
        lexerTokens=tokens,
        lexerLoc=loc,
        lexerStartLoc=start,
        lexerCurrent=curr,
        parserPeeked=tok
    } = "{ " ++ 
        (if isJust tok then show (fromJust tok) ++ " <- " else "") ++ 
        show tokens ++ 
        (if start /= loc then showLocIfWanted start ++ "'" ++ curr ++ "' <- " else "") ++
        (if null source || start /= loc then "" else " <- " ++ showLocIfWanted loc ++ "'" ++ source ++ "'") ++ 
        " }"

type LexerResult = Possible Lexer
type LexerMethod = Lexer -> LexerResult
type LexerMethodWith a = Lexer -> Possible (a, Lexer)

newLexer :: String -> Lexer
newLexer s = Lexer{
    lexerSource=s,
    lexerTokens=[],
    lexerLoc=newLoc,
    lexerStartLoc=newLoc,
    lexerCurrent="",
    parserPeeked=Nothing
}

lexErr :: String -> LexerMethod
lexErr msg = err . newError msg . lexerLoc

lexErrStartLoc :: String -> LexerMethod
lexErrStartLoc msg = err . newError msg . lexerStartLoc

-- Lexer Methods

lexerExhausted :: Lexer -> Bool
lexerExhausted lexer = null $ lexerSource lexer

lexerAdvance :: LexerMethod
lexerAdvance lexer = case lexerSource lexer of
    [] -> lexErr "Unexpected EOF" lexer
    (c:rest) -> return lexer{
            lexerSource=rest,
            lexerLoc=getLocAdvancer c $ lexerLoc lexer,
            lexerCurrent=lexerCurrent lexer ++ [c]
    }

lexerSkip :: LexerMethod
lexerSkip lexer = case lexerSource lexer of
    [] -> lexErr "Unexpected EOF" lexer
    (c:rest) -> return lexer{
            lexerSource=rest,
            lexerLoc=getLocAdvancer c $ lexerLoc lexer
    }

lexerExpect :: (Char -> Bool) -> String -> LexerMethod
lexerExpect f msg lexer = case lexerSource lexer of
    [] -> lexErr ("Expected `"++msg++"`, got EOF") lexer
    c:_ -> if f c
        then lexerAdvance lexer
        else lexErr ("Expected `"++msg++"`, got `"++[c]++"`") lexer

lexerExpectChar :: Char -> LexerMethod
lexerExpectChar c = lexerExpect (== c) [c]

lexerAssert :: (Char -> Bool) -> String -> LexerMethod
lexerAssert f msg lexer = case lexerSource lexer of
    [] -> lexErr ("Expected `"++msg++"`, got EOF") lexer
    c:_ -> if f c
        then lexerSkip lexer
        else lexErr ("Expected `"++msg++"`, got `"++[c]++"`") lexer

lexerAssertChar :: Char -> LexerMethod
lexerAssertChar c = lexerAssert (==c) [c]


takeCharsWhile :: (Char -> Bool) -> (String, String, Loc) -> (String, String, Loc)
takeCharsWhile f (curr, "", loc) = (curr, "", loc)
takeCharsWhile f (curr, c:r, loc) = if f c
    then takeCharsWhile f (curr ++ [c], r, getLocAdvancer c loc)
    else (curr, c:r, loc)

lexerAdvanceWhile :: (Char -> Bool) -> LexerMethod
lexerAdvanceWhile f lexer =
    case takeCharsWhile f ("", lexerSource lexer, lexerLoc lexer) of
        (chars, rest, loc) -> return lexer{
            lexerSource=rest,
            lexerLoc=loc,
            lexerCurrent=lexerCurrent lexer ++ chars
        }

lexerSkipWhile :: (Char -> Bool) -> LexerMethod
lexerSkipWhile f lexer =
    case takeCharsWhile f ("", lexerSource lexer, lexerLoc lexer) of
        (_, rest, loc) -> return lexer{
            lexerSource=rest,
            lexerLoc=loc
        }

lexerFlush :: LexerMethod
lexerFlush lexer = return lexer{
    lexerStartLoc=lexerLoc lexer,
    lexerCurrent=""
}

lexerGetCurrent :: Lexer -> (String, Loc)
lexerGetCurrent Lexer{lexerStartLoc=loc,lexerCurrent=curr} = (curr, loc)

-- Lexer Methods that add Tokens

appendToken :: Token -> LexerMethod
appendToken tok lexer = return lexer{lexerTokens=lexerTokens lexer ++ [tok]}

appendTokenFromFlush :: TokenKind -> LexerMethod
appendTokenFromFlush kind lexer = do
    let (curr, loc) = lexerGetCurrent lexer
    lexer <- appendToken (Token kind curr loc) lexer
    lexerFlush lexer

-- Main Lexer method

λlex :: LexerMethod
λlex lexer = do
    lexer <- lexerFlush lexer
    lexer <- case lexerSource lexer of
        [] -> return lexer
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
            | c == '*' -> do
                lexer <- lexerAdvance lexer
                appendTokenFromFlush Star lexer
            | c == '"' -> do
                lexer <- lexerSkip lexer
                lexer <- lexerAdvanceWhile (/= '"') lexer
                case lexerSource lexer of
                    [] -> lexErrStartLoc "Unterminated string literal" lexer
                    c:_ -> do
                        lexer <- lexerAssertChar '"' lexer
                        appendTokenFromFlush String lexer
            | isAlpha c -> do
                lexer <- lexerAdvanceWhile isAlpha lexer
                appendTokenFromFlush Ident lexer
            | isSpace c -> lexerSkipWhile isSpace lexer
            | otherwise -> lexErr ("Invalid character `"++[c]++"`") lexer
    if null (lexerSource lexer) then appendTokenFromFlush End lexer else λlex lexer

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

-- Parser Methods

parseError :: String -> LexerMethodWith a
parseError msg parser = do
    (tok, _) <- parserPeek parser
    err $ newError msg $ tokenLoc tok

parserNext :: LexerMethodWith Token
parserNext parser = case parserPeeked parser of
    Nothing -> case lexerTokens parser of
        [] -> error "TODO"
        (tok:rest) -> return (tok, parser{lexerTokens=rest})
    Just tok -> return (tok, parser{parserPeeked=Nothing})

parserPeek :: LexerMethodWith Token
parserPeek parser = do
    res <- parserNext parser
    let (tok, parser) = res
    return (tok, parser{parserPeeked=Just tok})

parserExpect :: TokenKind -> LexerMethodWith Token
parserExpect kind parser = do
    (tok, parser) <- parserPeek parser
    case tokenKind tok of
        kind1 | kind1 == kind -> parserNext parser
              | otherwise -> parseError
              ("Expected "++show kind++", but got "++show tok++"") parser

parserParseWhile :: LexerMethodWith a -> LexerMethodWith Bool -> LexerMethodWith [a]
parserParseWhile parseF pred parser = do
    (cond, parser) <- pred parser
    if cond then parserParseDoWhile parseF pred parser
    else return ([], parser)

parserParseDoWhile :: LexerMethodWith a -> LexerMethodWith Bool -> LexerMethodWith [a]
parserParseDoWhile parseF pred parser = do
    (a, parser) <- parseF parser
    (as, parser) <- parserParseWhile parseF pred parser
    return (a:as, parser)