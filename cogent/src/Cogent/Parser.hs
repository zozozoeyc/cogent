--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE LambdaCase, RecordWildCards, TupleSections, FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Cogent.Parser where

import Cogent.Common.Syntax hiding (Prefix)
import Cogent.Common.Types
import Cogent.Compiler
import qualified Cogent.Preprocess as PP
import Cogent.Surface
import Cogent.Util (getStdIncFullPath, (.*), (.**))

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative hiding (many, (<|>), optional)
import Data.Monoid (mconcat)
#endif
import qualified Control.Applicative as App
import Control.Arrow (left, second)
import Control.Monad
import Control.Monad.Identity
import Data.Char
import Data.Foldable as F (fold)
import Data.IORef
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Error (ParseError)
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Pos
import Text.Parsec.Prim
import qualified Text.Parsec.Token as T
import System.Directory
import System.FilePath

-- import Debug.Trace


type Parser a = ParsecT String S Identity a

newtype S = ParserState { avoidInit :: Bool }


language :: LanguageDef st
language = haskellStyle
           { T.reservedOpNames = ["+","*","/","%","&&","||",">=","<=",">","<","==","/="
                                 ,".&.",".|.",".^.",">>","<<"
                                 ,":","=","!",":<",".","_","..","#","$","::"
                                 ,"@","@@"  -- DocGent
                                 ,"@{"
                                 ,"->","=>","~>","<=","|","|>"]
           , T.reservedNames   = ["let","in","type","include","all","take","put","inline","upcast"
                                 ,"variant","record","at","layout","pointer"
                                 ,"if","then","else","not","complement","and","True","False","o"
#ifdef BUILTIN_ARRAYS
                                 ,"array","map2","@take","@put"]
#else
                                 ]
#endif
           , T.identStart = letter
           }

T.TokenParser {..} = cppLineTokenParser $ T.makeTokenParser language

sepByAligned1 p s c = (:) <$> p <*> many (getPosition >>= \o -> guard (sourceColumn o == c) >> s >> p)

manyAligned1Until p end c = do
  l0 <- getPosition
  guard (sourceColumn l0 == c)
  (:) <$> p <*> scan
  where
    scan  = do { _ <- try end; return [] }
          <|>
            do { l <- getPosition; guard (sourceColumn l == c); (:) <$> p <*> scan }

-- manyAligned1 p = do whiteSpace; c <- sourceColumn <$> getPosition
--                     (:) <$> p <*> many (whiteSpace >> getPosition >>= \o -> guard (sourceColumn o == c) >> p)

variableName = try (do (x:xs) <- identifier
                       (if isLower x then return else unexpected) $ x:xs)

typeConName = try (do (x:xs) <- identifier
                      (if isUpper x then return else unexpected) $ x:xs)

-- @p <= 0@ means unknown position
avoidInitial = do
  ParserState a <- getState
  if not a
    then return ()
    else do whiteSpace; p <- sourceColumn <$> getPosition; guard (p > 1 || p <= 0)


repDecl :: Parser DataLayoutDecl
repDecl = DataLayoutDecl <$> getPosition <*> typeConName <* reservedOp "=" <*> repExpr

repSize :: Parser DataLayoutSize
repSize = avoidInitial >> buildExpressionParser [[Infix (reservedOp "+" *> pure Add) AssocLeft]] (do
               x <- fromIntegral <$> natural
               (Bits <$ reserved "b" <*> pure x <|> Bytes <$ reserved "B" <*> pure x))

repExpr :: Parser DataLayoutExpr
repExpr = DL <$> repExpr'
  where
    repExpr' = avoidInitial >> buildExpressionParser [[Postfix (flip Offset <$ reserved "at" <*> repSize)]]
          ((Record <$ reserved "record" <*> braces (commaSep recordRepr))
      <|> (Variant <$ reserved "variant" <*> parens repExpr' <*> braces (commaSep variantRepr))
#ifdef BUILTIN_ARRAYS
      <|> (Array <$ reserved "array" <*> parens repExpr <*> getPosition)
#endif
      <|> (RepRef <$> typeConName)
      <|> (Prim <$> repSize)
      <|> (Ptr <$ reserved "pointer"))
    recordRepr = (,,) <$> variableName <*> getPosition <* reservedOp ":" <*> repExpr
    variantRepr = (,,,) <$> typeConName <*> getPosition <*> parens (fromIntegral <$> natural) <* reservedOp ":" <*> repExpr


-- TODO: add support for patterns like `_ {f1, f2}', where the record name is anonymous / zilinc
irrefutablePattern :: Parser LocIrrefPatn
irrefutablePattern = avoidInitial >> LocIrrefPatn <$> getPosition <*>
            (variableOrRecordOrArray <$> variableName <*> optionMaybe recOrArray
         <|> tuple <$> parens (commaSep irrefutablePattern)
#ifdef BUILTIN_ARRAYS
         <|> PArray <$> brackets (commaSep1 irrefutablePattern)
#endif
         <|> PUnboxedRecord <$ reservedOp "#" <*> braces recAssignsAndOrWildcard
         <|> PUnderscore <$ reservedOp "_")
       <?> "irrefutable pattern"
  where tuple [] = PUnitel
        tuple [LocIrrefPatn _ p] = p
        tuple ps  = PTuple ps

        recOrArray = do { x <- between (reservedOp "@{") (symbol "}") arrayAssigns
                        ; return $ Right x
                        }
                     <|>
                     do { x <- braces recAssignsAndOrWildcard
                        ; return $ Left x
                        }

        variableOrRecordOrArray v Nothing = PVar v
        variableOrRecordOrArray v (Just (Left  x)) = PTake v x
        variableOrRecordOrArray v (Just (Right x)) = PArrayTake v x
        recordAssignment = (\p n m -> (n, fromMaybe (LocIrrefPatn p $ PVar n) m))
                        <$> getPosition <*> variableName <*> optionMaybe (reservedOp "=" *> irrefutablePattern)
                        <?> "record assignment pattern"
        wildcard = reservedOp ".." >> return Nothing
        recAssign = Just <$> recordAssignment
        recAssignsAndOrWildcard = ((:[]) <$> wildcard)
                              <|> ((:) <$> recAssign <*> ((++) <$> many (try (comma >> recAssign))
                                                               <*> (liftM maybeToList . optionMaybe) (comma >> wildcard)))
        arrayAssigns = commaSep arrayAssignment
        arrayAssignment = do p <- getPosition
                             _ <- symbol "@"
                             idx <- expr 1
                             reservedOp "="
                             p <- irrefutablePattern
                             return (idx, p)
                          <?> "array assignment (pattern)"

pattern = avoidInitial >> LocPatn <$> getPosition <*>
            (PBoolLit <$> boolean
         <|> PCon <$> typeConName <*> many irrefutablePattern
         <|> PIntLit <$> integer
         <|> PCharLit <$> charLiteral
         <|> try (patnOfLP <$> parens pattern)
         <|> PIrrefutable <$> irrefutablePattern)
       <?> "pattern"

boolean = True <$ reserved "True"
      <|> False <$ reserved "False"
      <?> "boolean literal"

expr m = do avoidInitial
            LocExpr <$> getPosition <*>
                 (Let <$ reserved "let" <*> bindings <* reserved "in" <*> expr m
              <|> do reserved "if"
                     (do c <- sourceColumn <$> getPosition
                         guard (c > m)
                         es <- manyAligned1Until (reservedOp "|" >> multiWayIf c)
                                                 (reservedOp "|" >> reserved "else")
                                                 c
                         reservedOp "->"
                         el <- expr c
                         return $ MultiWayIf es el
                      <|>
                      (If <$> basicExpr m <*> many (reservedOp "!" >> variableName)
                          <*  reserved "then" <*> expr m <* reserved "else" <*> expr m))
              <|> Lam <$ string "\\" <*> irrefutablePattern <*> optionMaybe (reservedOp ":" *> monotype)
                      <* reservedOp "=>" <*> expr m
#ifdef BUILTIN_ARRAYS
              <|> do { reserved "map2"
                     ; f <- parens $ do { string "\\"
                                        ; p1 <- irrefutablePattern
                                        ; p2 <- irrefutablePattern
                                        ; reservedOp "=>"
                                        ; f <- expr m
                                        ; return ((p1,p2),f)
                                        }
                     ; e1 <- term
                     ; e2 <- term
                     ; return $ ArrayMap2 f (e1,e2)
                     }
#endif
                 )
     <|> matchExpr m
     <?> "expression"
  where binding = (Binding <$> irrefutablePattern <*> optionMaybe (reservedOp ":" *> monotype)
                           <*  reservedOp "=" <*> expr 1 <*> many (reservedOp "!" >> variableName))
              <|> do p <- pattern
                     mt <- optionMaybe (reservedOp ":" *> monotype)
                     reservedOp "<="
                     e <- expr 1
                     bs <- many (reservedOp "!" >> variableName)
                     c <- sourceColumn <$> getPosition
                     guard (c > m)
                     alts <- F.fold <$> optionMaybe (reservedOp "|>" >> sepByAligned1 (alternative c) (reservedOp "|>") c)
                     return $ BindingAlts p mt e bs alts
        bindings = binding `sepBy1` reserved "and"

-- A hack to handle boolean matching exhaustivity :)
matchExpr m =  flip fmap (matchExpr' m) (\case
  (LocExpr p (Match e bs [Alt (LocPatn p1 (PBoolLit True )) a e1, Alt (LocPatn p2 (PBoolLit False)) a' e2])) ->
   LocExpr p (Match e bs [Alt (LocPatn p1 (PBoolLit True )) a e1, Alt (LocPatn p2 (PIrrefutable (LocIrrefPatn p2 PUnderscore))) a' e2])
  (LocExpr p (Match e bs [Alt (LocPatn p1 (PBoolLit False)) a e1, Alt (LocPatn p2 (PBoolLit True )) a' e2])) ->
   LocExpr p (Match e bs [Alt (LocPatn p1 (PBoolLit False)) a e1, Alt (LocPatn p2 (PIrrefutable (LocIrrefPatn p2 PUnderscore))) a' e2])
  e -> e)

matchExpr' m = do
  e <- basicExpr m
  (try (do bangs <- many (reservedOp "!" >> variableName)
           c <- sourceColumn <$> getPosition
           guard (c > m)
           reservedOp "|"
           return (c,bangs))
         >>= (\(c,bangs) -> LocExpr (posOfE e) . Match e bangs <$> sepByAligned1 (alternative c) (reservedOp "|") c))
   <|> pure e
  <?> "basic expression or case distinction"

alternative m = (Alt <$> pattern <*> matchArrow <*> expr m) <?> "alternative"

multiWayIf  m = do c <- basicExpr m
                   bs <- many (reservedOp "!" >> variableName)
                   l <- matchArrow
                   e <- expr m
                   return (c, bs, l, e)

matchArrow =  Likely   <$ reservedOp "=>"
          <|> Unlikely <$ reservedOp "~>"
          <|> Regular  <$ reservedOp "->"

basicExpr m = do e <- basicExpr'
                 LocExpr (posOfE e) . Seq e <$ semi <*> expr m
                  <|> pure e
basicExpr' = avoidInitial >> buildExpressionParser
            [ [postfix ((\f e -> LocExpr (posOfE e) (Member e f)) <$ reservedOp "." <*> variableName)]
            , [ Prefix (getPosition >>= \p -> reserved "upcast" *> pure (LocExpr p . Upcast))
              , Prefix (getPosition >>= \p -> reserved "complement" *> pure (LocExpr p . PrimOp "complement" . (:[])))
              , Prefix (getPosition >>= \p -> reserved "not" *> pure (LocExpr p . PrimOp "not" . (:[])))
              , Infix funapp AssocLeft
              , Postfix ((\rs x -> LocExpr (posOfE x) (Put x rs)) <$> braces recAssignsAndOrWildcard)
#ifdef BUILTIN_ARRAYS
              , Postfix ((\rs x -> LocExpr (posOfE x) (ArrayPut x rs)) <$> between (reservedOp "@{") (symbol "}") arrayAssigns)
#endif
              ]

#ifdef BUILTIN_ARRAYS
            , [Infix (reservedOp "@" *> pure (\e i -> LocExpr (posOfE e) (ArrayIndex e i))) AssocLeft,
               Infix (reserved "o" *> pure (\f g -> LocExpr (posOfE f) (Comp f g))) AssocRight]
#else
            , [Infix (reserved "o" *> pure (\f g -> LocExpr (posOfE f) (Comp f g))) AssocRight]
#endif

            , [binary "*" AssocLeft, binary "/" AssocLeft, binary "%" AssocLeft ]
            , [binary "+" AssocLeft, binary "-" AssocLeft ]
            , map (`binary` AssocNone) [">", "<", ">=", "<=", "==", "/="]
            , [binary ".&." AssocLeft]
            , [binary ".^." AssocLeft]
            , [binary ".|." AssocLeft]
            , [binary ">>" AssocLeft, binary "<<" AssocLeft]
            , [binary "&&" AssocRight]
            , [binary "||" AssocRight]
            , [postfix ((\t e -> LocExpr (posOfE e) (Annot e t)) <$ reservedOp ":" <*> monotype)]
            , [Infix (reservedOp "$" *> pure (\a b -> LocExpr (posOfE a) (App a b True))) AssocRight]
            ] term <?> "basic expression"
  where binary name = Infix (reservedOp name *> pure (\a b -> LocExpr (posOfE a) (PrimOp name [a,b])))

        funapp = (pure (\a b -> case a of
                                  LocExpr p (Con n es) -> LocExpr p (Con n (es ++ [b]))
                                  _ -> LocExpr (posOfE a) (App a b False)))

        postfix :: Parser (LocExpr -> LocExpr) -> Operator String S Identity LocExpr
        postfix p = Postfix . chainl1 p $ return (flip (.))

term = avoidInitial >> (LocExpr <$> getPosition <*>
          (var <$> optionMaybe (reserved "inline")
               <*> variableName
               <*> optionMaybe (brackets (commaSep1 ((char '_' >> return Nothing)
                                                 <|> (Just <$> monotype))))
       <|> BoolLit <$> boolean
       <|> Con <$> typeConName <*> pure []
       <|> IntLit <$> natural
       <|> CharLit <$> charLiteral
       <|> StringLit <$> stringLiteral
       <|> tuple <$> parens (commaSep $ expr 1)
#ifdef BUILTIN_ARRAYS
       <|> ArrayLit <$> brackets (commaSep1 $ expr 1)
#endif
       <|> UnboxedRecord <$ reservedOp "#" <*> braces (commaSep1 recordAssignment)))
    <?> "term"

var Nothing  v Nothing = Var v
var (Just _) v Nothing = TypeApp v [] Inline
var Nothing  v (Just ts) = TypeApp v ts NoInline
var (Just _) v (Just ts) = TypeApp v ts Inline

tuple [] = Unitel
tuple [e] = exprOfLE e
tuple es  = Tuple es

recordAssignment = (\p n m -> (n, fromMaybe (LocExpr p (Var n)) m))
                <$> getPosition <*> variableName <*> optionMaybe (reservedOp "=" *> expr 1)
                <?> "record assignment"

wildcard = reservedOp ".." >> return Nothing

recAssign = Just <$> recordAssignment

recAssignsAndOrWildcard = ((:[]) <$> wildcard)
                      <|> ((:) <$> recAssign
                               <*> ((++) <$> many (try (comma >> recAssign))
                                         <*> (liftM maybeToList . optionMaybe) (comma >> wildcard)))

arrayAssignment = do p <- getPosition
                     _ <- symbol "@"
                     idx <- expr 1
                     reservedOp "="
                     e <- expr 1
                     return (idx, e)
                  <?> "array assignment"

arrayAssigns = commaSep arrayAssignment
                

-- monotype ::= typeA1 ("->" typeA1)?
-- typeA1   ::= Con typeA2*
--            | typeA2 (take fList | put fList)?
-- typeA2   ::= "#" atomtype
--            | atomtype "!"?
--            | atomtype "[" int-expr "]"
-- atomtype ::= "(" monotype* ")"  -- comma-separated list
--            | "{" fieldname ":" monotype "," ... "}"
--            | "<" Con typeA2 "|" ... ">"
--            | var
--            | Con

-- NOTE: use "string" instead of "reservedOp" so that it allows no spaces after "@" / zilinc
docHunk = do whiteSpace; _ <- try (string "@"); x <- manyTill anyChar newline; whiteSpace; return x

monotype = do avoidInitial
              t1 <- typeA1
              t2 <- optionMaybe (reservedOp "->" >> typeA1)
              case t2 of
                Nothing -> return t1
                Just t2' -> return $ LocType (posOfT t1) $ TFun t1 t2'
  where
    typeA1 = do
      x <- typeA1'
      t2 <- optionMaybe (avoidInitial >> docHunk)
      case t2 of Nothing -> return x; Just doc -> do
                    return (Documentation doc x)
    typeA2 = do
      x <- typeA2'
      t2 <- optionMaybe (avoidInitial >> docHunk)
      case t2 of Nothing -> return x; Just doc -> do
                    return (Documentation doc x)
    typeA1' = do avoidInitial
                 try paramtype
                 <|> (do t <- typeA2'
                         op <- optionMaybe takeput
                         let t' = (case op of
                                      Nothing -> t
                                      Just f  -> f t)
                         aop <- optionMaybe arrTakeput
                         let ta = (case aop of
                                     Nothing -> t'
                                     Just f  -> f t')
                         l <- optionMaybe layout
                         let t'' = (case l of
                                      Nothing -> ta
                                      Just fl -> fl ta)
                         return t''
                     )
    typeA2' = avoidInitial >>
               ((unbox >>= \op -> atomtype >>= \at -> return (op at))
#ifdef BUILTIN_ARRAYS
           <|>  try ( do { t <- atomtype
                         ; mu <- optionMaybe unbox
                         ; l <- brackets $ expr 1
                         ; mb <- optionMaybe bang
                         ; let fu = case mu of Nothing -> id; Just u -> u
                               fb = case mb of Nothing -> id; Just b -> b
                         ; return . fb . fu $ (LocType (posOfT t) $ TArray t l (Boxed False Nothing) [])
                         } )
#endif
           <|>  (atomtype >>= \t -> optionMaybe bang >>= \op -> case op of Nothing -> return t; Just f -> return (f t)))

    paramtype = avoidInitial >> LocType <$> getPosition <*>
      -- If the type `typeConName` refers to an abstract type, its sigil should be `Boxed`
      -- and should have no associated layout.
      -- If the type `typeConName` is a type alias, the sigil we choose here is ignored
      -- because the actual sigil comes from the aliased type. /mdimeglio
      (TCon <$> typeConName <*> many1 typeA2 <*> pure (Boxed False Nothing))

    unbox = avoidInitial >> reservedOp "#" >> return (\x -> LocType (posOfT x) (TUnbox x))
    bang  = avoidInitial >> reservedOp "!" >> return (\x -> LocType (posOfT x) (TBang x))
    takeput = avoidInitial >>
             ((reservedOp "take" >> fList >>= \fs -> return (\x -> LocType (posOfT x) (TTake fs x)))
          <|> (reservedOp "put"  >> fList >>= \fs -> return (\x -> LocType (posOfT x) (TPut  fs x))))
    -- vvv TODO: add the @take(..) syntax for taking all elements / zilinc
    arrTakeput = avoidInitial >>
              ((reservedOp "@take" >> parens (commaSep (expr 1)) >>= \idxs -> return (\x -> LocType (posOfT x) (TATake idxs x))) 
           <|> (reservedOp "@put"  >> parens (commaSep (expr 1)) >>= \idxs -> return (\x -> LocType (posOfT x) (TAPut  idxs x))))
    -- either we have an actual layout, or the name of a layout synonym
    layout = avoidInitial >> reservedOp "layout" >> repExpr
      >>= \l -> return (\x -> LocType (posOfT x) (TLayout l x))

    atomtype = avoidInitial >> LocType <$> getPosition <*> (
          TVar <$> variableName <*> pure False
      <|> (do tn <- typeConName
              let s = if tn `elem` primTypeCons  -- give correct sigil to primitive types
                        then Unboxed
                       -- If the type `typeConName` refers to an abstract type, its sigil should be `Boxed`
                       -- and should have no associated layout.
                       -- If the type `typeConName` is a type alias, the sigil we choose here is ignored
                       -- because the actual sigil comes from the aliased type. /mdimeglio
                        else Boxed False Nothing
              return $ TCon tn [] s)
      -- <|> TCon <$> typeConName <*> pure [] <*> pure Writable
      <|> tuple <$> parens (commaSep monotype)
      <|> (\fs -> TRecord fs (Boxed False Nothing))
          <$> braces (commaSep1 ((\a b c -> (a,(b,c))) <$> variableName <* reservedOp ":" <*> monotype <*> pure False))
      <|> TVariant . M.fromList <$> angles (((,) <$> typeConName <*> fmap ((,False)) (many typeA2)) `sepBy` reservedOp "|"))

    tuple [] = TUnit
    tuple [e] = typeOfLT e
    tuple es  = TTuple es

    fList = (Just . (:[])) <$> identifier
        <|> parens ((reservedOp ".." >> return Nothing) <|> (commaSep identifier >>= return . Just))

polytype = PT <$ reserved "all" <*> (((:[]) <$> kindSignature) <|> parens (commaSep1 kindSignature)) <* reservedOp "." <*> monotype
       <|> PT [] <$> monotype

kindSignature = do n <- variableName
                   (n,) <$> (reservedOp ":<" *> (kind <?> "kind")
                          <|> pure (K False False False))
  where kind = do x <- identifier
                  determineKind x (K False False False)
        determineKind ('D':xs) k =  determineKind xs (k { canDiscard = True })
        determineKind ('S':xs) k =  determineKind xs (k { canShare = True })
        determineKind ('E':xs) k =  determineKind xs (k { canEscape = True })
        determineKind [] k = return k
        determineKind _ k = fail "Kinds are made of three letters: D, S, E"

-- NOTE: use "string" instead of "reservedOp" so that it allows no spaces after "@@" / zilinc
docBlock = do whiteSpace; _ <- try (string "@@"); x <- manyTill anyChar newline; whiteSpace; return x

toplevel = getPosition >>= \p ->
                 (p, "",) <$> DocBlock <$> unlines <$> many1 docBlock
             <|> toplevel'

toplevel' = do
  docs <- unlines . fromMaybe [] <$> optionMaybe (many1 docHunk)
  p <- getPosition
  when (sourceColumn p > 1) $ fail "toplevel entries should start at column 1"
  (p,docs,) <$> (try (Include <$ reserved "include" <*> stringLiteral)
        <|> IncludeStd <$ reserved "include" <*> angles (many (noneOf "\r\n>"))
        <|> RepDef <$ reserved "layout" <*> repDecl
        <|> typeDec <$ reserved "type" <*> typeConName <*> many (avoidInitial >> variableName) <*>
              ((Left <$> (reservedOp "=" *> monotype)) <|> (Right <$> option [] (reservedOp "-:" *> commaSep monotype)))
        <|> do n <- variableName
               reservedOp ":"
               tau <- polytype
               do try (do n' <- variableName
                          when (n /= n') $ fail $ "The name in the type signature, `" ++ n
                                               ++ "` does not match the name in the equation, `" ++ n' ++ "`." )
                  let fundef = FunDef n tau <$> (functionAlts <|> (:[]) <$> functionSingle)
                  case tau of
                    PT [] t -> (ConstDef n t <$ reservedOp "=" <*> expr 1 <|> fundef)
                    _       -> fundef
                <|> pure (AbsDec n tau))
  where
    typeDec n vs (Left  t ) = TypeDec n vs t
    typeDec n vs (Right ts) = AbsTypeDec n vs ts
    functionAlts = do
      c <- sourceColumn <$> getPosition
      reservedOp "|"
      sepByAligned1 (alternative c) (reservedOp "|") c
    functionSingle = Alt <$> (LocPatn <$> getPosition <*> (PIrrefutable <$> irrefutablePattern))
                         <*> pure Regular <* reservedOp "=" <*> expr 1

program :: Parser [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)]
program = whiteSpace *> many1 toplevel <* eof

-- NOTE: It will search for the path provided in the files. If it cannot find anything, it will
--   check for directories given in the -I arguments, relative to the current working dir.
--   A path (B) in an include clauses is relative to the file (A) containing the include.
--   When searching with -I, it looks for B in A/I/B. If I is absolute, it ignores A.
-- Example:
--   current dir: C
--   file a in dir: A, relative to C
--   file b included in file a, in dir B, relative to A
--   -I argument: S
--   * It searches for file a in A, from C
--     case 1) a found. Then it searches for file b in A/B, from C
--       case 1-1) b found. DONE
--       case 1-2) b not found. It then attempts A/S/B, from C
--     case 2) a not found. It tries S/A, from C, and finds a. Next
--             it searches for file b in A/B, from C
--       case 2-1) b found. DONE
--       case 2-2) b not found. It attempts A/S/B from C
--   We can conclude that the search path for b is independent of where a was found

parseWithIncludes :: FilePath -> [FilePath]
                  -> IO (Either String ([(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)], [PP.LocPragma]))
parseWithIncludes f paths = do
  r <- newIORef S.empty
  loadTransitive' r f paths "."  -- relative to orig, we're in orig

-- r: IORef
-- fp: file path declared in the include clause, or the given path in command-line (only for the initial one)
-- paths: search paths, relative to origin
-- ro: the path of the current file, relative to original dir
loadTransitive' :: IORef (S.Set FilePath) -> FilePath -> [FilePath] -> FilePath
                -> IO (Either String ([(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)], [PP.LocPragma]))
loadTransitive' r fp paths ro = do
  let fps = map (flip combine fp) (ro:paths)  -- all file paths need to search
      fpdir = takeDirectory (combine ro fp)
  findPath fps >>= \case
    Nothing  -> return $ Left $ "File " ++ fp ++ " cannot be found"
    Just fp' -> canonicalizePath fp' >>= \fpc -> (S.member fpc <$> readIORef r) >>= \case
      True  -> return $ Right ([],[])
      False -> do modifyIORef r (S.insert fpc)
                  PP.preprocess fp' >>= \case
                    Left err -> return $ Left $ "Preprocessor failed: " ++ err
                    Right (cpped,pragmas) -> do
                      case runIdentity $ runParserT program (ParserState True) fp' cpped of
                        Left err -> return $ Left $ "Parser failed: " ++ show err
                        Right defs -> do
                           defs' <- mapM (flip transitive fpdir) defs
                           return $ fmap (second (pragmas ++) . mconcat) . sequence $ defs'
  where
    transitive :: (SourcePos, DocString, TopLevel LocType LocPatn LocExpr)
               -> FilePath
               -> IO (Either String ([(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)], [PP.LocPragma]))
    transitive (p,d,Include x) curr = loadTransitive' r x (map (combine curr) paths) curr
    transitive (p,d,IncludeStd x) curr = do filepath <- (getStdIncFullPath x); loadTransitive' r filepath (map (combine curr) paths) curr
    transitive x _ = return (Right ([x],[]))

    findPath :: [FilePath] -> IO (Maybe FilePath)
    findPath [] = return Nothing
    findPath (p:paths) = doesFileExist p >>= \case
      False -> findPath paths
      True  -> return $ Just p

-- ----------------------------------------------------------------------------
-- custTyGen

parseCustTyGen :: FilePath -> IO (Either String [(LocType, String)])
parseCustTyGen = return . left show <=< parseFromFile tygenfile

tygenfile = whiteSpace *> many tygen <* eof

tygen = do
  p <- getPosition
  when (sourceColumn p > 1) $ fail "Customised type generation info should start at column 1"
  cty <- identifier  -- FIXME: not quite the character set for C identifiers / zilinc
  string "<=="
  ty <- monotype  -- NOTE: this syntax is because of the `avoidInitial`s in `monotype` function / zilinc
  return (ty,cty)

parseFromFile :: Parser a -> FilePath -> IO (Either ParseError a)
parseFromFile p fname = do
  input <- readFile fname
  return $ runP p (ParserState True) (if __cogent_ffull_src_path then fname else takeFileName fname) input

-- -------
-- cpp line directives
-- process cpp line directives in whitespace and after every token.

cppLineTokenParser :: Stream s m Char => T.GenTokenParser s u m -> T.GenTokenParser s u m
cppLineTokenParser tp
    = T.TokenParser { identifier = cppLineAfter $ T.identifier tp
                    , reserved = cppLineAfter . T.reserved tp
                    , operator = cppLineAfter $ T.operator tp
                    , reservedOp = cppLineAfter . T.reservedOp tp

                    , charLiteral = cppLineAfter $ T.charLiteral tp
                    , stringLiteral = cppLineAfter $ T.stringLiteral tp
                    , natural = cppLineAfter $ T.natural tp
                    , integer = cppLineAfter $ T.integer tp
                    , float = cppLineAfter $ T.float tp
                    , naturalOrFloat = cppLineAfter $ T.naturalOrFloat tp
                    , decimal = cppLineAfter $ T.decimal tp
                    , hexadecimal = cppLineAfter $ T.hexadecimal tp
                    , octal = cppLineAfter $ T.octal tp

                    , symbol = cppLineAfter . T.symbol tp
                    , lexeme = cppLineAfter . T.lexeme tp
                    , whiteSpace = cppLineAfter $ T.whiteSpace tp

                    , parens = cppLineAfter . T.parens tp
                    , braces = cppLineAfter . T.braces tp
                    , angles = cppLineAfter . T.angles tp
                    , brackets = cppLineAfter . T.brackets tp
                    , squares = cppLineAfter . T.brackets tp
                    , semi = cppLineAfter $ T.semi tp
                    , comma = cppLineAfter $ T.comma tp
                    , colon = cppLineAfter $ T.colon tp
                    , dot = cppLineAfter $ T.dot tp
                    , semiSep = cppLineAfter . T.semiSep tp
                    , semiSep1 = cppLineAfter . T.semiSep1 tp
                    , commaSep = cppLineAfter . T.commaSep tp
                    , commaSep1 = cppLineAfter . T.commaSep1 tp
                    }
    where
        cppLineAfter p = do{ x <- p; skipMany cppLine; return x  }
        cppLine = do
            pos <- getPosition
            guard (sourceColumn pos == 1)
            (T.symbol tp) "#line"
            ln <- T.integer tp
            fn <- T.stringLiteral tp
            pos2 <- getPosition
            setPosition $ setSourceLine (setSourceName pos2 fn)  (sourceLine pos2 - sourceLine pos - 1 + fromInteger ln)
