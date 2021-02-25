module ImpPrettyPrint
        ( prettyprint
        , prettyprintAExp
        , prettyprintBExp
        )
where

import Assertion ( Assertion
                 , Arith )
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc.Render.String
import Data.Text ( Text )
import Imp

prettyprint :: Stmt -> Text
prettyprint = renderStrict . layoutPretty defaultLayoutOptions . prettyStmt

prettyprintAExp :: AExp -> String
prettyprintAExp = renderString . layoutPretty defaultLayoutOptions . prettyAExp

prettyprintBExp :: BExp -> String
prettyprintBExp = renderString . layoutPretty defaultLayoutOptions . prettyBExp

prettyStmt :: Stmt -> Doc ()
prettyStmt SSkip       = pretty "skip" <> semi
prettyStmt (SAsgn v a) = pretty v <+> pretty ":=" <+> prettyAExp a <> semi
prettyStmt (SSeq ss  ) = vsep (map prettyStmt ss)
prettyStmt (SIf c t e) = vsep
        [ pretty "if" <+> prettyBExp c <+> pretty "then"
        , indent 2 (prettyStmt t)
        , pretty "else"
        , indent 2 (prettyStmt e)
        , pretty "end"
        ]
prettyStmt (SWhile c b (i, v, _)) = vsep
        [ pretty "while" <+> prettyBExp c <+> pretty "do"
        , indent 2 $ vsep
                [ pretty "@inv" <+> braces (prettyAssertion i)
                , pretty "@var" <+> braces (prettyArith v)
                , prettyStmt b
                ]
        , pretty "end"
        ]
prettyStmt (SCall ls rs n) =
        hsep (punctuate comma (map pretty ls))
                <+> pretty ":="
                <+> pretty "call"
                <+> pretty n
                <>  tupled (map pretty rs)

parenPrec :: Int -> Int -> Doc () -> Doc ()
parenPrec oPrec iPrec doc = if oPrec <= iPrec then doc else parens doc

-- inspired by
-- https://hackage.haskell.org/package/language-c-0.8.3/docs/src/Language.C.Pretty.html#line-403
prettyAExp :: AExp -> Doc ()
prettyAExp = go 0
    where
        go :: Int -> AExp -> Doc ()
        go _ (ALit i  ) = pretty i
        go _ (AVar v  ) = pretty v
        go p (AAdd l r) = parenPrec p 1 $ go 1 l <+> pretty "+" <+> go 2 r
        go p (ASub l r) = parenPrec p 1 $ go 1 l <+> pretty "-" <+> go 2 r
        go p (AMul l r) = parenPrec p 2 $ go 2 l <+> pretty "*" <+> go 3 r
        go p (ADiv l r) = parenPrec p 2 $ go 2 l <+> pretty "/" <+> go 3 r
        go p (AMod l r) = parenPrec p 2 $ go 2 l <+> pretty "%" <+> go 3 r
        go p (APow l r) = parenPrec p 2 $ go 2 l <+> pretty "^" <+> go 3 r

prettyBExp :: BExp -> Doc ()
prettyBExp = go 0
    where
        go :: Int -> BExp -> Doc ()
        go _ BTrue      = pretty "true"
        go _ BFalse     = pretty "false"
        go p (BNot b  ) = parenPrec p 2 $ pretty '!' <> go 2 b
        go p (BAnd l r) = parenPrec p 1 $ go 1 l <+> pretty "&&" <+> go 2 r
        go p (BOr  l r) = parenPrec p 1 $ go 1 l <+> pretty "||" <+> go 2 r
        go _ (BEq  l r) = prettyAExp l <+> pretty "==" <+> prettyAExp r
        go _ (BNe  l r) = prettyAExp l <+> pretty "!=" <+> prettyAExp r
        go _ (BLe  l r) = prettyAExp l <+> pretty "<=" <+> prettyAExp r
        go _ (BGe  l r) = prettyAExp l <+> pretty ">=" <+> prettyAExp r
        go _ (BLt  l r) = prettyAExp l <+> pretty "<" <+> prettyAExp r
        go _ (BGt  l r) = prettyAExp l <+> pretty ">" <+> prettyAExp r

prettyAssertion :: Assertion -> Doc ()
prettyAssertion assertion = pretty $ show assertion

prettyArith :: Arith -> Doc ()
prettyArith arith = pretty $ show arith
