{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module HieDebug where

import GhcPrelude

import Data.Function (on)
import Data.List (sortOn)
import Data.Foldable

import HieTypes
import HieBin
import HieUtils

import SrcLoc
import Module
import FastString
import Outputable

import qualified Data.Map as M
import qualified Data.Set as S

ppHies :: Outputable a => (HieASTs a) -> SDoc
ppHies (HieASTs asts) = M.foldrWithKey go "" asts
  where
    go k a rest = vcat $
      [ "File: " <> ppr k
      , ppHie a
      , rest
      ]

ppHie :: Outputable a => HieAST a -> SDoc
ppHie = go 0
  where
    go n (Node inf sp children) = hang header n rest
      where
        rest = vcat $ map (go (n+2)) children
        header = hsep
          [ "Node"
          , ppr sp
          , ppInfo inf
          ]
ppInfo :: Outputable a => NodeInfo a -> SDoc
ppInfo ni = hsep
  [ ppr $ toList $ nodeAnnotations ni
  , ppr $ nodeType ni
  , ppr $ M.toList $ nodeIdentifiers ni
  ]

type Diff a = a -> a -> [SDoc]

diffFile :: Diff HieFile
diffFile = diffAsts eqDiff `on` (getAsts . hieAST)

diffAsts :: (Outputable a, Eq a) => Diff a -> Diff (M.Map FastString (HieAST a))
diffAsts f = diffList (diffAst f) `on` M.elems

diffAst :: (Outputable a, Eq a) => Diff a -> Diff (HieAST a)
diffAst diffType (Node info1 span1 xs1) (Node info2 span2 xs2) =
    infoDiff ++ spanDiff ++ diffList (diffAst diffType) xs1 xs2
  where
    spanDiff
      | span1 /= span2 = [hsep ["Spans", ppr span1, "and", ppr span2, "differ"]]
      | otherwise = []
    infoDiff = (diffList eqDiff `on` (S.toAscList . nodeAnnotations)) info1 info2
            ++ (diffList diffType `on` nodeType) info1 info2
            ++ (diffIdents `on` nodeIdentifiers) info1 info2
    diffIdents a b = (diffList diffIdent `on` normalizeIdents) a b
    diffIdent (a,b) (c,d) = diffName a c
                         ++ eqDiff b d
    diffName (Right a) (Right b) = case (a,b) of
      (ExternalName mod occ _, ExternalName mod' occ' _) -> eqDiff (mod,occ) (mod',occ')
      (LocalName occ _, ExternalName _ occ' _) -> eqDiff occ occ'
      _ -> eqDiff a b
    diffName a b = eqDiff a b

type DiffIdent = Either ModuleName HieName

normalizeIdents :: NodeIdentifiers a -> [(DiffIdent,IdentifierDetails a)]
normalizeIdents = sortOn fst . map (first toHieName) . M.toList
  where
    first f (a,b) = (fmap f a, b)

diffList :: Diff a -> Diff [a]
diffList f xs ys
  | length xs == length ys = concat $ zipWith f xs ys
  | otherwise = ["length of lists doesn't match"]

eqDiff :: (Outputable a, Eq a) => Diff a
eqDiff a b
  | a == b = []
  | otherwise = [hsep [ppr a, "and", ppr b, "do not match"]]

validAst :: HieAST a -> Either SDoc ()
validAst (Node _ span children) = do
  checkContainment children
  checkSorted children
  forM_ children validAst
  where
    checkSorted [] = return ()
    checkSorted [_] = return ()
    checkSorted (x:y:xs)
      | nodeSpan x `leftOf` nodeSpan y = checkSorted (y:xs)
      | otherwise = Left $ hsep
          [ ppr $ nodeSpan x
          , "is not to the left of"
          , ppr $ nodeSpan y
          ]
    checkContainment [] = return ()
    checkContainment (x:xs)
      | span `containsSpan` (nodeSpan x) = checkContainment xs
      | otherwise = Left $ hsep
          [ ppr $ span
          , "does not contain"
          , ppr $ nodeSpan x
          ]

validateScopes :: M.Map FastString (HieAST a) -> [SDoc]
validateScopes asts = M.foldrWithKey (\k a b -> valid k a ++ b) [] refMap
  where
    refMap = generateReferencesMap asts
    valid (Left _) _ = []
    valid (Right n) refs = concatMap inScope refs
      where
        scopes =  case foldMap (foldMap getScopeFromContext . identInfo . snd) refs of
          Just xs -> xs
          Nothing -> []
        inScope (sp, dets)
          |  definedInAsts asts n
          && any isOccurrence (identInfo dets)
            = case scopes of
              [] -> []
              _ -> if any (`scopeContainsSpan` sp) scopes
                   then []
                   else return $ hsep $
                     [ "Name", ppr n, "at position", ppr sp
                     , "doesn't occur in calculated scope", ppr scopes]
          | otherwise = []

instance Outputable a => Outputable (IdentifierDetails a) where
  ppr x = text "IdentifierDetails" <+> ppr (identType x) <+> ppr (identInfo x)

instance Outputable HieName where
  ppr (ExternalName m n sp) = text "ExternalName" <+> ppr m <+> ppr n <+> ppr sp
  ppr (LocalName n sp) = text "LocalName" <+> ppr n <+> ppr sp
  ppr (KnownKeyName u) = text "KnownKeyName" <+> ppr u

instance Outputable Scope where
  ppr NoScope = text "NoScope"
  ppr (LocalScope sp) = text "LocalScope" <+> ppr sp
  ppr ModuleScope = text "ModuleScope"

instance Outputable ContextInfo where
  ppr = text . show
