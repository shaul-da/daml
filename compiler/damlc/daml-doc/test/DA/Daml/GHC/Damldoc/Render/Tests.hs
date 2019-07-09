-- Copyright (c) 2019 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
-- SPDX-License-Identifier: Apache-2.0

{-# LANGUAGE OverloadedStrings #-}

module DA.Daml.Doc.Render.Tests(mkTestTree)
  where

import           DA.Daml.Doc.Types
import           DA.Daml.Doc.Render

import           Control.Monad.Except
import qualified Data.Text as T
import qualified Data.Text.IO as T

import qualified Test.Tasty.Extended as Tasty
import           Test.Tasty.HUnit



mkTestTree :: IO Tasty.TestTree
mkTestTree = do
  pure $ Tasty.testGroup "DA.Daml.Doc.Render"
    [ Tasty.testGroup "RST Rendering" $
      zipWith (renderTest Rst) cases expectRst
    , Tasty.testGroup "Markdown Rendering" $
      zipWith (renderTest Markdown) cases expectMarkdown
    ]


cases :: [(String, ModuleDoc)]
cases = [ ("Empty module",
           ModuleDoc "Empty" Nothing [] [] [] [])
        , ("Type def with argument",
           ModuleDoc "Typedef" Nothing []
            [TypeSynDoc "T" (Just "T descr") ["a"] (TypeApp Nothing "TT" [TypeApp Nothing "TTT" []])]
            [] []
          )
        , ("Two types",
           ModuleDoc "TwoTypes" Nothing []
            [ TypeSynDoc "T" (Just "T descr") ["a"] (TypeApp Nothing "TT" [])
            , ADTDoc "D" Nothing ["d"] [PrefixC "D" (Just "D descr") [TypeApp Nothing "a" []]]
            ]
            [] []
          )
        , ("Documented function with type",
           ModuleDoc "Function1" Nothing [] []
            [FunctionDoc "f" Nothing (Just $ TypeApp Nothing "TheType" []) (Just "the doc")] []
          )
        , ("Documented function without type",
           ModuleDoc "Function2" Nothing [] []
            [FunctionDoc "f" Nothing Nothing (Just "the doc")] []
          )
        , ("Undocumented function with type",
           ModuleDoc "Function3" Nothing [] []
            [FunctionDoc "f" Nothing (Just $ TypeApp Nothing "TheType" []) Nothing] []
          )
        -- The doc extraction won't generate functions without type nor description
        , ("Module with only a type class",
           ModuleDoc "OnlyClass" Nothing [] [] []
            [ClassDoc "C" Nothing Nothing ["a"] [FunctionDoc "member" Nothing (Just (TypeApp Nothing "a" [])) Nothing]])
        , ("Multiline field description",
           ModuleDoc
             "MultiLineField"
             Nothing
             []
             [ADTDoc
                "D"
                Nothing
                []
                [RecordC "D" Nothing [FieldDoc "f" (TypeApp Nothing "T" []) (Just "This is a multiline\nfield description")]]]
             []
             []
          )
        ]

expectRst :: [T.Text]
expectRst =
        [ T.empty
        , mkExpectRst "module-typedef-50108" "Typedef" "" [] []
            ["\n.. _type-typedef-t-88479:\n\ntype **T a**\n    = TT TTT\n\n  T descr"] []
        , mkExpectRst "module-twotypes-33303" "TwoTypes" "" []
            []
            ["\n.. _type-twotypes-t-17090:\n\ntype **T a**\n    = TT\n\n  T descr"
            , "\n.. _data-twotypes-d-66754:\n\ndata **D d**\n\n  \n  \n  .. _constr-twotypes-d-45919:\n  \n  **D** a\n  \n  D descr"]
            []
        , mkExpectRst "module-function1-29590" "Function1" "" [] [] [] [ "\n.. _function-function1-f-45407:\n\n**f**\n  : TheType\n\n  the doc\n"]
        , mkExpectRst "module-function2-7227" "Function2" "" [] [] [] [ "\n.. _function-function2-f-87524:\n\n**f**\n  :   the doc\n"]
        , mkExpectRst "module-function3-84844" "Function3" "" [] [] [] [ "\n.. _function-function3-f-32653:\n\n**f**\n  : TheType\n\n"]
        , mkExpectRst "module-onlyclass-88463" "OnlyClass" ""
            []
            [ "\n.. _class-onlyclass-c-63566:"
            , "**class C a where**\n  \n  .. _function-onlyclass-member-45125:\n  \n  **member**\n    : a"
            ]
            []
            []
        , mkExpectRst "module-multilinefield-24755" "MultiLineField" ""
            []
            []
            [ "\n.. _data-multilinefield-d-47142:"
            , "data **D**"
            , T.concat
                  [ "  \n  \n"
                  , "  .. _constr-multilinefield-d-61939:\n  \n"
                  , "  **D**\n  \n  \n"
                  , "  .. list-table::\n"
                  , "     :widths: 15 10 30\n"
                  , "     :header-rows: 1\n  \n"
                  , "     * - Field\n"
                  , "       - Type\n"
                  , "       - Description\n"
                  , "     * - f\n"
                  , "       - T\n"
                  , "       - This is a multiline field description"
                  ]
            ]
            []
        ]
        <> repeat (error "Missing expectation (Rst)")

mkExpectRst :: T.Text -> T.Text -> T.Text -> [T.Text] -> [T.Text] -> [T.Text] -> [T.Text] -> T.Text
mkExpectRst anchor name descr templates classes adts fcts = T.unlines $
  [ ".. _" <> anchor <> ":"
  , ""
  , "Module " <> name
  , "-------" <> T.replicate (T.length name) "-"
  , descr, ""
  ]
  <> concat
     [ if null templates then [] else
         [ "Templates"
         , "^^^^^^^^^"
         , T.unlines templates
         , ""]
     , if null classes then [] else
         [ "Typeclasses"
         , "^^^^^^^^^^^"
         , T.unlines (map (<> "\n") classes)
         ]
     , if null adts then [] else
         [ "Data types"
         , "^^^^^^^^^^"
         , T.unlines (map (<> "\n") adts)
         ]
     , if null fcts then [] else
         [ "Functions"
         , "^^^^^^^^^"
         , T.unlines (map (<> "\n") fcts)
         ]
     ]
  -- NB T.unlines adds a trailing '\n'


expectMarkdown :: [T.Text]
expectMarkdown =
        [ T.empty
        , mkExpectMD "Typedef" "" [] [] ["### `type` `T a`\n    = `TT` `TTT`\n\n  T descr\n"] []
        , mkExpectMD "TwoTypes" "" [] []
            ["### `type` `T a`\n    = `TT`\n\n  T descr\n"
            , "### `data` `D d`\n\n* `D` `a`\n  D descr\n"]
            []
        , mkExpectMD "Function1" "" [] [] [] [ "* `f` : `TheType`  \n  the doc\n"]
        , mkExpectMD "Function2" "" [] [] [] [ "* `f`  \n  the doc\n"]
        , mkExpectMD "Function3" "" [] [] [] [ "* `f` : `TheType`\n"]
        , mkExpectMD "OnlyClass" ""
            []
            [ "### `class` C a where"
            , ""
            , "  * `member` : `a`"
            ]
            []
            []
        , mkExpectMD "MultiLineField" ""
            []
            []
            [ "### `data` `D`"
            , ""
            , "* `D`"
            , ""
            , "  | Field | Type/Description |"
            , "  | :---- | :----------------"
            , "  | `f`   | `T` |"
            , "  |       | This is a multiline field description |" ]
            []
        ]
        <> repeat (error "Missing expectation (Markdown)")

mkExpectMD :: T.Text -> T.Text -> [T.Text] -> [T.Text] -> [T.Text] -> [T.Text] -> T.Text
mkExpectMD name descr templates classes adts fcts
  | null templates && null classes && null adts && null fcts && T.null descr = T.empty
  | otherwise = T.unlines $
  [ "# Module " <> name
  , "", descr, ""
  ]
  <> concat
  [ if null templates then [] else
      [ "## Templates"
      , "", T.unlines templates
      , ""]
  , if null classes then [] else
      [ "## Typeclasses"
      , "", T.unlines classes
      , ""]
  , if null adts then [] else
      [ "## Data types"
      , "", T.unlines adts
      , ""]
  , if null fcts then [] else
      [ "## Functions"
      , "", T.unlines fcts
      , ""]
  ]

renderTest :: DocFormat -> (String, ModuleDoc) -> T.Text -> Tasty.TestTree
renderTest format (name, input) expected =
  testCase name $ do
  let
    renderer = case format of
                 Json -> error "Json encoder testing not done here"
                 Rst -> renderSimpleRst
                 Markdown -> renderSimpleMD
                 Html -> error "HTML testing not supported (use Markdown)"
                 Hoogle -> error "Hoogle doc testing not yet supported."
    output = T.strip $ renderer input
    expect = T.strip expected

  unless (output == expect) $ do
    T.putStrLn $ T.unlines
      [ "Output differs from expectation:"
      , "Expected:"
      , T.pack $ show expect
      , "Actual:"
      , T.pack $ show output ]

    let diffs = [  "`" <> e <> "' /= `" <> o <> "'"
                | (e, o) <- zip (T.lines expect) (T.lines output), e /= o ]

    putStrLn $ show (length diffs) <> " different lines"
    mapM_ T.putStrLn diffs

    assertFailure "Output differs from expectation."
