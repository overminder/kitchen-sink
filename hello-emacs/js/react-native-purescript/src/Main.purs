module Main where

import Prelude
import Control.Monad.Eff (runPure, Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Data.Maybe (Maybe(Nothing, Just))
import RN (touchableOpacity, createStyleSheet, baseStyle, addStyle, view, registerComponent, text)
import React (writeState, readState, createClass, createClassStateless, spec, createFactory, spec')
import Unsafe.Coerce (unsafeCoerce)

counter = createClass $ spec 0 render
  where
    render thiz = do
      i <- readState thiz
      let
        mkOnPress ps = ps {
          onPress = unsafeCoerce $ writeState thiz (i + 1)
          }
      pure $ view [baseStyle viewStyle]
        [touchableOpacity [mkOnPress] $
         [text [baseStyle textStyle] $ "Hello " ++ show i]]

textStyle = createStyleSheet "text" {
  color: "green"
  }

viewStyle = createStyleSheet "view" {
  flex: 1,
  alignItems: "center",
  justifyContent: "center"
  }

main = do
  registerComponent "TFLandingPage" counter
