module Main where

import Prelude
import Data.Nullable as N
import Data.Maybe (Maybe(..))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (log, CONSOLE)

import React as R
import React.DOM as R
import React.DOM.Props as P
import ReactDOM as RDOM
import DOM as DOM
import DOM.HTML as DOM
import DOM.HTML.Types as DOM
import DOM.HTML.Window as DOM
import DOM.Node.ParentNode as DOM

counter = R.createClass (R.spec' mkS render)
  where
    mkS _ = pure 0
    render this = do
      i <- R.readState this
      let incr unit = R.writeState this (i + 1)
      pure $
        R.div' [ R.div' [R.text $ "value = " ++ show i]
               , R.button [P.onClick incr] [R.text "Incr"]
               ]

component = R.createFactory counter

main = void do
  document <- DOM.window >>= DOM.document
  let
    getMountPoint = DOM.querySelector "#mount-point"
    docAsParent = DOM.htmlDocumentToParentNode document
  Just mountPoint <- N.toMaybe <$> getMountPoint docAsParent
  RDOM.render (component {}) mountPoint
  log "Hello from PureScript!"
