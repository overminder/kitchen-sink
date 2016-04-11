module RN where

import React.DOM as RD
import Control.Monad.Eff (runPure, Eff)
import Data.Array (cons)
import Data.Default (class Default)
import Data.Foldable (foldl)
import Data.Function (runFn2, Fn2)
import Data.Generic (toSpine)
import Data.Maybe (Maybe(Nothing))
import Prelude (id, Unit, (>>>))
import React (EventHandlerContext, createElement, ReactElement, ReactClass)
import React.DOM.Props (unsafeMkProps, unsafeFromPropsArray, Props)
import Unsafe.Coerce (unsafeCoerce)

foreign import registerComponentF
  :: forall e ps. Fn2 String (ReactClass ps) (Eff e Unit)

foreign import createStyleSheetF
  :: forall e s. Fn2 String s (Eff e StyleSheet)

foreign import data StyleSheet :: *

foreign import viewClass
  :: ReactClass ViewProps

foreign import textClass
  :: ReactClass TextProps

foreign import touchableOpacityClass
  :: ReactClass TouchableOpacityProps

registerComponent name klass = runFn2 registerComponentF name klass

createStyleSheet name value = runPure (runFn2 createStyleSheetF name value)

type LayoutRectangle = {
  x :: Number,
  y :: Number,
  width :: Number,
  height :: Number
  }

type LayoutChangeEvent = {
  nativeEvent :: {
     layout :: LayoutRectangle
     }
  }

type TextProps = {
  allowFontScaling :: Boolean,
  onLayout :: LayoutChangeEvent -> Unit,
  numberOfLines :: Int,
  testID :: String,
  onPress :: Unit -> Unit,  -- Use EventHandlerContext?
  style :: Array TextStyle,
  suppressHighlighting :: Boolean
  }

type FlexStyle a = {
  alignItems :: String,  --enum('flex-start', 'flex-end', 'center', 'stretch'),
  alignSelf :: String, -- enum('auto', 'flex-start', 'flex-end', 'center', 'stretch'),
  borderBottomWidth :: Number,
  borderLeftWidth :: Number,
  borderRightWidth :: Number,
  borderTopWidth :: Number,
  borderWidth :: Number,
  bottom :: Number,
  flex :: Number,
  flexDirection :: String, -- enum('row', 'column')
  flexWrap :: String, -- enum('wrap', 'nowrap')
  height :: Number,
  justifyContent :: String, -- enum('flex-start', 'flex-end', 'center', 'space-between', 'space-around')
  left :: Number,
  margin :: Number,
  marginBottom :: Number,
  marginHorizontal :: Number,
  marginLeft :: Number,
  marginRight :: Number,
  marginTop :: Number,
  marginVertical :: Number,
  padding :: Number,
  paddingBottom :: Number,
  paddingHorizontal :: Number,
  paddingLeft :: Number,
  paddingRight :: Number,
  paddingTop :: Number,
  paddingVertical :: Number,
  position :: String, -- enum('absolute', 'relative')
  right :: Number,
  top :: Number,
  width :: Number | a
  }

  --transform :: [{perspective :: Number}, {rotate :: String}, {rotateX :: String}, {rotateY :: String}, {rotateZ :: String}, {scale :: Number}, {scaleX :: Number}, {scaleY :: Number}, {translateX :: Number}, {translateY :: Number}, {skewX :: String}, {skewY :: String}],
type TransformsFlexStyle a = FlexStyle (
  transformMatrix :: Array Number,
  rotation :: Number,
  scaleX :: Number,
  scaleY :: Number,
  translateX :: Number,
  translateY :: Number | a
  )

type ViewStyle a = TransformsFlexStyle (
  backgroundColor :: String,
  borderBottomColor :: String,
  borderBottomLeftRadius :: Number,
  borderBottomRightRadius :: Number,
  borderColor :: String,
  borderLeftColor :: String,
  borderRadius :: Number,
  borderRightColor :: String,
  borderTopColor :: String,
  borderTopLeftRadius :: Number,
  borderTopRightRadius :: Number,
  opacity :: Number,
  overflow :: String, -- enum('visible', 'hidden')
  shadowColor :: String,
  shadowOffset :: {width :: Number, height :: Number},
  shadowOpacity :: Number,
  shadowRadius :: Number | a
  )

type TextStyle = ViewStyle (
  color :: String,
  fontFamily :: String,
  fontSize :: Number,
  fontStyle :: String, -- 'normal' | 'italic';
  fontWeight :: String, -- enum("normal", 'bold', '100', '200', '300', '400', '500', '600', '700', '800', '900')
  letterSpacing :: Number,
  lineHeight :: Number,
  textAlign :: String, -- enum("auto", 'left', 'right', 'center')
  textDecorationLine :: String, -- enum("none", 'underline', 'line-through', 'underline line-through')
  textDecorationStyle :: String, -- enum("solid", 'double', 'dotted', 'dashed')
  textDecorationColor :: String,
  writingDirection :: String
  )

type ImageStyle = TransformsFlexStyle (
  resizeMode :: String, --Object.keys(ImageResizeMode)
  backgroundColor :: String,
  borderColor :: String,
  borderWidth :: Number,
  borderRadius :: Number,
  overflow :: String, -- enum('visible', 'hidden')
  tintColor :: String,
  opacity :: Number
  )

type ViewProps = {
  accessibilityLabel :: String,
  accessible :: Boolean,
  onAcccessibilityTap :: Unit -> Unit,
  onLayout :: LayoutChangeEvent -> Unit,
  onMagicTap :: Unit -> Unit,
  pointerEvents :: String,
  removeClippedSubviews :: Boolean,
  style :: Array (ViewStyle ()),
  testID :: String
  }

type OnPress eff ps s r = Unit -> EventHandlerContext eff ps s r

type TouchableWithoutFeedbackProps a = {
  accessible :: Boolean,
  delayLongPress :: Number,
  delayPressIn :: Number,
  delayPressOut :: Number,
  onLayout :: LayoutChangeEvent -> Unit,
  onLongPress :: Unit -> Unit,
  onPress :: Unit -> Unit,
  onPressIn :: Unit -> Unit,
  onPressOut :: Unit -> Unit,
  style :: Array (ViewStyle ()) | a
  }

type TouchableOpacityProps = TouchableWithoutFeedbackProps (
  activityOpacity :: Number
  )

baseStyle s x = x { style = cons (sToAny s) x.style }
  where
    sToAny :: forall a. StyleSheet -> a
    sToAny = unsafeCoerce

addStyle f x = x { style = cons (f defStyle) x.style }
  where
    defStyle = unsafeCoerce {}

type Mut a = a -> a

foldMut :: forall a. Array (Mut a) -> a -> a
foldMut = foldl (>>>) id

defProps :: forall a s. { style :: Array s | a}
defProps = unsafeCoerce { style: [] }

mkFactory klass fs es = createElement klass (foldMut fs defProps) es

view = mkFactory viewClass
touchableOpacity = mkFactory touchableOpacityClass

text :: Array (Mut TextProps) -> String -> ReactElement
text fs s = createElement textClass (foldMut fs defProps) [RD.text s]
