# Applicative Showcase

In some use cases a Functor is too simple and a Monad is too heavy-weighted.
For example, let look at a form-validation process:

> import Control.Applicative

A user type that's going to be the final result of the validation:

> data User = User {
>   uName :: String,
>   uAge :: Int,
>   uGender :: Gender
> } deriving (Show)

> data Gender = Male | Female | Hideyoshi
>   deriving (Show)

Let's say the form input is a tuple of two strings and a int:

> type UserForm = (String, Int, String)

The validation function needs to have the following type:

> toUser :: UserForm -> Result User

where the Result type allows us to attach an error message if the validation
failes.

> type Result a = Either ErrorMessage a
> type ErrorMessage = String

Where gender can be validated by

> toGender :: String -> Result Gender
> toGender "M" = Right Male
> toGender "F" = Right Female
> toGender "H" = Right Hideyoshi
> toGender g   = Left $ "Not a valid gender: " ++ g

Also we have age validation:

> toAge :: Int -> Result Int
> toAge i | i < 0     = Left "Negative age"
>         | otherwise = Right i

And name validation:

> toName :: String -> Result String
> toName "" = Left "Empty name"
> toName xs = Right xs

So how do we write toUser? Let's first try pattern matching:

> toUserP :: UserForm -> Result User
> toUserP (nameS, ageS, genderS) = case (nameM, ageM, genderM) of
>   (Right name, Right age, Right gender) ->
>     Right $ User name age gender
>   (Left nameE, _, _) ->
>     Left nameE
>   (_, Left ageE, _) ->
>     Left ageE
>   (_, _, Left genderE) ->
>     Left genderE
>  where
>   nameM   = toName nameS
>   ageM    = toAge ageS
>   genderM = toGender genderS

That's long! Can we use Monad instead?

> toUserM :: UserForm -> Result User
> toUserM (nameS, ageS, genderS) = do
>   name   <- toName nameS
>   age    <- toAge ageS
>   gender <- toGender genderS
>   return $ User name age gender

This is clearly better. However it still introduces temporary variables.
What about Applicative?

> toUserA :: UserForm -> Result User
> toUserA (nameS, ageS, genderS) =
>   User <$> toName nameS <*> toAge ageS <*> toGender genderS

So you can see that the applicative style is very consise and compact.

> toUser = toUserA

> main = do
>   print $ toUser ("Wu", (-1), "M")
>   print $ toUser ("De", 52, "Yooo")
>   print $ toUser ("", 52, "M")
>   print $ toUser ("Kai", 52, "M")

