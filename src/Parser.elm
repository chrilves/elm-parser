module Parser exposing (
  Parser, run,
  pure, fail, lazy, rec, fetch, peek,
  map, andThen, (<$>), map2, (<&&), (&&>),
  maybe, filter, filterMap,
  not, (<|>), upTo, many, between,
  iso, normalize, lens, select
 )

{-| A generic on input monadic parsing combinator library

It is inspired by [Parsec](https://hackage.haskell.org/package/parsec)
and others monadic parsing combinator library. Parsers are values consuming some
input to produce some output value or fail.

This library is designed to be completely generic on the input type.
The input is viewed by parsers as a global mutable state. Parsers can
read and write this global mutable state freely.

Antoher design goal is to enable multi-pass parsing. A parser's input
can be the ouput of another's.

@docs Parser, run

# Constructors
@docs pure, fail, lazy, rec, fetch, peek

# Monadic operations
@docs map, andThen, (<$>), map2, (<&&), (&&>)

# Filtering output
@docs maybe, filter, filterMap

# Composing parsers
@docs not, (<|>), upTo, many, between

# Transforming the input
@docs iso, normalize, lens, select
-}


import Lazy exposing (..)

{-|Parser producing values of type `o` from input of type `s`-}
type Parser s o = Echec
                | Reussite o
                | Thunk (Lazy (Parser s o))
                | Ecrit  s   (Parser s o)
                | Lit   (s -> Parser s o)

-- Eliminator

{-|Run a parser on some input-}
run : Parser i o -> i -> Maybe (o, i)
run pa s0 =
  case pa of
    Echec      -> Nothing
    Reussite a -> Just (a, s0)
    Thunk l    -> run (Lazy.force l) s0
    Lit k      -> run (k s0) s0
    Ecrit s1 p -> run p s1

-- Constuctors

{-|The parser `pure o` always returns `o` while consuming no input-}
pure : o -> Parser i o
pure = Reussite

{-|Always fails while consuming no input-}
fail : Parser i o
fail = Echec

{-|A parser made from a lazy computation-}
lazy : (() -> Parser s o) -> Parser s o
lazy f = Thunk (Lazy.lazy f)

{-|Helps to define recursive parsers-}
rec : (Parser s o -> Parser s o) -> Parser s o
rec f = Thunk (Lazy.lazy (\_ -> f (rec f)))

{-|`fetch f` send the input to `f`.
- If `f` returns nothing, then it fails.
- If `f` returns `Just (o, i)` then it output `o` and set the input value to `i`.
-}
fetch : (i -> Maybe (o , i)) -> Parser i o
fetch f = Lit (\i -> case f i of
                       Nothing    -> Echec
                       Just (a,i) -> Ecrit i (Reussite a)
              )

{-|`peek f` send the input to `f`.
- If `f` returns nothing, then it fails.
- If `f` returns `Just o` then it output `o`. The input is unchanged.
-}
peek : (i -> Maybe o) -> Parser i o
peek f = Lit (\i -> case f i of
                      Nothing -> Echec
                      Just a  -> Reussite a
             )

-- Monadic

{-|-}
map : (a -> b) -> Parser i a -> Parser i b
map f =
  let aux pa =
        case pa of
          Echec      -> Echec
          Reussite a -> Reussite (f a)
          Thunk l    -> Thunk (Lazy.map aux l)
          Ecrit s p  -> Ecrit s (aux p)
          Lit k      -> Lit  (k >> aux)
  in aux

{-|-}
andThen : (a -> Parser i b) -> Parser i a -> Parser i b
andThen f =
  let aux pa =
        case pa of
          Echec      -> Echec
          Reussite a -> f a
          Thunk l    -> Thunk (Lazy.map aux l)
          Lit k      -> Lit (k >> aux)
          Ecrit i p  -> Ecrit i (aux p)
  in aux

{-|The applicative functor's operation **ap**-}
(<$>) : Parser i (a -> b) -> Parser i a -> Parser i b
(<$>) pf pa = pf |> andThen (\f -> map f pa)

{-|-}
map2 : (a -> b -> c) -> Parser i a -> Parser i b -> Parser i c
map2 f pa pb = (pa |> map f) <$> pb

{-|`p1 <&& p2` runs p1 then p2 but only returns p1's output-}
(<&&) : Parser i a -> Parser i b -> Parser i a
(<&&) = map2 (\a _ -> a)

{-|`p1 <&& p2` runs p1 then p2 but only returns p2's output-}
(&&>) : Parser i a -> Parser i b -> Parser i b
(&&>) = map2 (\_ a -> a)

-- Filtering

{-|`maybe p` never fails. It output `Just _` on `p`'s success and `Nothing` on `p`'s failure.-}
maybe : Parser i o -> Parser i (Maybe o)
maybe pa = (pa |> map Just) <|> pure Nothing

{-|-}
filter : (o -> Bool) -> Parser i o -> Parser i o
filter f p = p |> andThen (\a -> if f a then pure a else fail)

{-|-}
filterMap : (a -> Maybe b) -> Parser i a -> Parser i b
filterMap f p = p |> andThen (\a ->
  case f a of
    Just b -> pure b
    _      -> fail
 )

-- And/Or

{-|`not o p` returns `o` if `p` fails. Fails otherwise. It never consume input.-}
not : o -> Parser i o -> Parser i o
not a =
  let aux pa =
        case pa of
          Echec      -> Reussite a
          Reussite _ -> Echec
          Thunk l    -> Thunk (Lazy.map aux l)
          Lit k      -> Lit (k >> aux)
          Ecrit s p  -> Ecrit s (aux p)
  in aux

{-|`p1 <|> p2` is `p1` if `p1` success and `p2` is `p1` fails-}
(<|>) : Parser i o -> Parser i o -> Parser i o
(<|>) p1 p2 =
  let aux : Maybe i -> Parser i o -> Parser i o
      aux mi p1 =
        case p1 of
          Reussite _ -> p1
          Echec      -> case mi of
                          Nothing -> p2
                          Just i  -> Ecrit i p2
          Thunk l    -> Thunk (Lazy.map (aux mi) l)
          Lit   k    -> Lit (\i0 -> let mi2 = case mi of
                                                Just _  -> mi
                                                Nothing -> Just i0
                                     in aux mi2 (k i0)
                            )
          Ecrit s p  -> Ecrit s (aux mi p)
  in aux Nothing p1

{-|`upTo n p` uses `p` to parse up to `n` elements.-}
upTo : Int -> Parser i o -> Parser i (List o)
upTo n pa =
  case n of
    0 -> pure []
    1 -> pa |> map (\x -> [x])
    _ -> if (n > 0)
         then map2 (::) pa (upTo (n - 1) pa)
         else fail

{-|`many p` parse elements using `p` until `p` fails-}
many : Parser i o -> Parser i (List o)
many pa = rec (\r -> (map2 (::) pa r) <|> pure [])

{-|`between inf sup p` uses `p` to parse between `inf` and `sup` elements (both included).-}
between : Int -> Maybe Int -> Parser i o -> Parser i (List o)
between inf msup pa =
  let pla = case msup of
              Just sup -> upTo sup pa
              Nothing  -> many pa
  in pla |> andThen (\l -> if List.length l < inf then fail else pure l)

-- State Transformation

{-|`iso i2j j2i p` transforms input by `j2i` before sending it to `p` and
by `i2j` when `p` wants to store the state.
-}
iso : (i -> j) -> (j -> i) -> Parser i o -> Parser j o
iso i2j j2i =
  let aux p =
        case p of
          Echec      -> Echec
          Reussite a -> Reussite a
          Thunk l    -> Thunk (Lazy.map aux l)
          Lit k      -> Lit (j2i >> k >> aux)
          Ecrit i p  -> Ecrit (i2j i) (aux p)
  in aux

{-|`normalize f = iso f f`-}
normalize : (i -> i) -> Parser i o -> Parser i o
normalize f = iso f f

{-|-}
lens : (j -> (i, i -> j)) -> Parser i o -> Parser j o
lens l =
  let aux mctx p =
        case p of
          Echec      -> Echec
          Reussite a -> Reussite a
          Thunk lz   -> Thunk (Lazy.map (aux mctx) lz)
          Lit k      -> Lit (\j0 -> let (i0, ctx) = l j0
                                    in aux (Just ctx) (k i0)
                            )
          Ecrit s p  -> case mctx of
                          Nothing  -> Echec
                          Just ctx -> Ecrit (ctx s) (aux mctx p)
  in aux Nothing

{-|-}
select : (j -> Maybe (i, i -> j)) -> Parser i o -> Parser j o
select l =
  let aux mctx p =
        case p of
          Echec      -> Echec
          Reussite a -> Reussite a
          Thunk lz   -> Thunk (Lazy.map (aux mctx) lz)
          Lit k      -> Lit (\j0 -> case  l j0 of
                                      Just (i0, ctx) -> aux (Just ctx) (k i0)
                                      Nothing -> Echec
                            )
          Ecrit s p  -> case mctx of
                          Nothing  -> Echec
                          Just ctx -> Ecrit (ctx s) (aux mctx p)
  in aux Nothing