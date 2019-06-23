> {-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

> module Golf

> where

This is imported by the CTF

> import Control.Applicative
> import Control.Arrow
> import Control.Monad
> import Data.Array
> import Data.Bits
> import Data.Bool
> import Data.Char
> import Data.Complex
> import Data.Dynamic
> import Data.Either
> import Data.Eq
> import Data.Fixed
> import Data.Function
> import Data.Graph
> import Data.Int
> import Data.Ix
> import Data.List
> import Data.Maybe
> import Data.Monoid
> import Data.Ord
> import Data.Ratio
> import Data.Tree
> import Data.Tuple
> import Data.Typeable
> import Data.Word
> import Text.Printf

This is not imported by the CTF.

> import qualified System.Random as R

-- Generate a test case:

> pprint :: [String] -> String
> pprint strs = concatMap (\str -> "\""++str ++  "\"\n") strs

> targets :: Int -> [Int]
> targets num = (R.randomRs (1, num) (R.mkStdGen 1))

> explode :: Int -> String -> [String]
> explode num str = map (\target->
>                          map (\(i,t)->
>                                 if t == target
>                                 then (str!!(i-1))
>                                 else ' ') (zip [1..(length str)] (targets num))) [1..num]


> tests1 :: String
> tests1 = "Your task is to write a payload that decrypts these messages for us."
> tests2 :: String
> tests2 = "I have no idea man this is just where I work"
> tests3 :: String
> tests3 = "There are no bagels in this neighbourhood but if you go over yonder there may be some possibility of finding a poodle."

> breakApartAndIO :: Int -> String -> IO ()
> breakApartAndIO n str = putStr $ pprint $ strip <$> explode n str

> test :: String
> test = solution problem -- solve problem
>   where
>     problem :: [String]
>     problem = strip <$> (explode 6 $ concat [tests1, tests2, tests3])

solve strs = head $ sortBy (lexical) $ mergeAll <$> ((applyOffsets strs) <$> (findOffsets $ mkBlocks strs))


-- Specification

For the data we're working with, the following rules seem to always hold:

1. The correct offset will never cause two characters to occupy the same column.
2. The correct offset will minimize the length of the final text after trimming
   leading and trailing spaces.
3. If there are multiple possible decryptions that follow the above rules, the
   lexicographically first one is correct.

We start by attacking this.

Our strategy is attempt to zip together the strings. zipWith is the solution.

solve :: [String] -> String

Each line has an offset.

Lexicographical order := like a phonebook.

Pipeline:

[String] -possible-> [String] -shortest-> [String] -first-> String

-- Solution in less than 300 bytes

Okay I can solve the problem but it takes 300 bytes.


If we treat the offsets as a lattice that we traverse with

> g = mapM(\x->[0..x])

then we will do a reduction like this:

> areduction :: [String] -> Maybe String
> areduction = concat . (filter $ (==1).length) . (filter /=' ') <$> transpose

if the second filter actually filters something then we return nothing.

after concat we would need to count the bits (i.e. not whitespaces) and compare to the bits in a concat of the original string matrix.

The concat would actually be done with a list comprehension and we would use the infix operator equivalent of !! that returns ' ' if it tries to index an empty list.

This would have to fit into 100 bytes but it would replace binary merge operation that made the other solution to big.

However I feel like I am missing experience with using monads to keep track of state in the pipeline since that way I could hide the structure and save bytes.

Anyway I'm out of time so I'm just going to keep playing around with the shamir secret sharing challenge.





--- Tools I use ----

Not needed, sort already is lexical!

 lexical :: Ord a => [a] -> [a] -> Ordering
 lexical [] [] = EQ
 lexical [] _  = LT
 lexical _  [] = GT
 lexical (x:xs) (y:ys) | compare x y == EQ = lexical xs ys
                       | otherwise = compare x y


---- Filters ----

> ck :: String -> Bool
> ck xs = (length $ filter (/=' ') xs) < 2


> chk :: [String] -> Bool
> chk xs = (\x->(length$filter (/=' ') x)<2) (head<$>xs)&&(chk$tail<$>xs)

Now we need to minimize this:

> min_chk :: [String] -> Bool
> min_chk xs = foldr ((&&) . (\y->(length$filter (/=' ') y)<2)) True (transpose xs)

Transpose works as expected.

Another Check idea:
-> OR rows together, if number of bits is smaller than number of bits in the matrix FALSE

Idea bank: Transpose would give a lot of things
-- || -- : Traversible will traverse everything!

--------------------------

-- Utility:

> if' :: Bool -> a -> a -> a
> if' True x _ = x
> if' _ _ y = y

> strip :: String -> String
> strip = reverse . (dropWhile (==' ')) . reverse . (dropWhile (==' '))

-- Merge functions

> mergeAll :: [String] -> String
> mergeAll xs | chk xs = (head . (filter (/=' '))) <$> transpose xs
>             | otherwise = concat xs -- worst possible solution basically.


Either we just naively merge the strings or we find all possible ways to combine the strings with the caveat that we assume that these are the only two strings. The offsets are applied to str2 and maxn=str1+str1+str2

> combinations :: String -> String -> [Int]
> combinations str1 str2 = filter (\x->chk[cmpStr,(mkOffset x)++str2]) [0..(length cmpStr)]
>   where
>     cmpStr = (mkOffset (length str2)) ++ str1

Our problem with this approach is that it is non-exhaustive.

IF the strings are supposed to have a space between them then this won't be able to find it.


-- This is the final form merge.
It assumes that the first one needs no padding and picks the first possible way to merge.

> merge :: String -> String -> String
> merge s1 s2 | min_chk [s1, s2] = strip $  map (\(a,b)->if' (a==' ') b a) $ zip (s1++(take (length s2) $ repeat ' ')) (s2++(take (length s1) $ repeat ' '))
>             | otherwise = merge s1 (' ':s2)

and it works!!

-- Sliding window method

We get the necessary information for combining the strings by counting number of letters or spaces in each `block` of text within an individual string. We make sure that the first number is a number of letters and then it will alternate.

> split :: String -> [String]
> split string = reverse $ go (strip string) False []
>   where
>     go :: String -> Bool -> [String] -> [String]
>     go "" _ acc = acc
>     go str True acc  = go (dropWhile (==' ') str) False ((takeWhile (==' ') str):acc)
>     go str False acc = go (dropWhile (/=' ') str) True  ((takeWhile (/=' ') str):acc)

> mkBlocks :: [String] -> [[Int]]
> mkBlocks xs = (fmap length) <$> (split <$> ((dropWhile (==' ')) <$> xs))

Then we find the offset list that makes the smallest solution. We want to combine all the blocklists into a single blocklist s.t. the sum of it's elements is as small as possible.

The finding of offsets is like subset-sum on steroids and takes a lot of code to do properly.

 findOffsets :: [[Int]] -> [[Int]] -- Blocklist -> Offsetlistlist
 findOffsets xs = foldr (\(i,b,ys)->) [] (struct xs)
   where
     struct :: [[Int]] -> [(Int, Bool, [Int])] -- index, notspace, blocks
     struct xs = (zip3 [0..] (repeat True) xs)

     blkChk :: [(Int, Bool, [Int])] -> Bool
     blkChk zs | any (\(_,b,_)->b) zs = (\ws->all (\w->((filter \(_,v,_->v)) ws)<=w) ws) (head <$> zs)
               | otherwise = True -- we will remove the smallest common padding so that one string is unpadded. This case never happens


-- Search functions

The reduction we will do is:
- Assume some String has no padding
- Merge it with the next string in the list
- Assume the resulting string has no padding
- Merge it with the next  string in the list
- etc.

> reduction :: [String] -> String
> reduction xs = foldr merge [] xs


> searchStrs :: [String] -> [String]
> searchStrs strs = reduction <$> (permutations strs)


Can be minified:

> getShortest :: [[a]] -> [[a]]
> getShortest xs = (\ys->
>                      (takeWhile $ (\x y->
>                                     (length x)==(length y)) $ head ys) ys)
>                  $ sortBy (\x y-> compare (length x) (length y)) $ xs

> solution :: [String] -> String
> solution strs = head $ sort $ getShortest $ searchStrs strs

-- Offset list

I need some way to do this cleverly, bound the amount of possible offsets.
=> We can keep one string in place!

Strategy: We sort strings by length, shortest first.
We offset the first string so that it is a suffix for the longest string
Then we offset all the other strings in lexical ordering keeping that one constant
and finally we end when it has become a prefix for the others.

Then we filter based on length.

Then we sort based on lexical ordering.

> mkOffset :: Int -> String
> mkOffset n = take n $ repeat ' '

> applyOffsets :: [String] -> [Int] -> [String]
> applyOffsets strs xs = (\(n,str)-> (mkOffset n)++str) <$> (zip xs strs)

Naive increment, gets fed a max-num so that it knows when to stop.

 increment :: Int -> [Int] -> Maybe [Int]
 increment _ [] = Nothing
 increment maxn [n] = Just [succ n]
 increment maxn (n:ns) | all $ (\x-> x==maxn) <$> (n:ns) = Nothing
                       | all $ (\x-> x==maxn) <$> ns = Just (succ n):ns
                       | otherwise = (n:)<$>(increment ns)

 offset_start :: [String] -> [Int]
 offset_start words = take (length words) $ repeat 0

 lex_ord :: Ord a => [a] -> [a]
 lex_ord xs = sortBy (fst . (<)) $ zip (head <$> xs) [1..]

 ord (x:xs) = 

> inc :: [Int] -> [Int]
> inc = id

 gen :: [Int] -> [String] -> [String]
 gen off xs | (chk $ possibility words off) = (possibility xs off):(gen (inc off) xs)
   where
     possibility words offsets = (\(w,o)-> (take o $ repeat " ")<>w) <$> (zip words offsets)



--- Code golf part of challenge ---

Your solution must be provided in a single line of Base64-encoded UTF-8,
without any extra whitespace. That is, if your code looked like this:

    g a = "This is probably not the right answer"

You would need to submit:

    ZyBhID0gIlRoaXMgaXMgcHJvYmFibHkgbm90IHRoZSByaWdodCBhbnN3ZXIi

Note that it is the length of your source code, *not* of the Base64 version,
that matters. The above example would count as 46 bytes.

Your task is to write a function `g :: [String] -> String`
that takes a list of strings, each representing a transparency, and produces a
decrypted string according to the rules above. You may write any helper
functions you need, so long as the total length of your code does not exceed 181
bytes.

You have access to the following modules, all of which are imported for you.
No other modules may be imported.

    Prelude
    Control.Applicative
    Control.Arrow
    Control.Monad
    Data.Array
    Data.Bits
    Data.Bool
    Data.Char
    Data.Complex
    Data.Dynamic
    Data.Either
    Data.Eq
    Data.Fixed
    Data.Function
    Data.Graph
    Data.Int
    Data.Ix
    Data.List
    Data.Maybe
    Data.Monoid
    Data.Ord
    Data.Ratio
    Data.Tree
    Data.Tuple
    Data.Typeable
    Data.Word
    Debug.SimpleReflect
    Text.Printf
    ShowFun

-- Scrapped ideas:

 reduction :: String -> [String] -> [[String]]
 reduction [] = []
 reduction s strs = take 10 $ sortBy (\x y-> compare (length x) (length y)) $ (merge s) <$> strs
