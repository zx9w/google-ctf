module GolfSolution

where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Data.Array
import Data.Bits
import Data.Bool
import Data.Char
import Data.Complex
import Data.Dynamic
import Data.Either
import Data.Eq
import Data.Fixed
import Data.Function
import Data.Graph
import Data.Int
import Data.Ix
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Ord
import Data.Ratio
import Data.Tree
import Data.Tuple
import Data.Typeable
import Data.Word
import Text.Printf


if' :: Bool -> a -> a -> a
if' True x _ = x
if' _ _ y = y

strip :: String -> String
strip = reverse . (dropWhile (==' ')) . reverse . (dropWhile (==' '))

min_chk :: [String] -> Bool
min_chk xs = foldr ((&&) . (\y->(length$filter (/=' ') y)<2)) True (transpose xs)

merge :: String -> String -> String
merge s1 s2 | min_chk [s1, s2] = strip $  map (\(a,b)->if' (a==' ') b a) $ zip (s1++(s2>>" ")) (s2++(s1>>" "))
            | otherwise = merge s1 (' ':s2)


reduction :: [String] -> String
reduction xs = foldr merge [] xs


searchStrs :: [String] -> [String]
searchStrs strs = reduction <$> (permutations strs)


getShortest :: [[a]] -> [[a]]
getShortest xs = (\ys->
                     (takeWhile $ (\x y->
                                    (length x)==(length y)) $ head ys) ys)
                 $ sortBy (\x y-> compare (length x) (length y)) $ xs

solution :: [String] -> String
solution = head.sort.gs.searchStrs

_#[]=' '
0#(y:_)=y
x#(y:z)=(x-1)#z

(?)=filter


-- Mini merge
m :: String -> String -> String
-- m s z = last$s:[z|s==z]
m s z = head$filter(((==)$length.filter(/=' ')$s++z).length.filter(/=' '))[[last$(1#e):[0#e|0#e/=' ']|e<-q,(' '==0#e)||(' '==1#e)]|q<-((\w->transpose [s,w])<$>((++z)<$>[[' '|_<-[1..n]]|n<-[1..(length s)]]))]

sol = head.sort.(takeWhile=<<(.length).(==).length.head).(sortOn length).((foldr m [])<$>).permutations

-- Mini getShortest
gs :: [[a]]->[[a]]
gs = (takeWhile=<<(.length).(==).length.head).(sortOn length)

-- mini searchStr
ss = (reduction <$>) . permutations



-- last$x:[y|b] -- is equivalent to: if b then y else x

--chk :: String -> String -> Bool
--chk x y =  all $ (||) <$> ((<$>).(<$>)) $ (==' ') (transpose [x,y])

--(||)<$>((==' ')<$>x)<*>(==' '<$>y)

{-
ms :: [String] -> String
ms ss
 = head$sort$(\->)$(foldMap ($))<$>(permutations ss)
  where
    m x y | (all$(||)( (transpose [x, y])
    gs xs = 


-}
