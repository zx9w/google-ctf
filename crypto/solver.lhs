
> {-# LANGUAGE ConstraintKinds                              #-}
> {-# LANGUAGE GADTs                                        #-}
> {-# LANGUAGE DataKinds                                    #-}
> {-# LANGUAGE PolyKinds                                    #-}
> {-# LANGUAGE StandaloneDeriving                           #-}
> {-# LANGUAGE TypeFamilies                                 #-}
> {-# LANGUAGE TypeInType                                   #-}
> {-# LANGUAGE TypeOperators                                #-}
> {-# LANGUAGE UndecidableInstances                         #-}
> {-# LANGUAGE EmptyCase                                    #-}
> {-# LANGUAGE FlexibleInstances                            #-}
> {-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}


> module Shamir

> where

> import qualified Data.ByteString.Char8 as Chr8
> import Data.Char
> import Data.Kind (Constraint, Type)

> data Nat = Z | Suc Nat
>   deriving (Show, Read, Eq, Ord)

> data Vec :: Nat -> Type -> Type where
>   Nul  :: Vec Z a
>   (:>) :: a -> Vec n a -> Vec (Suc n) a

> deriving instance Show a => Show (Vec n a)
> deriving instance Eq   a => Eq   (Vec n a)
> deriving instance Ord  a => Ord  (Vec n a)

> instance Foldable (Vec n) where
>   foldr _ z Nul = z
>   foldr f z (x :> xs) = foldr f (f x z) xs

> instance Functor (Vec n) where
>   fmap _ Nul = Nul
>   fmap f (x :> xs) = (f x) :> (fmap f xs)

> instance Traversable (Vec n) where
>   sequenceA Nul       = pure Nul
>   sequenceA (x :> xs) = (:>) <$> x <*> sequenceA xs


Google CTF => Reality

Here's a base32-encoded and encrypted flag:

> ctxtb32 :: String
> ctxtb32 = "RZTN56A37VOLHPWFT42MJVJAIT2ISIC4Q6T52QKFNGJZPCF7LE6A===="

We want this flag to be in base10 so that we can fit it into our polynomial.

This is the base32 reference: https://tools.ietf.org/html/rfc4648#page-8

> b32toNums :: String -> [Int]
> b32toNums "" = []
> b32toNums (x:xs) = (myLookup x) : (b32toNums xs)
>   where
>     myLookup :: Char -> Int
>     myLookup 'Z' = 25
>     myLookup '7' = 31
>     myLookup char = (myLookup (succ char))-1

Base32 splits data into 40 bit parts, the '=' is padding to fill in a part.

Each part consists of 8 characters (each character has 5 bits of data).

The cases we can encounter are:

Data is multiple of 40 bits    -> No padding
Final part has 8 bits of data  -> ======
Final part has 16 bits of data -> ====
Final part has 24 bits of data -> ===
Final part has 32 bits of data -> =

The idea is that we take 8 things in the list and turn them into 5 octets of data.

We should be using a dependently types list to make sure that its length is a multiple of 8.
  => No we should not, because it is a total hack unless we do it in Idris.

> data Bit = Zero | One deriving (Eq, Ord, Enum)
> instance Show Bit where
>   show One = "1"
>   show Zero = "0"


I will just make an increment function instead of trying to derive Enum.


> increment :: [Bit] -> Maybe [Bit]
> increment [] = Nothing
> increment [Zero] = Just [One]
> increment (x:xs) | (allOne xs) = if x == Zero
>                                  then Just (One : (take (length xs) $ repeat Zero))
>                                  else Nothing
>                  | otherwise = (x :) <$> (increment xs)

> allOne :: [Bit] -> Bool
> allOne [] = True
> allOne (x:xs) | x == Zero = False
>               | otherwise = allOne xs

Then I can use a conversion toInt and fromInt to get where I need to be.

> toInt :: [Bit] -> Int
> toInt [] = 0 -- This is not strictly true
> toInt (x:xs) | x == One  = 2^(length xs) + (toInt xs)
>              | x == Zero = toInt xs
> toInt _ = 0


> preFromInt :: Int -> [Bit]
> preFromInt 0 = [Zero]
> preFromInt 1 = [One]
> preFromInt x | even x    = (preFromInt $ x `quot` 2) ++ [Zero]
>              | otherwise = (preFromInt $ (x-1) `quot` 2) ++ [One]

The padding is just useful because we get 5 bits per number and change to 8 bits.

> padding :: [Bit] -> [Bit]
> padding xs = if (length xs < 5) then padding (Zero : xs) else xs

I should use Quickcheck to make sure this invariant holds! ~ toInt $ fromInt x == x

> fromInt :: Int -> [Bit]
> fromInt = padding . preFromInt

This function changes a natural number to an array of bits.

> makeBits :: [Int] -> [Bit]
> makeBits xs = foldr ((++) . fromInt) [] $ filter (/=(-4)) xs

This function take 8 bits and makes an int from it (basically a char).

> makeInts :: [Bit] -> [Int]
> makeInts [] = []
> makeInts xs = (toInt (take 8 xs)) : (makeInts (drop 8 xs))

Here I have an array of 5 bit ints and I change it into an array of 8 bit ints.

The strategy is to take 8 numbers make a single array of 40 bits and then break that up.

> change5to8 :: [Int] -> [Int]
> change5to8 [] = []
> change5to8 xs = (makeInts $ makeBits $ take 8 xs) ++ (change5to8 $ drop 8 xs)


> dataIntsToByteString :: [Int] -> Chr8.ByteString
> dataIntsToByteString [] = Chr8.empty
> dataIntsToByteString (x:xs) = Chr8.cons (chr x) (dataIntsToByteString xs)

> getBase32Data :: String -> Chr8.ByteString
> getBase32Data str = dataIntsToByteString $ change5to8 $ b32toNums str

 intsToNaive :: [Int] -> Bits n Bit
 intsToNaive [] = Nil
 intsToNaive xs = (translate $ take 8 xs) :* (intsToNaive $ drop 8 xs)
   where
     translate :: [Int] -> Bits n Bit
     translate [] = Nil
     translate (i:ints) | i == -4 = Nil
                        | otherwise =  (toEnum i):*(translate ints)






This dependently typed stuff is probably a horrible way to do this.
  => yes it is, I give up.

 data Bits :: Nat -> Type -> Type where
   Nil  :: Bits Z Bit
   (:*) :: Bit -> Bits n Bit -> Bits (Suc n) Bit

deriving instance Show a => Show (Bits n Bit)
deriving instance Eq   a => Eq   (Bits n Bit)
deriving instance Ord  a => Ord  (Bits n Bit)

 head :: Bits (Suc n) Bit -> Bit
 head (x :* _) = x

 tail :: Bits (Suc n) Bit -> Bits n Bit
 tail (_ :* xs) = xs

 instance Foldable (Bits n) where
   foldr _ z Nil = z
   foldr f z (x :* xs) = foldr f (f x z) xs

 instance Functor (Bits n) where
   fmap _ Nil = Nil
   fmap f (x :* xs) = (f x) :* (fmap f xs)

 instance Traversable (Bits n) where
   sequenceA Nil       = pure Nil
   sequenceA (x :* xs) = (:*) <$> x <*> sequenceA xs


I don't know how to use the Vec data to define NaiveBits

 data NaiveBits = Vec (Suc n) Bit

So everything has changed to this Bits datatype that is a more restricted version of Vec.

 allOne :: Bits (Suc n) Bit -> Bool
 allOne One = True
 allOne (x:*xs) | x == Zero = False
                | otherwise = allOne xs


This is probably not such a great way to do this.

 makeZeros :: Bits (Suc n) Bit -> Bits (Suc n) Bit
 makeZeros (_:*Nil) = Zero :* Nil
 makeZeros (x:*xs)  = Zero :* (makeZeros xs)

 instance Enum (Bits (Suc n) Bit) where
   succ :: Bits (Suc n) Bit -> Bits (Suc n) Bit
   succ (x:*xs) | allOne xs = (succ x):*(makeZeros xs)
                | otherwise = x:*(succ xs)

 instance Show (Bits (Suc n) Bit) where
   show xs = foldMap show xs

Now we can get finish our base32 conversion

(I'm not going to make a type that makes sure the list has length that is multiple of 8)

 intsToNaive :: [Int] -> Bits n Bit
 intsToNaive [] = Nil
 intsToNaive xs = (translate $ take 8 xs) :* (intsToNaive $ drop 8 xs)
   where
     translate :: [Int] -> Bits n Bit
     translate [] = Nil
     translate (i:ints) | i == -4 = Nil
                        | otherwise =  (toEnum i):*(translate ints)

Note to self: next time use Idris.

----------- End stupid dependently typed stuff -------------------

base32 -d gives:

 ctxt = "fş4 D \AEiY<"

so my implementation of base32 is correct!

Now to solve the problem.

This is a (5,n) threshold scheme so we have a 4th degree polynomial.

The secret is the constant term of the polynomial so we need to find f(0).

where we have the following equation for f:

f(x) = ptxt + a1 x + a2 x^2 + a3 x^3 + a4 x^4

I don't yet understand how the ctxt fits in but my hypothesis is:
=> ctxt is encrypted with rsa
=> the private key is the secret in the shamir secret

we can therefore assume that a0 is a prime number

Let's try to write the interpolation in the ugliest way possible:

> subPolation :: Rational -> Rational -> Rational -> Rational
>             -> Rational -> Rational -> Rational -> Rational
> subPolation yj xj xm0 xm1 xm2 xm3 x
>   = yj*((x-xm0)/(xj-xm0))*((x-xm1)/(xj-xm1))*((x-xm2)/(xj-xm2))*((x-xm3)/(xj-xm3))



> interpolation :: Rational -> Rational -> Rational -> Rational -> Rational -> Rational
>               -> Rational -> Rational -> Rational -> Rational -> Rational -> Rational
> interpolation x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x
>   = subPolation y0 x0 x1 x2 x3 x4 x
>   + subPolation y1 x1 x0 x2 x3 x4 x
>   + subPolation y2 x2 x0 x1 x3 x4 x
>   + subPolation y3 x3 x0 x1 x2 x4 x
>   + subPolation y4 x4 x0 x1 x2 x3 x


> equation :: Rational ->
> equation brute_x1 brute_y1 brute_x2 brute_y2
>   = interpolation g_x1 g_fx1 g_x2 g_fx2 g_x3 g_fx3 brute_x1 brute_y1 brute_x2 brute_y2 0




The following three coordinates satisfy the equation.

coefficients 1:

> g_x1 :: Rational
> g_x1 = 1.505117499247214630924512847267979613769462905262487114759381502761123961852607339573816373829348003868607684002420229130697780634932380997717799180817425137675515324586017552155102874429962233450969350825850137585127913605216538638066828698399081178354805655330817216806513464435284935457397486491044377189818064832941355907795441407528829562801759020232076577597350929695599585566850111078553025294573294508335784157970803083832500115503080030545369802979401085165215711770543581228067116169166957

> g_fx1 :: Rational
> g_fx1 = 3808553642364268241782612886552327210624.767031948074667291673760574952920536448725625791340401120209338836429793684067144776163984733017554631378031845122772967243740514213871372005542298031484445539817274707387934463832452544216696270740013909322231589333555413178927671492653653498782005624421189690303044208037110199684565074364583617255453592012203586532340931433437479341885283880075781329075019438019315126941731314803215798293244679721969215848302499714752427444529532921146961613467755253446

coefficients 2:

> g_x2 :: Rational
> g_x2 = 1.3745867258717334112559815243328723315107366523817988974613217689796916683975857237002410944088415813757009202661829077991544409879934883068632932472836483323769177555524217942837935257875358349851393874880182158466256468870413461475944743051015336734186750929225618526014155154427970529221597109735467159242024819916273868071311255561437088173663691002941457544143855107175017269918275202812620469280094301738365995801118636931347871479988977945423798129010024316438556617794879519449121059162569073

> g_fx2 :: Rational
> g_fx2 = 2991455322865145593456708251805550080766.2245099545815519969558015455631189083441552663866455473716581269087266651184000653679036226366768485148086497604461640851942548901380875400271374502627956898854309204914998657161738171615679188677181839428642840553525171563574462703154710772514011840188881819863636246573813838857544894328548366464900120059408646337197984170572347609206257443958127073593178082179880938935916915918917591336967758841573185517976052935475997307049645901419967810993480349108586

coefficients 3:

> g_x3 :: Rational
> g_x3 = 1.0642755308392070331995628718826849712547617088569427728139145995831243091282388132557831555848623286319050086219852223883944254078542966368160381341615376912045474645480105931194548004836706594585772302635189715222051913729701299722452936123548553208165406729266858453940957362623414095370552790849889181731110713477919762784241357038753696013756404974377972101057436812961919121189619014936257915446656952320448126198938540550597609393689077076064139728603215184862079350145170859473842766747414771

> g_fx3 :: Rational
> g_fx3 = 1639297048960664640237420360291885165014.8353952686196028555264390378263117543846610614896449623855302065581630915371062983712921843083735517168750771388040481207450988157792713068643298474012561916200796493884966500978779317122892602252769466804524438487041252913110000649710790587049728073675677950359059183374597220449657345481415519261972133880621029464625851303075861653182744800861034308195928064608638070938534846403055171466451948933431222937631600957843625166041424697993388963006222535855049

We will use lagrange curve fitting to set up the equation for the solution.

We can assume that the coefficients of the polynomial are integers!

 constantTerm :: String -> Int
 constantTerm 


 lagrange :: Rational -> Rational -> Rational -> Rational
          -> Rational -> Rational -> Rational -> Rational
          -> Rational -> Rational -> (Rational -> Rational)
 lagrange x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 = \x -> (((a4*x +a3)*x +a2)*x +a1)*x+a0
   where
     a0 = (someFun ctxt)
     a1 = 
     a2 = 
     a3 = 
     a4 = 
