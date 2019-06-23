-- Exercises from the Well-Typed course

--

--   Fun with Types: Type-level programming with GHC

--   Adam Gundry

--   ZuriHac 2019

--

-- Copyright (c) 2019 Well-Typed LLP



{-# LANGUAGE ConstraintKinds                              #-}
{-# LANGUAGE GADTs                                        #-}
{-# LANGUAGE DataKinds                                    #-}
{-# LANGUAGE PolyKinds                                    #-}
{-# LANGUAGE StandaloneDeriving                           #-}
{-# LANGUAGE TypeFamilies                                 #-}
{-# LANGUAGE TypeInType                                   #-}
{-# LANGUAGE TypeOperators                                #-}
{-# LANGUAGE UndecidableInstances                         #-}
{-# LANGUAGE EmptyCase                                    #-}
{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module Exercises where

import Data.Kind (Constraint, Type)

import Prelude hiding ((++), (!!), reverse, length, minimum, unzip, take, drop, replicate, zipWith)



-- Definitions from the slides


data Nat = Zero | Suc Nat
  deriving (Show, Read, Eq, Ord)

data Vec :: Nat -> Type -> Type where
  Nil  :: Vec Zero a
  (:*) :: a -> Vec n a -> Vec (Suc n) a

infixr 5 :*

-- GADTs frequently need StandaloneDeriving so we can specify the context

deriving instance Show a => Show (Vec n a)
deriving instance Eq   a => Eq   (Vec n a)
deriving instance Ord  a => Ord  (Vec n a)

data SomeVec :: Type -> Type where
  SomeVec :: Vec n a -> SomeVec a

fromList :: [a] -> SomeVec a
fromList []       = SomeVec Nil
fromList (x : xs) = case fromList xs of
                      SomeVec ys -> SomeVec (x :* ys)

type family (+) (m :: Nat) (n :: Nat) :: Nat where
  Zero  + n = n
  Suc m + n = Suc (m + n)

(++) :: Vec m a -> Vec n a -> Vec (m + n) a
Nil       ++ ys = ys
(x :* xs) ++ ys = x :* (xs ++ ys)

type family If (x :: Bool) (t :: k) (f :: k) :: k where
  If True  t _ = t
  If False _ f = f

type family Replicate (n :: Nat) (x :: a) :: Vec n a where
  Replicate Zero    _ = Nil
  Replicate (Suc n) x = x :* Replicate n x

data SNat (n :: Nat) where
  SZero :: SNat Zero
  SSuc  :: SNat n -> SNat (Suc n)

replicate :: SNat n -> a -> Vec n a
replicate SZero    _ = Nil
replicate (SSuc n) x = x :* replicate n x

class SNatI (n :: Nat) where
  sNat :: SNat n

instance SNatI Zero where
  sNat = SZero

instance SNatI n => SNatI (Suc n) where
  sNat = SSuc sNat

replicate' :: SNatI n => a -> Vec n a
replicate' = replicate sNat

-- Exercise T1. [GADTs]
--
-- Define 'head' and 'tail' for 'Vec'.

head :: Vec (Suc n) a -> a
head (x :* _) = x

tail :: Vec (Suc n) a -> Vec n a
tail (_ :* xs) = xs


-- Exercise T2. [GADTs]
--
-- Write 'minimum' for 'Vec'.

-- minimum :: Ord a => [a] -> a

minimum :: Ord a => Vec (Suc n) a -> a
minimum (x :* Nil) = x
minimum (x :* y :* xs) | x < minimum (y :* xs) = x
                       | otherwise             = minimum (y :* xs)

-- Exercise T3. [GADTs]
--
-- Write 'zipWith' for 'Vec', where the vectors are required to be the same
-- length.  Observe how few cases are required!

zipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith _ _ Nil = Nil
zipWith f (x :* xs) (y :* ys) = (f x y) :* zipWith f xs ys

-- Exercise T4. [GADTs]
--
-- Define a 'Traversable' instance for 'Vec' (which implies
-- that you have to define a 'Functor' and a 'Foldable'
-- instance, too).
--
-- Note: These can just be derived using StandaloneDeriving,
-- and doing so is fine, but if you prefer, you can also define
-- the instances manually.

instance Foldable (Vec n) where
  foldr _ z Nil = z
  foldr f z (x :* xs) = foldr f (f x z) xs

instance Functor (Vec n) where
  fmap _ Nil = Nil
  fmap f (x :* xs) = (f x) :* (fmap f xs)

instance Traversable (Vec n) where
  sequenceA Nil       = pure Nil
  sequenceA (x :* xs) = (:*) <$> x <*> sequenceA xs

-- Didn't figure out how to do it with this definition :(
--  traverse _ Nil = pure Nil --   this vvv is what I was missing
--  traverse f (x :* xs) = (:*) <$> f x <*> (traverse f xs)
    --((f x) :* (traverse f xs))

-- Exercise T5. [GADTs]
--
-- Define 'unzip' for 'Vec'.

unzip :: Vec n (a, b) -> (Vec n a, Vec n b)
unzip Nil = (Nil, Nil)
unzip ((x,y) :* xys) = ((x :* (fst (unzip xys))), (y :* (snd (unzip xys))))


-- Exercise T6. [GADTs]
--
-- Consider the type 'Fin' below. Observe that 'Fin n' has 'n' inhabitants.
--
-- Define '(!!) :: Vec n a -> Fin n -> a'.
--
-- Recall that 'Data.List.findIndex :: (a -> Bool) -> [a] -> Maybe Int'.
-- Write a version of 'findIndex' for Vec.
--
-- Write a function 'update' for Vec, which takes a 'Fin n' and a function of
-- type 'a -> a', and applies the function to the nth element of the vector.

-- Cyclic group
data Fin :: Nat -> Type where
  FZero :: Fin (Suc n)
  FSuc  :: Fin n -> Fin (Suc n)

(!!) :: Vec n a -> Fin n -> a
(!!) (x:*_) FZero = x
(!!) (_:*xs) (FSuc n) = xs !! n
(!!) Nil n = case n of {}

vecFindIndex :: (a -> Bool) -> Vec n a -> Maybe (Fin n)
vecFindIndex _ Nil = Nothing
vecFindIndex f (x :* xs) | f x = Just FZero
                         | otherwise = FSuc <$> vecFindIndex f xs

update :: Vec n a -> Fin n -> (a -> a) -> Vec n a
update (x:*xs) FZero f = (f x) :* xs
update (x:*y:*xs) (FSuc (FZero)) f = x :* (f y) :* xs
update (x:*xs) (FSuc (FSuc n)) f = x:* (update xs (FSuc n) f)
update Nil n _ = case n of {}



-- deriving instance Enum (Fin m) => Enum (Vec n (Fin m))























-- Exercise T7. [GADTs]
--
-- The following datatype represents well-typed expressions. Define a function
-- 'eval :: Expr a -> a' to evaluate an expression.

data Expr :: Type -> Type where
  Int  :: Int  -> Expr Int
  Bool :: Bool -> Expr Bool
  Add  :: Expr Int -> Expr Int -> Expr Int
  Leq  :: Expr Int -> Expr Int -> Expr Bool
  If   :: Expr Bool -> Expr a -> Expr a -> Expr a

deriving instance Show (Expr a)

exExpr :: Expr Bool
exExpr = If (Leq (Int 4) (Add (Int 2) (Int 1))) (Bool False) (Leq (Int 0) (Int 1))

-- Works!

eval :: Expr a -> a
eval (Int b)   = b
eval (Bool b)  = b
eval (Add a b) = (eval a) + (eval b)
eval (Leq a b) = (eval a) <= (eval b)
eval (If a e1 e2) = if (eval a) then (eval e1) else (eval e2)



































-- Exercise T8. [GADTs]
--
-- Define a type-safe version of 'printf :: Format f -> f -> String', by first
-- defining a GADT 'Format f' representing format strings that expect parameters
-- of type 'f'.
-- Note: Not supposed to be a variadic printf

-- data Format f :: Empty | String f


-- Exercise T9. [Type families]
--
-- Define a type family corresponding to 'minimum' (on lists or vectors,
-- whichever you prefer).


-- type family Minimum' (x :: Nat) (xs :: Vec n Nat) :: Nat


-- minimum :: Ord a => Vec (Suc n) a -> a
-- minimum (x :* Nil) = x
-- minimum (x :* y :* xs) | x < minimum (y :* xs) = x
--                        | otherwise             = minimum (y :* xs)


-- Exercise T10. [GADTs, type families]
--
-- Write a function 'interleave' that takes two vectors of the same length and
-- returns a function of twice the length, taking elements from each vector in
-- turn.  For example:
--
-- >>> interleave ('a' :* 'b' :* Nil) ('c' :* 'd' :* Nil)
-- 'a' :* ('c' :* ('b' :* ('d' :* Nil)))

-- Exercise T11. [GADTs, type families]
--
-- Define a type family 'Vect (n :: Nat) (a :: Type) :: Type' that corresponds
-- to 'Vec'.  How does this representation compare to the GADT representation?

-- Exercise T12. [singletons, existential types]
--
-- The type 'Some' is a general-purpose existential type.
--
-- Show that 'Nat' and 'Some SNat' are isomorphic (i.e. define mutually inverse
-- functions to convert between them).

data Some (f :: k -> Type) where
  This :: f x -> Some f

-- Exercise T13. [GADTs, singletons, type families]
--
-- Define 'take' and/or 'drop' on vectors.

-- Exercise T14. [GADTs]
--
-- Define a datatype of perfect(ly) balanced binary trees,
-- indexed by their height.
--
-- Define / derive 'Show' and 'Functor' instances for this type.
-- Define a function that reverses a perfect tree.

-- Exercise T15. [GADTs, existential types]
--
-- Define a "normal" datatype of binary trees. Define a
-- function that checks whether a binary tree is perfect,
-- and produces the perfect tree as a witness on success.

-- Exercise T16. [GADTs, existential types, advanced]
--
-- Define a datatype of untyped expressions corresponding to 'Expr' above. Write
-- a type checker that takes an untyped expression and returns an 'Expr'
-- together with its type.

-- Exercise T17. [GADTs, constraint families]
--
-- Consider the 'HList' type below, which represents heterogeneous lists,
-- indexed by a type-level list of element types. Give it a 'Show' instance by
-- writing down a type family returning the required constraints.
--
-- You will need to use an explicit tick '[] for the promoted empty list data
-- constructor, because [] in types represents the list type constructor.
-- Similarly [Int] means "the type of lists of integers" while '[Int] means "the
-- type-level list of types containing a single element Int".  You can write
-- (x : xs) or (x ': xs) for the promoted cons constructor.

data HList :: [Type] -> Type where
  HNil :: HList '[]
  HCons :: a -> HList as -> HList (a : as)

type T = [Int, Bool, Char]

hlist :: HList T
hlist = HCons 3 (HCons True (HCons 'x' HNil))

-- A frequently more useful type is 'Env', which generalises 'HList' over an
-- arbitrary type constructor. How can you instantiate 'f' so that 'Env f' is
-- isomorphic to 'HList'?

--

-- Define 'Eq' and 'Show' instances for 'Env'.
-- What does 'Env Fin' represent?

data Env (f :: k -> Type) (as :: [k]) :: Type where
  ENil  :: Env f '[]
  ECons :: f a -> Env f as -> Env f (a : as)





-- Exercise T18. [Type families, dependent types]

--

-- Write a type family 'Length' that returns the length of a type-level list,

-- and a type family 'ListToVector' that takes a type-level list and returns a

-- vector of the corresponding 'Length'.





-- Exercise T19. [Theorem proving, advanced]

--

-- Here is a definition of 'reverse' from the slides:



type PlusZero n   = (n + Zero)   ~ n

type PlusSuc p q  = (p + Suc q)  ~ Suc (p + q)



type family Lemma (m :: Nat) (n :: Nat) :: Constraint where

  Lemma (Zero)  n =  ()

  Lemma (Suc m) n =  (PlusSuc m n, Lemma m (Suc n))



reverse :: (PlusZero n, Lemma n Zero) => Vec n a -> Vec n a

reverse ys = go ys Nil

  where

    go :: Lemma p q => Vec p a -> Vec q a -> Vec (p + q) a

    go Nil        acc = acc

    go (x :* xs)  acc = go xs (x :* acc)



-- The type 'Dict c' makes it possible to write functions that take and return

-- constraint dictionaries.  For example, 'Dict (m ~ n)' is a proof that 'm' and

-- 'n' are equal.

--

-- Implement 'lemma' and test that 'reverseN' behaves as expected.



data Dict c where

  MkDict :: c => Dict c



lemma :: SNat n -> Dict (PlusZero n, Lemma n Zero)

lemma = undefined



length :: Vec n a -> SNat n

length Nil        = SZero

length (_ :* xs)  = SSuc (length xs)



reverseN :: Vec n a -> Vec n a

reverseN xs = case lemma (length xs) of

                MkDict -> reverse xs





-- Exercise T20. [Theorem proving, advanced]
--
-- Define 'rotate :: ... => Vec a (Suc n) -> Vec a (Suc n)' that rotates a
-- vector by moving the first element into last position, filling in the context
-- appropriately.
--
-- Prove commutativity of addition of natural numbers, i. e.  that 'm + n ~ n + m'
-- (or, somewhat easier: 'm + 1 ~ 1 + m').  Hence define 'rotate' without an
-- equality constraint on 'n'.





-- Exercise T21. [GADTs, equality constraints]
--
-- The module Data.Type.Equality defines:
--
--     data (a :: k) :~: (b :: k) where
--       Refl :: a :~: a
----
-- Show that 'a :~: b' is isomorphic to 'Dict (a ~ b)'.





-- Data.Type.Equality also defines:
--
--     class TestEquality (f :: k -> Type) where
--       testEquality :: f a -> f b -> Maybe (a :~: b)
--
-- This class identifies singleton types that admit (semi)decidable equality.
-- Give an instance of 'TestEquality' for 'SNat'.  Define a singleton type for
-- vectors, with a 'TestEquality' instance.
--
-- (You may use the class as defined in Data.Type.Equality, or define your own
-- version for the 'Dict' representation).





-- Exercise T22. [GADTs, advanced]
--
-- For the following type of untyped expressions:
--
-- data Expr =
--     Int Int
--   | Bool Bool
--   | Add Expr Expr
--   | Leq Expr Expr
--   | If Expr Expr Expr
--   | Var Name
--   | Let Name Expr Expr
--
-- come up with a GADT of well-scoped and well-typed expressions, indexed by the
-- list of types of the variables in scope, and the type of the expression.
-- Write an evaluator for well-typed expressions.
--
-- (If you prefer, a fractionally simpler variant is to define a type of
-- well-scoped expressions, indexed by the number of variables in scope. You can
-- then use 'Fin' for the representation of variables.)





-- Exercise T23. [GADTs, existential types, advanced]
--
-- Write a "type checker" from untyped expressions to well-typed
-- and well-scoped expressions.
