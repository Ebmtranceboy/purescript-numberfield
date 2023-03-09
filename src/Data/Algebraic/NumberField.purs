module Data.Algebraic.NumberField
    (module Data.Algebraic.NumberField) where
        
import Prelude

import Data.Array (init, last, (..), (:), uncons, zipWith, zip, scanl)
import Data.Foldable (foldr, product, sum)
import Data.Maybe (Maybe (..), fromMaybe)
import Data.Map (fromFoldable, lookup)
import Data.Ratio (Ratio)
import Data.Reflectable 
  ( class Reflectable
  , class Reifiable
  , reflectType
  )
import Data.Sparse.Matrix 
    ( Matrix (..)
    , height
    , ringDeterminant
    )
import Data.Sparse.Polynomial 
    ( class Arity
    , class Axed
    , class Divisible
    , class Full
    , class GoSwap
    , class Leadable
    , class Nest
    , class Pad
    , class Peel
    , class Set
    , class Unpad
    , Polynomial
    , (^)
    , (?)
    , (:.)
    , arity'
    , axes
    , fill
    , full
    , goSwap
    , nest
    , pad
    , pow
    , prevAxis
    , set
    , unpad
    )
import Data.Tuple.Nested ((/\))
import Prim.Int (class Add)
import Type.Proxy (Proxy (..))

-- | Builds the https://en.wikipedia.org/wiki/Sylvester_matrix
-- | of two univariate polynomials with coefficients in a commutative ring
sylvester :: forall a. 
  CommutativeRing a => 
  Divisible a => 
  Eq a =>  
  Leadable a => 
  Polynomial a -> Polynomial a -> Matrix a
sylvester p p' =
  let d = degree p
      d' = degree p'
      q = p^0
      q' = p'^0
      dim = d + d'
  in 
    Matrix 
      { height: dim
      , width: dim
      , coefficients:
        foldr 
          (\n acc -> acc + q * pow (one^1^1) n) 
          zero 
          (0..(d'-1)) +
        foldr 
          (\n acc -> acc + q' * pow (one^0^1) (d'+n) * pow (one^1^0) n) 
          zero 
          (0..(d-1))
      }

-- | Builds the minimal polynomial whose root(s)
-- | is (are) the sum of the roots of each of
-- | the polynomials listed in the array
extensionBySum :: forall a. 
  CommutativeRing a =>
    Divisible a => 
    Eq a => 
    Leadable a => 
    Ord a =>
    Ring a => 
    Array (Polynomial a) -> Polynomial a

extensionBySum arr = 
  let extensionBySum2 p1 p2 =
        let up = nest (Proxy :: _ 1)
        in ringDeterminant $ 
          sylvester (up p1) ((one^1^0 - one^0^1) `fill (Proxy :: _ 0)` (up p2))
      extensionBySums ps = 
        case uncons ps of
            Just { head: h1, tail } ->
                case uncons tail of
                     Just { head: h2, tail: ts } -> 
                        extensionBySums (extensionBySum2 h1 h2 : ts)
                     _ -> h1
            _ -> zero
    in extensionBySums arr

-- | Computes the reciprocal of the second polynomial
-- | with the help of the previously computed 
-- | https://en.wikipedia.org/wiki/Resultant between
-- | that polynomial and the minimal polynomial 
-- | of the extension
cayley :: forall a.
  Divisible a => 
  Eq a => 
  EuclideanRing a => 
  Leadable a => 
  Peel a a => 
  Polynomial a -> Polynomial a -> Polynomial a

cayley r qa =
  let r0 = (r ? 0) ^ 0
  in - (qa `fill (Proxy :: _ 0)` ((r - r0) / (one ^ 1))) / r0

-- | Computes the reciprocal of the first polynomial
-- | in the extension whose minimal polynomial 
-- | is provided by the second polynomial
reciprocal ::  forall n n1 n2 a r. 
  Add n2 1 n1 => 
  Add n1 1 n => 
  Arity a n => 
  Divisible r => 
  Eq r => 
  EuclideanRing r => 
  Leadable r => 
  Ord r =>
  Pad n2 (Polynomial r) a => 
  Peel r r => 
  Unpad n2 (Polynomial r) a => 
  a -> a -> a
  
reciprocal _m _mu =
  let m' = arity' _m
      m = unpad (prevAxis $ prevAxis m') _m
      mu = unpad (prevAxis $ prevAxis m') _mu
      up = nest (Proxy :: _ 1)
  in pad (prevAxis $ prevAxis m') $ 
    cayley (ringDeterminant (sylvester (up mu) (one^1^0 - up m))) m

newtype Framework a = Framework
  { primitiveExpressions :: Array (Polynomial a)
  , minimal :: Polynomial a
  , primitiveSubstitution :: Polynomial a -> Polynomial a
  , lift :: a -> Polynomial a
  , unlift :: Polynomial a -> a
  , rawModuli :: Array (Polynomial a)
  , value :: a
  }
  
-- | Computes the required quantities needed to 
-- | perform computations with algebraic extensions 
-- | in the field of rational numbers
framework :: forall r a n1 n2 n3. 
  Add n3 1 n2 =>
  Add n2 1 n1 =>
  Arity (Polynomial (Polynomial a)) n1 => 
  Axed a r => 
  CommutativeRing a =>
  CommutativeRing r =>
  Divisible a => 
  Divisible r =>
  DivisionRing r =>
  Full n2 (Polynomial a) => 
  GoSwap 0 n1 (Polynomial a) =>
  Leadable a => 
  Leadable r  =>
  Nest n2 (Polynomial a) =>
  Ord a => 
  Ord r =>
  Pad n3 (Polynomial r) (Polynomial (Polynomial a)) =>
  Pad n2 (Polynomial r) (Polynomial (Polynomial (Polynomial a))) =>
  Peel a r => 
  Set n2 r (Polynomial a) =>
  Unpad n3 (Polynomial r) (Polynomial (Polynomial a)) =>
  Polynomial a -> Array (Polynomial r) -> Framework (Polynomial a)
    
framework uno arr =
  let _ /\ axs' = axes (uno^0)
      axs = fromMaybe [] $ init axs'
      var = fromMaybe (uno^0) $ last axs'
      var' = arity' var
      ready = (goSwap (Proxy :: _ 0) var' <<< pad (prevAxis var')) <$> arr
      ms = zipWith (:.) ready axs
      ds = degree <$> ready
      d = product $ ds
      s = sum axs
      powers = (\n -> pow s n) <$> 0..(d-1)
      coefs = 
        zip 
          ((\p -> foldr (\m acc -> acc `mod` m) p ms) <$> powers) 
          (0..(d-1))
      scale = fromFoldable $ zip axs $ scanl (*) 1 (1:ds)
      convert (pol /\ x) = 
        let new = (\axe -> pow var (fromMaybe 0 $ lookup axe scale)) <$> axs
        in (_ ^ x) $ unpad (prevAxis $ prevAxis var') $ 
            new `full` pol
      
      base =
        recip $ 
          Matrix 
            { height: d
            , width: d
            , coefficients: sum (convert <$> coefs) 
            }

      primitiveExpressions = (\ icol -> 
          let Matrix column = 
                base * 
                  Matrix
                    { height: height base
                    , width: 1
                    , coefficients: one^icol^0
                    }
          in pad (prevAxis $ prevAxis var') $ 
              zero `set (Proxy :: _ 0)` column.coefficients ) <$> 
                (fromMaybe [] $ init $ scanl (*) 1 (1:ds))

      minimal = pad (prevAxis $ prevAxis var') $ extensionBySum arr
      primitiveSubstitution = fill (prevAxis var') s
      lift = nest (prevAxis var')
      unlift = set (prevAxis var') zero
      rawModuli = ms
      value = zero
        
  in Framework
    { primitiveExpressions
    , minimal
    , primitiveSubstitution
    , lift
    , unlift
    , rawModuli
    , value
    }

instance Reifiable (Framework (Polynomial (Ratio a)))
else instance 
  ( Reifiable (Framework a)
  ) => Reifiable (Framework (Polynomial a))

run :: forall a. Framework (Polynomial a) -> Polynomial a
run (Framework a) = a.value

newtype Extension :: forall k. k -> Type -> Type
newtype Extension f a = Extension a

element :: forall f a. 
  Eq a => Semiring a => a -> Extension f (Framework a)
element v = Extension $ Framework
    { primitiveExpressions: []
    , minimal: zero
    , primitiveSubstitution: identity
    , lift: (_ ^ 0)
    , unlift: (_ ? 0)
    , rawModuli: []
    , value: v
    }
    
build :: forall proxy a f. (proxy -> Extension f a) -> proxy -> a
build x = (\ (Extension a) -> a) <<< x

minimalPolynomial :: forall a. Framework a -> Polynomial a
minimalPolynomial (Framework f) = f.minimal

toPrimitive :: forall a. Framework a -> Array (Polynomial a)
toPrimitive (Framework f) = f.primitiveExpressions

type Expression :: forall k. k -> Type -> Type
type Expression f a = Reflectable f (Framework a) =>
  Proxy f -> Extension (Proxy f) (Framework a)

normalize :: forall f a n n1.
  Add n1 1 n =>
  Arity (Polynomial (Polynomial a)) n =>
  Divisible a =>
  Eq a =>
  EuclideanRing a =>
  Full n1 (Polynomial a) =>
  Leadable a =>
  Reflectable f (Framework (Polynomial a)) =>
  Polynomial a -> Extension (Proxy f) (Framework (Polynomial a))
normalize a = 
  Extension
    ( let Framework fw = reflectType (Proxy :: _ f)
      in 
        Framework fw 
          { value = 
            fw.unlift $ foldr (\m acc -> acc `mod` m) 
              (fw.primitiveSubstitution $ 
              (fw.primitiveExpressions `full` fw.lift a) 
                `mod` fw.minimal
                )  fw.rawModuli
          }
    )

instance
  ( Add n1 1 n
  , Arity (Polynomial (Polynomial a)) n
  , Divisible a
  , Eq a
  , EuclideanRing a
  , Full n1 (Polynomial a)
  , Leadable a
  , Reflectable f (Framework (Polynomial a))
  ) => Semiring (Extension (Proxy f) (Framework (Polynomial a))) where
  add (Extension (Framework a)) (Extension (Framework b)) = 
    normalize (a.value + b.value)
  mul (Extension (Framework a)) (Extension (Framework b)) = 
    normalize (a.value * b.value)
  one = normalize one
  zero = normalize zero

instance 
  ( Add n1 1 n
  , Arity (Polynomial (Polynomial a)) n
  , Divisible a
  , Eq a
  , EuclideanRing a
  , Full n1 (Polynomial a)
  , Leadable a
  , Reflectable f (Framework (Polynomial a))
  ) => Ring (Extension (Proxy f) (Framework (Polynomial a))) where
  sub (Extension (Framework a)) (Extension (Framework b)) = 
    normalize (a.value - b.value)

instance 
  ( Add n 1 m1
  , Add m1 1 m
  , Arity (Polynomial (Polynomial a)) m 
  , Divisible a
  , Divisible r
  , Eq a
  , Eq r
  , EuclideanRing a
  , EuclideanRing r
  , Full m1 (Polynomial a)
  , Leadable a
  , Leadable r
  , Ord r
  , Pad n (Polynomial r) (Polynomial (Polynomial a))
  , Peel r r
  , Reflectable f (Framework (Polynomial a))
  , Unpad n (Polynomial r) (Polynomial (Polynomial a))
  ) => DivisionRing (Extension (Proxy f) (Framework (Polynomial a))) where
  recip (Extension (Framework a)) = 
    Extension
    ( let Framework fw = reflectType (Proxy :: _ f)
      in 
        Framework fw 
          { value = 
              fw.unlift $ foldr (\m acc -> acc `mod` m) 
                (fw.primitiveSubstitution $ 
                  (reciprocal 
                      ((fw.primitiveExpressions `full` fw.lift a.value) 
                        `mod` fw.minimal)
                      fw.minimal
                  ) `mod` fw.minimal
                ) fw.rawModuli
          }
    )
