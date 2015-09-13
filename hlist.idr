module HList
import Data.Fin
% default total

infixr 7 ::
data HList : List Type -> Type where
  Nil : HList []
  (::) : t -> HList ts -> HList (t :: ts)
  
hcons :  t  -> HList ts -> HList (t :: ts)
hcons x xs = x :: xs

pTakeEmpty : {a: Type} -> (n: Nat) -> take n ([] {elem = a}) = ([] {elem = a})
pTakeEmpty Z = Refl
pTakeEmpty (S m) = Refl

take : (n: Nat) -> HList ts -> HList (take n ts)
take n Nil = rewrite pTakeEmpty n {a = Type} in Nil
take Z xs = Nil
take (S m) (x :: xs) = x :: (take m xs)

take' : (n: Nat) -> HList ts -> {auto p : n `lte` (length ts) = True} -> HList (take n ts)
take' Z _ = Nil
take' (S m) Nil = Nil -- impossible, but not proven to be so
take' (S m) (x :: xs) = x :: (take m xs)

infixr 0 ~~>
data (~~>) : (Type -> Type) -> (Type -> Type) -> Type where
  MkPoly : ((a: Type) -> (f a -> g a)) -> f ~~> g

applyPoly: {a: Type} -> (f ~~> g) -> f a -> g a
applyPoly {a = a} (MkPoly f) = (\fa => f a fa)

data Mapper : ply -> List Type -> List Type -> Type where
  NilMapper : Mapper (f ~~> g) [] []
  ConsMapper : Mapper (f ~~> g) ts ts' -> Mapper (f ~~> g) ((f a) :: ts) ((g a) :: ts')

listIntBoolMaybePrf : Mapper (List ~~> Maybe) [List Int, List Bool] [Maybe Int, Maybe Bool]
listIntBoolMaybePrf = ConsMapper (ConsMapper NilMapper)

maybeIntBoolMaybePrf : Mapper (Maybe ~~> Maybe) [Maybe Int, Maybe Bool] [Maybe Int, Maybe Bool]
maybeIntBoolMaybePrf = ConsMapper (ConsMapper NilMapper)

map' : (f ~~> g) -> HList ts -> Mapper (f ~~> g) ts ts' -> HList ts'
map' _ _ NilMapper = Nil
map' f (x :: xs) (ConsMapper y) = (applyPoly f x) :: (map' f xs y)

map : (f ~~> g) -> HList ts -> {default tactics { search } prf : Mapper (f ~~> g) ts ts'} -> HList ts'
map f xs {prf} = map' f xs prf
