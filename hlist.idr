import Data.Fin
% default total
namespace HList
  infixr 7 ::
  data HList : List Type -> Type where
    HNil : HList []
    (::) : t -> HList ts -> HList (t :: ts)
  
hcons :  t  -> HList ts -> HList (t :: ts)
hcons x xs = x :: xs

pTakeEmpty : {a: Type} -> (n: Nat) -> take n ([] {elem = a}) = ([] {elem = a})
pTakeEmpty Z = Refl
pTakeEmpty (S m) = Refl

take : (n: Nat) -> HList ts -> HList (take n ts)
take n HNil = rewrite pTakeEmpty n {a = Type} in HNil
take Z xs = HNil
take (S m) (x :: xs) = x :: (take m xs)

take' : (n: Nat) -> HList ts -> {auto p : n `lte` (length ts) = True} -> HList (take n ts)
take' Z _ = HNil
take' (S m) HNil = HNil -- impossible, but not proven to be so
take' (S m) (x :: xs) = x :: (take m xs)
