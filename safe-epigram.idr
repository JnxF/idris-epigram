%default total

data TyExp = Nat | Bool

data Val : TyExp -> Type where
  ValNat : Nat -> Val Nat
  ValBool : Bool -> Val Bool

data Exp : TyExp -> Type where
  SingleExp : Val t -> Exp t
  PlusExp : Exp Nat -> Exp Nat -> Exp Nat
  IfExp : Exp Bool -> Exp t -> Exp t -> Exp t

addValNats : Val Nat -> Val Nat -> Val Nat
addValNats (ValNat a) (ValNat b) = ValNat (a + b)

eval : Exp t -> Val t
eval (SingleExp v) = v
eval (PlusExp e1 e2) = addValNats (eval e1) (eval e2)
eval (IfExp b e1 e2) = case eval b of
                            ValBool True => eval e1
                            ValBool False => eval e2

data Stack : (s : List TyExp) -> Type where
  Nil : Stack []
  (::) : Val t -> Stack s -> Stack (t :: s)

top : Stack (t :: s) -> Val t
top (v :: s) = v

data Code : (s : List TyExp) -> (s' : List TyExp) -> Type where
  Skip : Code s s
  (++) : Code s0 s1 -> Code s1 s2 -> Code s0 s2
  PUSH : Val t -> Code s (t :: s)
  ADD : Code (Nat :: Nat :: s) (Nat :: s)
  IF : (c1 : Code s s') -> (c2 : Code s s') -> Code (Bool :: s) s'

exec : (c : Code s s') -> Stack s -> Stack s'
exec Skip s = s
exec (c1 ++ c2) s = exec c2 (exec c1 s)
exec (PUSH v) s = v :: s
exec ADD (n :: (m :: s)) = addValNats n m :: s
exec (IF c1 c2) ((ValBool True) :: s) = exec c1 s
exec (IF c1 c2) ((ValBool False) :: s) = exec c2 s

compile : Exp t -> Code s (t :: s)
compile (SingleExp v) = PUSH v
compile (PlusExp e1 e2) = (compile e2 ++ compile e1) ++ ADD
compile (IfExp b e1 e2) = (compile b) ++ IF (compile e1) (compile e2)

correct : (e : Exp t) -> (ss : Stack s) -> (eval e) :: ss = exec (compile e) ss
correct (SingleExp v) ss = Refl
correct (PlusExp e1 e2) ss =
  let p1 = correct e1 ss in
  let p2 = correct e2 ss in
  ?hole1
correct (IfExp b e1 e2) ss =
  let p1 = correct e1 ss in
  let p2 = correct e2 ss in
  let p3 = correct b ss in
  ?hole2
