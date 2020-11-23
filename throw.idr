%default total

data TyExp = NatTy | BoolTy

mutual
  StackType : Type
  StackType = List Ty

  data Ty = Han StackType StackType | Val TyExp

data V : TyExp -> Type where
  VNat : Nat -> V NatTy
  VBool : Bool -> V BoolTy

Eq (V t) where
  (==) (VNat x) (VNat y) = x == y
  (==) (VBool x) (VBool y) = x == y

data Exp : Bool -> TyExp -> Type where
  SingleExp : (v : V t) -> Exp False t
  PlusExp : (x : Exp a NatTy) -> (y : Exp b NatTy) -> Exp (a || b) NatTy
  IfExp : (cond : Exp a BoolTy) -> (x : Exp b t) -> (y : Exp c t) -> Exp (a || b || c) t
  ThrowExp : Exp True t
  CatchExp : (x : Exp a t) -> (h : Exp b t) -> Exp (a && b) t


mutual
  evalPlusExp : (p : (a || (Delay b)) = False) -> (x : Exp a NatTy) -> (y : Exp b NatTy) -> V NatTy
  evalPlusExp {a = False} {b = False} p x y =
    case eval Refl x of
          VNat x' => case eval Refl y of
                             VNat y' => VNat (x' + y')
  evalPlusExp {a = True} {b = _} Refl _ _ impossible
  evalPlusExp {a = False} {b = True} Refl _ _ impossible

  evalIfExp : (p : (a || (Delay (b || (Delay c)))) = False) -> (cond : Exp a BoolTy) -> (x : Exp b t) -> (y : Exp c t) -> V t
  evalIfExp {a = False} {b = False} {c = False} p cond x y =
    case eval Refl cond of
      VBool True => eval Refl x
      VBool False => eval Refl y
  evalIfExp {a = False} {b = False} {c = True} Refl _ _ _ impossible
  evalIfExp {a = False} {b = True} {c = _} Refl _ _ _ impossible
  evalIfExp {a = True} {b = _} {c = _} Refl _ _ _ impossible

  evalCatchExp : (p : (a && (Delay b)) = False) -> (x : Exp a t) -> (h : Exp b t) -> V t
  evalCatchExp {a = False} {b} p x h = eval Refl x
  evalCatchExp {a = True} {b = False} p x h = eval Refl h
  evalCatchExp {a = True} {b = True} Refl _ _ impossible

  eval : (b = False) -> Exp b t -> V t
  eval p (SingleExp v) = v
  eval p (PlusExp x y) = evalPlusExp p x y
  eval p (IfExp cond x y) = evalIfExp p cond x y
  eval Refl ThrowExp impossible
  eval p (CatchExp x h) = evalCatchExp p x h

mutual
  El : Ty -> Type
  El (Han t t') = Code t t'
  El (Val NatTy) = Nat
  El (Val BoolTy) = Bool

  data Code : (s : StackType) -> (s' : StackType) -> Type where
    PUSH : V tyExp -> Code (Val tyExp :: s) s' -> Code s s'
    ADD : Code (Val NatTy :: s) s' -> Code (Val NatTy :: Val NatTy :: s) s'
    IF : (c1 : Code s s') -> (c2 : Code s s') -> Code (Val BoolTy :: s) s'
    THROW : Code (s'' ++ (Han s s') :: s) s'
    MARK : (h : Code s s') -> (c : Code ((Han s s') :: s) s') -> Code s s'
    UNMARK : Code (t :: s) s' -> Code (t :: (Han s s') :: s) s'
    HALT : Code s s

--comp?
compCatch : Exp b ty -> Code (Val ty :: (s'' ++ (Han s s') :: s)) s' -> Code (s'' ++ (Han s s') :: s) s'
compCatch (SingleExp v) c = PUSH v c
compCatch (PlusExp x y) c = compCatch x (compCatch {s'' = Val NatTy :: _} y (ADD c))
compCatch {s} {s''} (IfExp cond x y) c = compCatch cond (IF (compCatch x c) (compCatch y c))
compCatch ThrowExp c = THROW
compCatch (CatchExp x h) c = MARK (compCatch h c) (compCatch {s'' = []} x (UNMARK c))


mutual
  compPlusExp : (p : (a || b) = False) -> (x : Exp a NatTy) ->  (y : Exp b NatTy) -> (c : Code ((Val NatTy) :: s) s') -> Code s s'
  compPlusExp {a = False} {b = False} Refl x y c =
    comp Refl x (comp Refl y (ADD c))
  compPlusExp {a = False} {b = True} Refl _ _ _ impossible
  compPlusExp {a = True} {b = _} Refl _ _ _ impossible

  compCatchExp : (p : (a && b) = False) -> (x : Exp a ty) -> (h : Exp b ty) -> (c : Code ((Val ty) :: s) s') -> Code s s'
  compCatchExp {a = False} Refl x h c =
    comp Refl x c
  compCatchExp {a = True} {b = False} p x h c =
    MARK (comp Refl h c) (compCatch {s'' = []} x (UNMARK c))
  compCatchExp {a = True} {b = True} Refl _ _ _ impossible

  compIfExp : (p : (a || b || c) = False) -> (cond : Exp a BoolTy) ->(x : Exp b ty) -> (y : Exp c ty) -> (co : Code ((Val ty) :: s) s') -> Code s s'
  compIfExp {a = False} {b = False} {c = False} Refl cond x y co =
     comp Refl cond (IF (comp Refl x co) (comp Refl y co))
  compIfExp {a = False} {b = False} {c = True} Refl _ _ _ _ impossible
  compIfExp {a = False} {b = False} {c = True} Refl _ _ _ _ impossible
  compIfExp {a = True} Refl _ _ _ _ impossible

  comp : (b = False) -> Exp b ty -> Code (Val ty :: s) s' -> Code s s'
  comp p (SingleExp v) c = PUSH v c
  comp p (PlusExp x y) c = compPlusExp p x y c
  comp p (IfExp cond x y) co = compIfExp p cond x y co
  comp p (CatchExp x h) c = compCatchExp p x h c
  comp Refl ThrowExp _ impossible

compile : (b = False) -> Exp b ty -> Code s (Val ty :: s)
compile p e = comp p e HALT

data Stack : (s : StackType) -> Type where
  Nil : Stack []
  (::) : El t -> Stack s -> Stack (t :: s)

top : Stack (t :: s) -> El t
top (t :: s) = t

mutual
  partial
  exec : Code s s' -> Stack s -> Stack s'
  exec (PUSH (VNat x) c) s = exec c (x :: s)
  exec (PUSH (VBool x) c) s = exec c (x :: s)
  exec (ADD c) (m :: n :: s) = exec c ((n + m) :: s)
  exec (IF c1 c2) (True :: s) = exec c1 s
  exec (IF c1 c2) (False :: s) = exec c2 s
  exec THROW s = fail s
  exec (MARK h c) s = exec c (h :: s)
  exec (UNMARK c) (x :: h :: s) = exec c (x :: s)
  exec HALT s = s

  partial
  fail : Stack (s'' ++ Han s s' :: s) -> Stack s'
  fail {s'' = []} (h' :: s) = exec h' s
  fail {s'' = (_ :: _)} (_ :: s) = fail s

partial
testExp : (t = False) -> Exp t tyExp -> V tyExp -> Bool
testExp Refl e (VNat n) =
  let t1 = eval Refl e == (VNat n) in
  let t2 = top (exec (compile Refl e) []) == n in
  t1 && t2
testExp Refl e (VBool b) =
  let t1 = eval Refl e == (VBool b) in
  let t2 = top (exec (compile Refl e) []) == b in
  t1 && t2

partial
checkAll : List (Exp False tyExp, V tyExp) -> Bool
checkAll [] = True
checkAll ((e, r) :: xs) = (testExp Refl e r) && checkAll xs

e1 : Exp False NatTy
e1 = CatchExp ThrowExp (PlusExp (SingleExp (VNat 2)) (SingleExp (VNat 3)))
r1 : V NatTy
r1 = VNat 5

e2 : Exp False NatTy
e2 = CatchExp (PlusExp (SingleExp (VNat 60)) ThrowExp)
              (SingleExp (VNat 30))
r2 : V NatTy
r2 = VNat 30

e3 : Exp False NatTy
e3 = SingleExp (VNat 3)
r3 : V NatTy
r3 = VNat 3

-- checkAll [(e1, r1), (e2, r2), (e3, r3)]

---
s : Stack [Val NatTy]
s = 123 :: Nil

t : Stack[Val BoolTy, Val NatTy]
t = False :: s
