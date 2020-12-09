import Data.List

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

VariableId : Type
VariableId = String

data ElemFirstComponent : a -> List (a, b) -> Type where
   Here : ElemFirstComponent x ((x, _) :: xs)
   There : (later : ElemFirstComponent x xs) -> ElemFirstComponent x (y :: xs)

findType : (vId : VariableId) -> (l: List (VariableId, TyExp)) -> (p : ElemFirstComponent vId l) -> TyExp
findType vId ((vId, ty) :: xs) Here = ty
findType vId (_ :: xs) (There later) = findType vId xs later

data Exp : Bool -> TyExp -> List (VariableId, TyExp) -> Type where
  VarExp : (vId : VariableId) -> {auto p : ElemFirstComponent vId l} -> Exp False (findType vId l p) l
  SingleExp : (v : V t) -> Exp False t l
  PlusExp : (x : Exp a NatTy l) -> (y : Exp b NatTy l) -> Exp (a || b) NatTy l
  IfExp : (cond : Exp a BoolTy l) -> (x : Exp b t l) -> (y : Exp c t l) -> Exp (a || b || c) t l
  ThrowExp : Exp True t l
  CatchExp : (x : Exp a t l) -> (h : Exp b t l) -> Exp (a && b) t l

data Program : List (VariableId, TyExp) -> List (VariableId, TyExp) -> Type where
  EmptyProgram : Program env []

  Declaration : (vId : VariableId) ->
                (exp : Exp b t env) ->
                {auto expExecutable : b = False} ->
                (continuing : Program ((vId, t) :: env) c1) ->
                (Program env ((vId, t) :: c1))

  Assignment : (vId : VariableId) ->
               (exp : Exp b t env) ->
               {auto expExecutable : b = False} ->
               (continuing : Program ((vId, t) :: env) c1) ->
               {auto prf' : Elem (vId, t) env} ->
               (Program env ((vId, t) :: c1))

{-
x<- 3;        -- [x <- 3]
x<- x+1       -- [x <- 4]
y<- x+2       -- [x <- 4, y <- 2]
-}

myEmpty : Program [("y", NatTy), ("x", NatTy), ("x", NatTy)] []
myEmpty = EmptyProgram

yEqualsXPlusTwo : Program [("x", NatTy), ("x", NatTy)] [("y", NatTy)]
yEqualsXPlusTwo = Declaration "y" (PlusExp (VarExp "x") (SingleExp (VNat 2))) myEmpty

xEqualsXPlusOne : Program [("x", NatTy)] [("x", NatTy), ("y", NatTy)]
xEqualsXPlusOne = Assignment "x" (PlusExp (VarExp "x") (SingleExp (VNat 1))) yEqualsXPlusTwo

xEquals3 : Program [] [("x", NatTy), ("x", NatTy), ("y", NatTy)]
xEquals3 = Declaration "x" (SingleExp (VNat 3)) xEqualsXPlusOne

data ValuesEnv : List (VariableId, TyExp) -> Type where
   EmptyValuesEnv : ValuesEnv []
   MoreValuesEnv : (vId: VariableId)
                   -> V ty
                   -> ValuesEnv envTy
                   -> ValuesEnv ((vId, ty) :: envTy)

mutual
  evalVarExp : (x : ValuesEnv tEnv) -> (p : ElemFirstComponent vId tEnv)  -> V (findType vId tEnv p)
  evalVarExp (MoreValuesEnv _ val _) Here = val
  evalVarExp (MoreValuesEnv _ _ valueEnv) (There later) = evalVarExp valueEnv later

  evalPlusExp : (x : Exp a NatTy tEnv) -> (y : Exp b NatTy tEnv) -> (valuesEnv : ValuesEnv tEnv) -> (prf : (a || (Delay b)) = False) -> V NatTy
  evalPlusExp x y valuesEnv prf {a = False} {b = False} =
    case eval x valuesEnv of
          (VNat x') => case eval y valuesEnv of
                             (VNat y') => VNat (x' + y')
  evalPlusExp _ _ _ Refl {a = False} {b = True} impossible
  evalPlusExp _ _ _ Refl {a = True} {b = _} impossible

  evalIfExp : (cond : Exp a BoolTy tEnv) -> (x : Exp b t tEnv) -> (y : Exp c t tEnv) -> (valuesEnv : ValuesEnv tEnv) -> (prf : (a || (Delay (b || (Delay c)))) = False) -> V t
  evalIfExp cond x y valuesEnv prf {a = False} {b = False} {c = False} =
    case eval cond valuesEnv of
          VBool True => eval x valuesEnv
          VBool False => eval y valuesEnv
  evalIfExp _ _ _ _ Refl {a = False} {b = False} {c = True} impossible
  evalIfExp _ _ _ _ Refl {a = False} {b = False} {c = True} impossible
  evalIfExp _ _ _ _ Refl {a = True} {b = _} {c = _} impossible

  evalCatchExp : (x : Exp a t tEnv) -> (h : Exp b t tEnv) -> (valuesEnv : ValuesEnv tEnv) ->(prf : (a && (Delay b)) = False) -> V t
  evalCatchExp x h valuesEnv prf {a = False} = eval x valuesEnv
  evalCatchExp x h valuesEnv prf {a = True} {b = False} = eval h valuesEnv
  evalCatchExp _ _ _ Refl {a = True} {b = True} impossible

  eval : (e : Exp b t tEnv) -> (valuesEnv : ValuesEnv tEnv) -> {auto prf : b = False} -> V t
  eval (VarExp vId {p}) valuesEnv = evalVarExp valuesEnv p
  eval (SingleExp v) valuesEnv = v
  eval (PlusExp x y) valuesEnv {prf} = evalPlusExp x y valuesEnv prf
  eval (IfExp cond x y) valuesEnv {prf} = evalIfExp cond x y valuesEnv prf
  eval ThrowExp _ {prf = Refl} impossible
  eval (CatchExp x h) valuesEnv {prf}= evalCatchExp x h valuesEnv prf


evPro : (p : Program env env') -> (valueEnv : ValuesEnv env) -> ValuesEnv env'
evPro EmptyProgram valueEnv = EmptyValuesEnv
evPro (Declaration vId exp continuing) valueEnv =
  let evaluated = eval exp valueEnv in
  MoreValuesEnv vId evaluated
    (evPro continuing (MoreValuesEnv vId evaluated valueEnv))
evPro (Assignment vId exp continuing) valueEnv =
  let evaluated = eval exp valueEnv in
  MoreValuesEnv vId evaluated
    (evPro continuing (MoreValuesEnv vId evaluated valueEnv))

evalProgram : (p : Program [] env') -> ValuesEnv env'
evalProgram p = evPro p EmptyValuesEnv

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

mutual
  compCatchVarExp : (valueEnv : ValuesEnv env) -> (p : ElemFirstComponent vId env) -> (c : Code ((Val (findType vId env p)) :: (s'' ++ ((Han s s') :: s))) s') -> Code (s'' ++ ((Han s s') :: s)) s'
  compCatchVarExp (MoreValuesEnv _ x _) Here c = PUSH x c
  compCatchVarExp (MoreValuesEnv _ _ y) (There later) c = compCatchVarExp y later c

  compCatch : (exp : Exp b ty env) -> (valueEnv : ValuesEnv env) -> (c : Code (Val ty :: (s'' ++ (Han s s') :: s)) s') -> Code (s'' ++ (Han s s') :: s) s'
  compCatch (VarExp vId {p}) valueEnv c = compCatchVarExp valueEnv p c
  compCatch (SingleExp v) valueEnv c = PUSH v c
  compCatch (PlusExp x y) valueEnv c =
    compCatch x valueEnv (compCatch {s'' = Val NatTy :: _} y valueEnv (ADD c))
  compCatch (IfExp cond x y) valueEnv c =
    compCatch cond valueEnv (IF (compCatch x valueEnv c) (compCatch y valueEnv c))
  compCatch ThrowExp valueEnv c = THROW
  compCatch (CatchExp x h) valueEnv c =
    MARK (compCatch h valueEnv c) (compCatch {s'' = []} x valueEnv (UNMARK c))

  compPlusExp : (prf : (a || (Delay b)) = False) -> (x : Exp a NatTy env) ->  (y : Exp b NatTy env) -> (valueEnv : ValuesEnv env) -> (c : Code ((Val NatTy) :: s) s')  -> Code s s'
  compPlusExp prf x y valueEnv c {a = False} {b = False} =
    (comp Refl x valueEnv (comp Refl y valueEnv (ADD c)))
  compPlusExp Refl _ _ _ _ {a = False} {b = True} impossible
  compPlusExp Refl _ _ _ _ {a = True} {b = _} impossible

  compIfExp :
    (prf : (a || (Delay (b || (Delay c)))) = False) -> (cond : Exp a BoolTy env) ->
    (x : Exp b ty env) -> (y : Exp c ty env) -> (valueEnv : ValuesEnv env) ->
    (co : Code ((Val ty) :: s) s') -> Code s s'
  compIfExp prf cond x y valueEnv co {a = False} {b = False} {c = False} =
    comp Refl cond valueEnv (IF (comp Refl x valueEnv co) (comp Refl y valueEnv co))
  compIfExp Refl _ _ _ _ _ {a = False} {b = False} {c = True} impossible
  compIfExp Refl _ _ _ _ _ {a = False} {b = True} {c = _} impossible
  compIfExp Refl _ _ _ _ _ {a = True} {b = _} {c = _} impossible

  compCatchExp :
    (prf : (a && (Delay b)) = False) -> (x : Exp a ty env) -> (h : Exp b ty env) ->
    (valueEnv : ValuesEnv env) -> (c : Code ((Val ty) :: s) s') -> Code s s'
  compCatchExp prf x h valueEnv c {a = False} =
    comp Refl x valueEnv c
  compCatchExp prf x h valueEnv c {a = True} {b = False} =
    MARK (comp Refl h valueEnv c) (compCatch {s'' = []} x valueEnv (UNMARK c))
  compCatchExp Refl _ _ _ _ {a = True} {b = True} impossible

  compVarExp : (valueEnv : ValuesEnv env) -> (p : ElemFirstComponent vId env) -> (c : Code ((Val (findType vId env p)) :: s) s') -> Code s s'
  compVarExp (MoreValuesEnv _ x _) Here c = PUSH x c
  compVarExp (MoreValuesEnv _ _ y) (There later) c = compVarExp y later c

  comp : (prf : b = False) -> (exp : Exp b ty env) -> (valueEnv : ValuesEnv env) -> Code (Val ty :: s) s' -> Code s s'
  comp prf (VarExp vId {p}) valueEnv c = compVarExp valueEnv p c
  comp prf (SingleExp v) valueEnv c = PUSH v c
  comp prf (PlusExp x y) valueEnv c = compPlusExp prf x y valueEnv c
  comp prf (IfExp cond x y) valueEnv co = compIfExp prf cond x y valueEnv co
  comp prf (CatchExp x h) valueEnv c = compCatchExp prf x h valueEnv c
  comp Refl ThrowExp _ _ impossible

compile : {auto prf : b = False} -> (exp : Exp b ty env) -> (valueEnv : ValuesEnv env) -> Code s (Val ty :: s)
compile exp valueEnv {prf = Refl} = comp Refl exp valueEnv HALT

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

{-
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

e1 : Exp False NatTy l
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
-}
