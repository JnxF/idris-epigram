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

findType : (id : VariableId) -> (l: List (VariableId, TyExp)) -> (p : ElemFirstComponent id l) -> TyExp
findType id ((id, ty) :: xs) Here = ty
findType id (_ :: xs) (There later) = findType id xs later

data Exp : Bool -> TyExp -> List (VariableId, TyExp) -> Type where
  VarExp : (id : VariableId) -> {auto p : ElemFirstComponent id l} -> Exp False (findType id l p) l
  SingleExp : (v : V t) -> Exp False t l
  PlusExp : (x : Exp a NatTy l) -> (y : Exp b NatTy l) -> Exp (a || b) NatTy l
  IfExp : (cond : Exp a BoolTy l) -> (x : Exp b t l) -> (y : Exp c t l) -> Exp (a || b || c) t l
  ThrowExp : Exp True t l
  CatchExp : (x : Exp a t l) -> (h : Exp b t l) -> Exp (a && b) t l


data Program : List (VariableId, TyExp) -> Type where
  EmptyProgram : Program []
  Statement : (statement : (VariableId, Exp b t env)) ->
              (previous : Program env) ->
              {auto p : b = False} ->
              Program ((fst statement, t) :: env)

data Trace : List (VariableId, TyExp) -> Type where
  EmptyTrace : Trace []
  TraceStep : (V t) -> (id : VariableId) -> (prf: Trace xs) -> Trace ((id, t) :: xs)

mutual
    findVariable : (p : False = False) -> (myProof : ElemFirstComponent id tEnv) -> (env : Trace tEnv) -> V (findType id tEnv myProof)
    findVariable p Here (TraceStep x id prf) = x
    findVariable p (There later) (TraceStep x id prf) = findVariable p later prf

    evalPlusExp : (x : Exp a NatTy tEnv) -> (y : Exp b NatTy tEnv) -> (env : Trace tEnv) ->  (p : (a || (Delay b)) = False) -> V NatTy
    evalPlusExp x y env p {a = False} {b = False} =
      case eval x env of
            (VNat x') => case eval y env of
                               (VNat y') => VNat (x' + y')
    evalPlusExp _ _ _ Refl {a = False} {b = True} impossible
    evalPlusExp _ _ _ Refl {a = True} {b = _} impossible

    evalIfExp : (cond : Exp a BoolTy tEnv) -> (x : Exp b t tEnv) -> (y : Exp c t tEnv) -> (env : Trace tEnv) ->   (p : (a || (Delay (b || (Delay c)))) = False) -> V t
    evalIfExp cond x y env p {a = False} {b = False} {c = False} =
      case eval cond env of
            VBool True => eval x env
            VBool False => eval y env
    evalIfExp _ _ _ _ Refl {a = False} {b = False} {c = True} impossible
    evalIfExp _ _ _ _ Refl {a = False} {b = True} {c = _} impossible
    evalIfExp _ _ _ _ Refl {a = True} {b = _} {c = _} impossible

    evalCatchExp : (x : Exp a t tEnv) -> (h : Exp b t tEnv) -> (env : Trace tEnv) -> (p : (a && (Delay b)) = False) -> V t
    evalCatchExp x h env p {a = False} {b} = eval x env
    evalCatchExp x h env p {a = True} {b = False} = eval h env
    evalCatchExp _ _ _ Refl {a = True} {b = True} impossible

    eval : (e : Exp b t tEnv) -> (env : Trace tEnv) -> {auto p : b = False} -> V t
    eval (VarExp {p=myProof} id) env {p} = findVariable p myProof env
    eval (SingleExp v) env = v
    eval (PlusExp x y) env {p} = evalPlusExp x y env p
    eval (IfExp cond x y) env {p} = evalIfExp cond x y env p
    eval ThrowExp _ {p = Refl} impossible
    eval (CatchExp x h) env {p} = evalCatchExp x h env p

evalProgram : (program : Program envt) -> Trace envt
evalProgram EmptyProgram = EmptyTrace
evalProgram (Statement (id, exp) previous) =
  let evaluatedPrevious = evalProgram previous in
  let evaluatedExpresion = eval exp evaluatedPrevious in
  TraceStep evaluatedExpresion id evaluatedPrevious

{-
var x = 0;
var y = 42;
var z = 17;
x = x + y + z;
-}

xEqualsZero : Program [("x", NatTy)]
xEqualsZero = Statement ("x", SingleExp (VNat 0)) EmptyProgram

yEqualsFortyTwo : Program [("y", NatTy), ("x", NatTy)]
yEqualsFortyTwo = Statement ("y", SingleExp (VNat 42)) xEqualsZero

zEquals17 : Program [("z", NatTy), ("y", NatTy), ("x", NatTy)]
zEquals17 = Statement ("z", SingleExp (VNat 17)) yEqualsFortyTwo

xEqualsSum : Program [("x", NatTy), ("z", NatTy), ("y", NatTy), ("x", NatTy)]
xEqualsSum = Statement ("x", PlusExp (PlusExp (VarExp "x") (VarExp "y")) (VarExp "z")) zEquals17

mutual
  debugL : Trace envt -> List String
  debugL EmptyTrace = []
  debugL (TraceStep x id prf) = case x of
    (VNat v) => (id ++ " <- " ++ show v) :: debugL prf
    (VBool v) => (id ++ " <- " ++ show v) :: debugL prf

  debugP : List String -> IO ()
  debugP [] = pure ()
  debugP (x :: xs) = do putStrLn x
                        debugP xs

  debug : (p : Program t) -> IO ()
  debug p = debugP (reverse $ debugL (evalProgram p))


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



{-
--comp?
compCatch : Exp b ty env -> Code (Val ty :: (s'' ++ (Han s s') :: s)) s' -> Code (s'' ++ (Han s s') :: s) s'
compCatch (VarExp id) c = ?compCatch_rhs_1
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
-}
