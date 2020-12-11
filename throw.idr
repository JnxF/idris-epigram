import Data.List

%default total

data TyExp = NatTy | BoolTy

VariableId : Type
VariableId = String

mutual
  StackType : Type
  StackType = List Ty

  HeapType : Type
  HeapType = List (VariableId, TyExp)

  data Ty = Han StackType StackType HeapType HeapType | Val TyExp

data V : TyExp -> Type where
  VNat : Nat -> V NatTy
  VBool : Bool -> V BoolTy

data Exp : Bool -> TyExp -> List (VariableId, TyExp) -> Type where
  VarExp : (vId : VariableId) -> {auto p : Elem (vId, ty) env} -> Exp False ty env
  SingleExp : (v : V t) -> Exp False t env
  PlusExp : (x : Exp a NatTy env) -> (y : Exp b NatTy env) -> Exp (a || b) NatTy env
  IfExp : (cond : Exp a BoolTy env) -> (x : Exp b t env) -> (y : Exp c t env) -> Exp (a || b || c) t env
  ThrowExp : Exp True t env
  CatchExp : (x : Exp a t env) -> (h : Exp b t env) -> Exp (a && b) t env

data Program : List (VariableId, TyExp) -> List (VariableId, TyExp) -> Type where
  EmptyProgram : Program env env

  Declaration : (vId : VariableId) ->
                (exp : Exp b t env) ->
                {auto expExecutable : b = False} ->
                (continuing : Program ((vId, t) :: env) env') ->
                (Program env env')

  Assignment : (vId : VariableId) ->
               (exp : Exp b t env) ->
               {auto expExecutable : b = False} ->
               (continuing : Program ((vId, t) :: env) env') ->
               {auto prf' : Elem (vId, t) env} ->
               (Program env env')

data ValuesEnv : List (VariableId, TyExp) -> Type where
   EmptyValuesEnv : ValuesEnv []
   MoreValuesEnv : (vId: VariableId)
                   -> V ty
                   -> ValuesEnv envTy
                   -> ValuesEnv ((vId, ty) :: envTy)

mutual
  evalVarExp : (x : ValuesEnv tEnv) -> (p : Elem (vId, ty) tEnv)  -> V ty
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
evPro EmptyProgram valueEnv = valueEnv
evPro (Declaration vId exp continuing) valueEnv =
  let evaluated = eval exp valueEnv in
  evPro continuing (MoreValuesEnv vId evaluated valueEnv)
evPro (Assignment vId exp continuing) valueEnv =
  let evaluated = eval exp valueEnv in
  evPro continuing (MoreValuesEnv vId evaluated valueEnv)
evalProgram : (p : Program [] env') -> ValuesEnv env'
evalProgram p = evPro p EmptyValuesEnv

mutual
  El : Ty -> Type
  El (Han t t' h h') = Code t t' h h'
  El (Val NatTy) = Nat
  El (Val BoolTy) = Bool

  data Code : (s : StackType) -> (s' : StackType) -> (h: HeapType) -> (h': HeapType) -> Type where
    STORE : (vId: VariableId) -> (c: Code s s' ((vId, ty)::h) h') -> Code ((Val ty)::s) s' h h'
    LOAD : (vId: VariableId) -> {auto prf: Elem (vId, ty) h} -> (c: Code ((Val ty)::s) s' h h') -> Code s s' h h'
    PUSH : V tyExp -> Code (Val tyExp :: s) s' h h' -> Code s s' h h'
    ADD : Code (Val NatTy :: s) s' h h' -> Code (Val NatTy :: Val NatTy :: s) s' h h'
    IF : (c1 : Code s s' h h') -> (c2 : Code s s' h h') -> Code (Val BoolTy :: s) s' h h'
    THROW : Code (s'' ++ (Han s s' h h') :: s) s' h h'
    MARK : (han : Code s s' h h') -> (c : Code ((Han s s' h h') :: s) s' h h') -> Code s s' h h'
    UNMARK : Code (t :: s) s' h h' -> Code (t :: (Han s s' h h') :: s) s' h h'
    HALT : Code s s h h

mutual
  compCatch : Exp b ty tenv -> Code (Val ty :: (s'' ++ (Han s s' tenv h') :: s)) s' tenv h' -> Code (s'' ++ (Han s s' tenv h') :: s) s' tenv h'
  compCatch (VarExp vId) c = LOAD vId c
  compCatch (SingleExp v) c = PUSH v c
  compCatch (PlusExp x y) c = compCatch x (compCatch {s'' = Val NatTy :: _} y (ADD c))
  compCatch {s} {s''} (IfExp cond x y) c = compCatch cond (IF (compCatch x c) (compCatch y c))
  compCatch ThrowExp c = THROW
  compCatch (CatchExp x h) c = MARK (compCatch h c) (compCatch {s'' = []} x (UNMARK c))

  compPlusExp : (p : (a || b) = False) -> (x : Exp a NatTy tenv) ->  (y : Exp b NatTy tenv) -> (c : Code ((Val NatTy) :: s) s' tenv h') -> Code s s' tenv h'
  compPlusExp {a = False} {b = False} Refl x y c = comp Refl x (comp Refl y (ADD c))
  compPlusExp {a = False} {b = True} Refl _ _ _ impossible
  compPlusExp {a = True} {b = _} Refl _ _ _ impossible

  compCatchExp : (p : (a && b) = False) -> (x : Exp a ty tenv) -> (handler : Exp b ty tenv) -> (c : Code ((Val ty) :: s) s' tenv h') -> Code s s' tenv h'
  compCatchExp {a = False} Refl x handler c = comp Refl x c
  compCatchExp {a = True} {b = False} p x handler c = MARK (comp Refl handler c) (compCatch {s'' = []} x (UNMARK c))
  compCatchExp {a = True} {b = True} Refl _ _ _ impossible

  compIfExp : (p : (a || b || c) = False) -> (cond : Exp a BoolTy tenv) ->(x : Exp b ty tenv) -> (y : Exp c ty tenv) -> (co : Code ((Val ty) :: s) s' tenv h') -> Code s s' tenv h'
  compIfExp {a = False} {b = False} {c = False} Refl cond x y co = comp Refl cond (IF (comp Refl x co) (comp Refl y co))
  compIfExp {a = False} {b = False} {c = True} Refl _ _ _ _ impossible
  compIfExp {a = False} {b = False} {c = True} Refl _ _ _ _ impossible
  compIfExp {a = True} Refl _ _ _ _ impossible

  comp : (b = False) -> Exp b ty tenv -> Code (Val ty :: s) s' tenv h' -> Code s s' tenv h'
  comp _ (VarExp {p} vId) {tenv} c = LOAD vId c
  comp p (SingleExp v) c = PUSH v c
  comp p (PlusExp x y) c = compPlusExp p x y c
  comp p (IfExp cond x y) co = compIfExp p cond x y co
  comp p (CatchExp x h) c = compCatchExp p x h c
  comp Refl ThrowExp _ impossible


  partial
  compile : (prog: Program tenv tenv') -> Code [] [] tenv tenv'
  compile (Declaration vId exp {expExecutable} continuing) =
    comp expExecutable exp (STORE vId (compile continuing))
  compile (Assignment vId exp {expExecutable} continuing) =
    comp expExecutable exp (STORE vId (compile continuing))
  compile EmptyProgram = HALT


data Stack : (s : StackType) -> Type where
  Nil : Stack []
  (::) : El t -> Stack s -> Stack (t :: s)

data Heap : (h : HeapType) -> Type where
  HeapNil : Heap []
  HeapCons : (vId: VariableId) -> V t -> Heap h -> Heap ((vId, t) :: h)

mutual

  lookup: Heap h -> (p: Elem (vId, ty) h) -> V ty
  lookup (HeapCons vId val tl) Here = val
  lookup (HeapCons _ _ tl) (There later) = lookup tl later

  partial
  exec : Code s s' h h' -> Stack s -> Heap h -> (Stack s', Heap h')
  exec (LOAD {prf} vId c) s h = case lookup h prf of
                                (VNat v) => exec c (v :: s) h
                                (VBool v) => exec c (v :: s) h
  exec (STORE vId c) {s=(Val NatTy)::_} (x :: tl) h = exec c tl (HeapCons vId (VNat x) h)
  exec (STORE vId c) {s=(Val BoolTy)::_} (x :: tl) h = exec c tl (HeapCons vId (VBool x) h)
  exec (PUSH (VNat x) c) s h = exec c (x :: s) h
  exec (PUSH (VBool x) c) s h = exec c (x :: s) h
  exec (ADD c) (m :: n :: s) h = exec c ((n + m) :: s) h
  exec (IF c1 c2) (True :: s) h = exec c1 s h
  exec (IF c1 c2) (False :: s) h = exec c2 s h
  exec THROW s h = fail s h
  exec (MARK handler c) s h = exec c (handler :: s) h
  exec (UNMARK c) (x :: handler :: s) h = exec c (x :: s) h
  exec HALT s h = (s, h)

  partial
  fail : Stack (s'' ++ Han s s' h h' :: s) -> Heap h -> (Stack s', Heap h')
  fail {s'' = []} (handler' :: s) h = exec handler' s h
  fail {s'' = (_ :: _)} (_ :: s) h = fail s h

{-
x<- 3;        -- []
x<- x+1       -- [x <- 3]
y<- x+2       -- [x <- 4,]
empty         -- [y <- 6, x <- 4]
-}

myEmpty : Program [("y", NatTy), ("x", NatTy), ("x", NatTy)] [("y", NatTy), ("x", NatTy), ("x", NatTy)]
myEmpty = EmptyProgram

yEqualsXPlusTwo : Program [("x", NatTy), ("x", NatTy)] [("y", NatTy), ("x", NatTy), ("x", NatTy)]
yEqualsXPlusTwo = Declaration "y" (PlusExp (VarExp "x") (SingleExp (VNat 2))) myEmpty

xEqualsXPlusOne : Program [("x", NatTy)] [("y", NatTy), ("x", NatTy), ("x", NatTy)]
xEqualsXPlusOne = Assignment "x" (PlusExp (VarExp "x") (SingleExp (VNat 1))) yEqualsXPlusTwo

xEquals3 : Program [] [("y", NatTy), ("x", NatTy), ("x", NatTy)]
xEquals3 = Declaration "x" (SingleExp (VNat 3)) xEqualsXPlusOne

evaluatedProgram : ValuesEnv [("y", NatTy),("x", NatTy),("x", NatTy)]
evaluatedProgram = evalProgram xEquals3

compiledProgram :  Code [] [] [] [("y", NatTy), ("x", NatTy), ("x", NatTy)]
compiledProgram = compile xEquals3

partial
executedProgram : (Stack [], Heap [("y", NatTy),("x", NatTy),("x", NatTy)])
executedProgram = exec (compiledProgram) [] HeapNil
