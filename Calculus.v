Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From AlgEffects Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Sets.Uniset.

Module Calculus.

Inductive computationType : Type :=
  | ComputationType : valueType -> uniset string -> computationType
with valueType : Type :=
  | BoolType : valueType
  | FunType : valueType -> computationType -> valueType
  | HandlerType : computationType -> computationType -> valueType.

Inductive computation : Type :=
  | CReturn (v : value)
  | COp (op : string) (v : value) (x : string) (c : computation)
  | CDo (x : string) (c1 c2 : computation) : computation
  | CIf (b : value) (c1 c2 : computation) : computation
  | CApp (v1 : value) (v2 : value) : computation
  | CHandle (e : computation) (h : value) : computation
with value : Type :=
  | VVar (x : string)
  | VTrue
  | VFalse
  | VFun (x : string) (t : valueType) (body : computation)
  (* Small simplification: handler handles only one op *)
  | VHandler (x : string) (cr : computation) (op : opCase)
with opCase : Type :=
  | OpCase (op : string) (x : string) (k : string) (e : computation).

(* Schemes for mutual induction on computations, values and op cases *)
Scheme computation_mut := Induction for computation Sort Prop
with value_mut := Induction for value Sort Prop
with opCase_mut := Induction for opCase Sort Prop.

Fixpoint subst
  (x : string) (s : value) (t : computation) :=
  match t with
  | CReturn v => CReturn (subst_in_value x s v)
  | COp op v y c => 
      if eqb_string x y then
        COp op (subst_in_value x s v) y c
      else
        COp op (subst_in_value x s v) y (subst x s c)
  | CDo y c1 c2 => 
      if eqb_string x y then
        CDo y (subst x s c1) c2
      else
        CDo y (subst x s c1) (subst x s c2)
  | CIf b c1 c2 => CIf (subst_in_value x s b) (subst x s c1) (subst x s c2)
  | CApp v1 v2 => CApp (subst_in_value x s v1) (subst_in_value x s v2)
  | CHandle c v => CHandle (subst x s c) (subst_in_value x s v)
  end
with subst_in_value (x : string) (s : value) (t : value) :=
  match t with
  | VVar y => if eqb_string x y then s else t
  | VTrue => VTrue
  | VFalse => VFalse
  | VFun y T body => 
    if eqb_string x y then 
      t
    else
      (VFun y T (subst x s body))
  | VHandler xr er op =>
    if eqb_string x xr then
      VHandler xr er (subst_in_opCase x s op)
    else
      VHandler xr (subst x s er) (subst_in_opCase x s op)
  end
with subst_in_opCase (x : string) (s : value) (t : opCase) :=
  match t with
  | OpCase op y k e => 
    if eqb_string x y || eqb_string x k then
       OpCase op y k e
    else
       OpCase op y k (subst x s e)
  end.

Reserved Notation "E '\' t '-->' t'" (at level 40).

Inductive step : total_map (valueType * valueType) -> computation -> computation -> Prop :=
  | ST_AppAbs : forall E x T2 c v2,
      E \ CApp (VFun x T2 c) v2 --> subst x v2 c
  | ST_IfTrue : forall E c1 c2,
      E \ CIf VTrue c1 c2 --> c1
  | ST_IfFalse : forall E c1 c2,
      E \ CIf VFalse c1 c2 --> c2
  | ST_Do1 : forall E x c1 c2 c1',
      E \ c1 --> c1' ->
      E \ CDo x c1 c2 --> CDo x c1' c2
  | ST_DoReturn : forall E x v c,
      E \ CDo x (CReturn v) c --> subst x v c
  | ST_DoOp : forall E op x v y c1 c2,
      E \ CDo x (COp op v y c1) c2 --> COp op v y (CDo x c1 c2)
  | ST_Handle1 : forall E c c' h,
      E \ c --> c' ->
      E \ CHandle c h --> CHandle c' h
  | ST_HandleReturn : forall E v xr er op,
    E \ CHandle (CReturn v) (VHandler xr er op) --> subst xr v er
  | ST_HandleOpEqual : forall E op v y c xr cr x k ch,
    E \ CHandle (COp op v y c) (VHandler xr cr (OpCase op x k ch)) -->
    subst k (VFun y (snd (E op))
    (CHandle c (VHandler xr cr (OpCase op x k ch)))) (subst x v ch)
  | ST_HandleOpNotEqual : forall E op1 op2 v y c xr cr x k ch,
    op1 <> op2 ->
    E \ CHandle (COp op1 v y c) (VHandler xr cr (OpCase op2 x k ch)) -->
    COp op1 v y (CHandle c (VHandler xr cr (OpCase op2 x k ch)))

where "E '\' t '-->' t'" := (step E t t').

Hint Constructors step : core.

Definition context := partial_map valueType.

(* computation c has type T in the type context Gamma and the effect signature E *)
Reserved Notation "E '\' Gamma '||-' c '\in' T" (at level 40).
(* value v has type T in the type context Gamma and the effect signature E *)
Reserved Notation "E '\' Gamma '|-' v '\in' T" (at level 40).

Definition set_remove (x : string) (s : uniset string) :=
  Charac (fun y:string => if eqb_string x y then false else (charac s y)).

Inductive has_type : total_map (valueType * valueType) -> context -> computation -> computationType -> Prop :=
  | T_App : forall E T1 T2 Gamma v1 v2,
      E \ Gamma |- v1 \in (FunType T2 T1) ->
      E \ Gamma |- v2 \in T2 ->
      E \ Gamma ||- CApp v1 v2 \in T1
   | T_If : forall E v c1 c2 T Gamma,
      E \ Gamma |- v \in BoolType ->
      E \ Gamma ||- c1 \in T ->
      E \ Gamma ||- c2 \in T ->
      E \ Gamma ||- CIf v c1 c2 \in T
   | T_Return : forall E v T Delta Gamma,
      E \ Gamma |- v \in T ->
      E \ Gamma ||- CReturn v \in (ComputationType T Delta)
   | T_Op : forall E op T1 T2 T Gamma Delta v y c,
      E op = (T1, T2) ->
      E \ Gamma |- v \in T1 ->
      In Delta op ->
      E \ y |-> T2 ; Gamma ||- c \in (ComputationType T Delta) ->
      E \ Gamma ||- COp op v y c \in (ComputationType T Delta)
   | T_Do : forall E x c1 c2 T1 T Gamma Delta,
      E \ Gamma ||- c1 \in (ComputationType T1 Delta) ->
      E \ x |-> T1 ; Gamma ||- c2 \in (ComputationType T Delta) ->
      E \ Gamma ||- CDo x c1 c2 \in (ComputationType T Delta)
   | T_Handle : forall E T1 T2 h c Gamma,
      E \ Gamma ||- c \in T1 ->
      E \ Gamma |- h \in (HandlerType T1 T2) ->
      E \ Gamma ||- CHandle c h \in T2

where "E '\' Gamma '||-' c '\in' T" := (has_type E Gamma c T)

with has_type_value : total_map (valueType * valueType) -> context -> value -> valueType -> Prop :=
  | T_Var : forall E Gamma x T,
      Gamma x = Some T ->
      E \ Gamma |- VVar x \in T
  | T_True : forall E Gamma,
      E \ Gamma |- VTrue \in BoolType
  | T_False : forall E Gamma,
      E \ Gamma |- VFalse \in BoolType
  | T_Fun : forall E Gamma x T1 T2 c,
      E \ x |-> T2 ; Gamma ||- c \in T1 ->
      E \ Gamma |- VFun x T2 c \in (FunType T2 T1)
  | T_Handler : forall E xr cr op opCase A B Gamma Delta Delta',
      E \ xr |-> A ; Gamma ||- cr \in (ComputationType B Delta') ->
      has_type_opCase E Gamma op opCase (ComputationType B Delta') ->
      incl (set_remove op Delta) Delta' ->
      E \ Gamma |- VHandler xr cr opCase \in 
        (HandlerType (ComputationType A Delta) (ComputationType B Delta'))

where "E '\' Gamma '|-' v '\in' T" := (has_type_value E Gamma v T)

with has_type_opCase : total_map (valueType * valueType) -> context -> string -> opCase -> computationType -> Prop :=
  | T_OpCase : forall E x op k T1 T2 T Gamma c,
      E op = (T1, T2) ->
      x <> k ->
      E \ x |-> T1 ; k |-> FunType T2 T ; Gamma ||- c \in T ->
      has_type_opCase E Gamma op (OpCase op x k c) T.

Hint Constructors has_type : core.
Hint Constructors has_type_value : core.
Hint Constructors has_type_opCase : core.

End Calculus.