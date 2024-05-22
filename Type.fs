namespace ITT

module Type =

  type Type =
    | Unit
    | Tuple of Type * Type
    | Arrow of Type * Type
    | Box of Type 
  
  type Checkable =
    | CUnit
    | CTuple of Checkable * Checkable
    | CArrow of Type * Checkable

  [<RequireQualifiedAccess>]
  module Type =

    let rec reduce (typ : Type) =
      match typ with
      | Box (Box t) -> reduce (Box t) 
      | Box (Tuple (s, t)) -> reduce (Tuple (Box s, Box t))
      | _ -> typ
    
    let rec show (typ : Type) =
      match reduce typ with
      | Unit -> "Unit"
      | Tuple (s, t) -> $"({show s} * {show t})"
      | Arrow (s, t) -> $"({show s} => {show t})"
      | Box t -> $"!{show t}"
    
    let rec isSubtype (typ1 : Type) (typ2 : Type) =
      match typ1, typ2 with
      | Unit, Unit -> true
      | Tuple (s1, t1), Tuple (s2, t2) -> isSubtype s1 s2 && isSubtype t1 t2
      | Arrow (s1, t1), Arrow (s2, t2) -> isSubtype s2 s1 && isSubtype t1 t2
      | Box t1, Box t2 -> isSubtype t1 t2
      | Box t1, _ -> isSubtype t1 typ2
      | _ -> false

  [<RequireQualifiedAccess>]
  module Checkable =

    let rec toType (a : Checkable) =
      match a with
      | CUnit -> Unit
      | CTuple (a, b) -> Tuple (toType a, toType b)
      | CArrow (t, a) -> Arrow (t, toType a)
    
    let show = toType >> Type.show

    let rec isSubtype (typ : Type) (a : Checkable) =
      match typ, a with
      | Unit, CUnit -> true
      | Tuple (s, t), CTuple (a, b) -> isSubtype s a && isSubtype t b
      | Arrow (s, t), CArrow (a, u) -> isSubtype t u && Type.isSubtype a s
      | Box t, _ -> isSubtype t a
      | _ -> false
