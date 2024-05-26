namespace ITT

module Type =

  type Type =
    | TUnit
    | TTuple of Type * Type
    | TArrow of Type * Type
    | TBox of Type 
  
  let (|Unit|Tuple|Arrow|Bang|) (typ : Type) =
    match typ with
    | TUnit -> Unit
    | TTuple (a, b) -> Tuple (a, b)
    | TArrow (a, b) -> Arrow (a, b)
    | TBox t -> Bang t 
    
  let Unit = TUnit

  let hom (a : Type) (b : Type) = TArrow (a, b)

  let tup (a : Type) (b : Type) = TTuple (a, b)

  let rec bang (typ : Type) =
    match typ with
    | TBox _ -> typ
    | TTuple (a, b) -> TTuple (bang (TBox a), bang (TBox b))
    | _ -> TBox typ

  [<RequireQualifiedAccess>]
  module Type =

    let rec reduce (typ : Type) =
      match typ with
      | TBox (TBox t) -> reduce (TBox t) 
      | TBox (TTuple (s, t)) -> reduce (TTuple (TBox s, TBox t))
      | _ -> typ
    
    let rec show (typ : Type) =
      match reduce typ with
      | TUnit -> "U"
      | TTuple (s, t) -> $"({show s} ⊗ {show t})"
      | TArrow (s, t) -> $"({show s} ⇒ {show t})"
      | TBox t -> $"!{show t}"
    
    let rec isSubtype (typ1 : Type) (typ2 : Type) =
      match typ1, typ2 with
      | TUnit, TUnit -> true
      | TTuple (s1, t1), TTuple (s2, t2) -> isSubtype s1 s2 && isSubtype t1 t2
      | TArrow (s1, t1), TArrow (s2, t2) -> isSubtype s2 s1 && isSubtype t1 t2
      | TBox t1, TBox t2 -> isSubtype t1 t2
      | TBox t1, _ -> isSubtype t1 typ2
      | _ -> false
    