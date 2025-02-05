namespace ITT


module Type =

  type Type =
    | Unit
    | Tuple of Type * Type
    | Arrow of Type * Type
    | BangedArrow of Type * Type 
    
  let Unit = Unit

  let hom (a : Type) (b : Type) = Arrow (a, b)

  let tup (a : Type) (b : Type) = Tuple (a, b)

  let rec bang (typ : Type) =
    match typ with
    | Unit -> Unit
    | Tuple (a, b) -> Tuple (bang a, bang b)
    | Arrow (a, b) -> BangedArrow (a, b)
    | _ -> typ

  [<RequireQualifiedAccess>]
  module Type =

    let rec show (typ : Type) =
      match typ with
      | Unit -> "Unit"
      | Tuple (s, t) -> $"({show s} ⊗ {show t})"
      | Arrow (s, t) -> $"({show s} ⊸ {show t})"
      | BangedArrow (s, t) -> $"!({show s} ⊸ {show t})"
    
    let rec isSubtype (typ1 : Type) (typ2 : Type) =
      match typ1, typ2 with
      | Unit, Unit -> true
      | Tuple (s1, t1), Tuple (s2, t2) -> isSubtype s1 s2 && isSubtype t1 t2
      | Arrow (s1, t1), Arrow (s2, t2)
      | BangedArrow (s1, t1), Arrow (s2, t2)
      | BangedArrow (s1, t1), BangedArrow (s2, t2) ->
        isSubtype s2 s1 && isSubtype t1 t2
      | _ -> false
    