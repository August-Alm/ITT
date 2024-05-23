namespace ITT

module Type =

  type Type =
    | Unit
    | Tuple of Type * Type
    | Arrow of Type * Type
    | Box of Type 
  
  [<RequireQualifiedAccess>]
  module Type =

    /// Reduces a type to its normal form:
    /// `!` is idempotent and distributes over `⊗`.
    let rec reduce (typ : Type) =
      match typ with
      | Box (Box t) -> reduce (Box t) 
      | Box (Tuple (s, t)) -> reduce (Tuple (Box s, Box t))
      | _ -> typ
    
    let rec show (typ : Type) =
      match reduce typ with
      | Unit -> "Unit"
      | Tuple (s, t) -> $"({show s} ⊗ {show t})"
      | Arrow (s, t) -> $"({show s} ⇒ {show t})"
      | Box t -> $"!{show t}"
    
    /// Returns `true` if `typ1` is a subtype of `typ2`, written `typ1 < typ2`.
    /// Subsumption is defined by the requirements that `typ < typ` and `typ < !typ`
    /// for all types, and giving tensor and arrow types their usual co- and contravariance
    /// properties.
    let rec isSubtype (typ1 : Type) (typ2 : Type) =
      match typ1, typ2 with
      | Unit, Unit -> true
      | Tuple (s1, t1), Tuple (s2, t2) -> isSubtype s1 s2 && isSubtype t1 t2
      | Arrow (s1, t1), Arrow (s2, t2) -> isSubtype s2 s1 && isSubtype t1 t2
      | Box t1, Box t2 -> isSubtype t1 t2
      | Box t1, _ -> isSubtype t1 typ2
      | _ -> false
    