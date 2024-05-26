namespace ITT

module Type =

  [<Sealed>]
  type Type

  val (|Unit|Tuple|Arrow|Bang|) : Type -> Choice<unit, Type * Type, Type * Type, Type>

  val Unit : Type

  // Constructor of arrow types.
  val hom : Type -> Type -> Type

  // Constructor of tuple (tensor) types.
  val tup : Type -> Type -> Type

  /// The bang `!` is idempotent and distributes over the tensor tuple `⊗`.
  val bang : Type -> Type

  [<RequireQualifiedAccess>]
  module Type =

    val show : Type -> string

    /// Returns `true` if `typ1` is a subtype of `typ2`, written `typ1 < typ2`.
    /// Subsumption is defined by the requirements that `typ < typ` and `typ < !typ`
    /// for all types, and giving tensor and arrow types their usual co- and contravariance
    /// properties.
    val isSubtype : Type -> Type -> bool


