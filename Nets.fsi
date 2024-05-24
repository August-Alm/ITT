namespace ITT

module Nets =

  open Type

  type Kind =
    | ROOT = 0
    | NIL = 1
    | LAM = 2
    | APP = 3
    | SUP = 4
    | ANN = 5
    | CHK = 6
    | FRE = 7
    | DUP = 8
  
  type Net =
    new : unit -> Net
    member Rewrites : int

  [<Measure>]
  type uomPort
  
  type Port = int<uomPort>

  [<RequireQualifiedAccess>]
  module Port =

    val inline mk : address:int -> slot:int -> Port
    val inline address : Port -> int
    val inline slot : Port -> int
  
  module Net =
    val mkNode : Net -> Kind -> int
    val mkAnnNode : Net -> Type -> int
    val mkChkNode : Net -> Type -> int
    val inline getRoot : Net -> int
    val enter : Net -> Port -> Port
    val link : Net -> Port -> Port -> unit
    val kind : Net -> int -> Kind
    val getFirst : Net -> int
    val getType : Net -> int -> Type
    val getNodes : Net -> int array
  
  module Interaction =
    val reduce : Net -> int
