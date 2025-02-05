namespace ITT

module Terms =

  open Nets

  [<AbstractClass>]
  type Term = class end
  
  type Nil =
    inherit Term
    new : unit -> Nil
  
  type Uni =
    inherit Term
    new : unit -> Uni

  type Var =
    inherit Term
    member Name : string
    new : string -> Var
  
  type Lam =
    inherit Term
    member Name : string
    member Body : Term
    new : string * Term -> Lam
  
  type App =
    inherit Term
    member Func : Term
    member Argm : Term
    new : Term * Term -> App
  
  type Sup =
    inherit Term
    member Left : Term
    member Right : Term
    new : Term * Term -> Sup
  
  type The =
    inherit Term
    member Name : string
    member Body : Term
    new : string * Term -> The
  
  type Chk =
    inherit Term
    member Term : Term
    member Type : Term
    new : Term * Term -> Chk
  
  type Fre =
    inherit Term
    member Term : Term
    member Body : Term
    new : Term * Term -> Fre
  
  type Dup =
    inherit Term
    member Left : string
    member Right : string
    member Term : Term
    member Body : Term
    new : string * string * Term * Term -> Dup
  

  val show : Term -> string

  val build : Term -> Net

  val readback : Net -> Term

  val roundtrip : Term -> Term

  val reduce : Term -> Term

  val reduceSteps : Term -> int * Term