namespace ITT

module Terms =

  open Nets


  [<AbstractClass>]
  type Term = class end
  
  type Nil =
    inherit Term
    new : unit -> Nil
  
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
  
  type Ann =
    inherit Term
    member Term : Term
    member Type : Term
    new : Term * Term -> Ann
  
  type Chk =
    inherit Term
    member Term : Term
    member Type : Term
    new : Term * Term -> Chk
  
  type Arr =
    inherit Term
    member Domain : Term
    member Codomain : Term
    new : Term * Term -> Arr
  
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
  
  type Dec =
    inherit Term
    member Left : string
    member Right : string
    member Type : Term
    member Body : Term
    new : string * string * Term * Term -> Dec


  val show : Term -> string

  val build : Term -> Net

  val readback : Net -> Term

  val roundtrip : Term -> Term