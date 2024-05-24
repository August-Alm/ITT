namespace ITT


[<AutoOpen>]
module Utils =

  [<RequireQualifiedAccess>]
  module Debug =
    let printfn s = System.Diagnostics.Debug.WriteLine s