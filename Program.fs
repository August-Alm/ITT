namespace ITT

module Program =

  open ITT.Terms
  open ITT.Type
  open System
  open System.Threading
  open System.Threading.Tasks

  let church2 =
    let bod = App (Var "s1", App (Var "s2", Var "z"))
    Dup ("s1", "s2", Var "s", Lam ("s", Lam ("z", bod)))
  
  let church2Alt =
    let bod = App (Var "s1", App (Var "s2", Var "z"))
    Lam ("s", Lam ("z", Dup ("s1", "s2", Var "s", bod)))
  
  let idlam = Lam ("t", Var "t")

  let idapp = App (idlam, Lam ("y", Var "y"))

  let killer = Fre (Var "x", Lam ("x", Nil ()))

  let vanishing = Fre (idlam, Nil ())

  let checker1 = Chk (idlam, hom Unit Unit)

  let checker2 =
    let e = hom Unit Unit
    let t = hom (bang e) e
    Chk (church2, t)

  let dup =
    let bod = App (Var "s1", App (Var "s2", Var "z"))
    let lam = Lam ("s", Lam ("z", bod))
    Fre (Var "f1", Dup ("s1", "s2", Var "s", Dup ("f1", "f2", lam, Var "f2")))

  let checker3 =
    let e = hom Unit Unit
    let t = hom (bang e) e
    Chk (church2, bang t)
  
  let y =
    Lam ("f", Dup ("fx", "x", App (Var "f", Var "x"), Var "fx"))
  
  let checker4 =
    let e = hom Unit Unit
    let t = hom (bang e) e
    Chk (y, t)
  

  [<EntryPoint>]
  let main _ =

    let foo t =
      printfn "original: %s" (t |> show)
      printfn "readback: %s" (t |> roundtrip |> show)
      let printReduction t =
        try
          let s, r = reduceSteps t
          printfn "reduced after %d steps: %s" s (show r)
        with
        | e -> printfn "%s" e.Message
      let cts = new CancellationTokenSource ()
      let task = Task.Factory.StartNew ((fun _ ->
        printReduction t; cts.Token.ThrowIfCancellationRequested ()),
        cts)
      if not (task.Wait (10_000, cts.Token)) then
        cts.Cancel ()
        printfn "no normal form achieved in 10 seconds"
      printfn ""

    foo idlam

    foo idapp

    foo church2

    foo church2Alt

    foo killer

    foo vanishing

    foo checker1

    foo checker2

    foo dup

    foo checker3

    foo y

    foo checker4

    foo (App (y, idlam))

    foo (App (y, church2))

    0