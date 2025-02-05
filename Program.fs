namespace ITT

module Program =

  open ITT.Terms
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

  let polid = Fre (Var "c", Lam ("c", idlam))

  let EndF = Dup ("a1", "a2", Var "a", Lam ("a", The ("f", Lam ("x",
    Chk (App (Var "f", Chk (Var "x", Var "a1")), Var "a2")))))

  let forall =
    Lam ("F", The ("n", Lam ("s", Dup ("s1", "s2", Var "s",
    Chk (App (Var "n", Chk (Var "s1", Uni ())), App (Var "F", Chk (Var "s2", Uni ())))))))

  let polidCheck = Chk (polid, App (forall, EndF))

  let dup =
    let bod = App (Var "s1", App (Var "s2", Var "z"))
    let lam = Lam ("s", Lam ("z", bod))
    Fre (Var "f1", Dup ("s1", "s2", Var "s", Dup ("f1", "f2", lam, Var "f2")))

  let y =
    Lam ("f", Dup ("fx", "x", App (Var "f", Var "x"), Var "fx"))
  
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

    foo polidCheck

    foo dup

    foo y

    foo (App (y, idlam))

    foo (App (y, church2))

    0