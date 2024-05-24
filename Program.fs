namespace ITT

module Program =

  open ITT.Terms
  open ITT.Type

  let church2 =
    let bod = App (Var "s1", App (Var "s2", Var "z"))
    Dup ("s1", "s2", Var "s", Lam ("s", Lam ("z", bod)))
  
  let church2Alt =
    let bod = App (Var "s1", App (Var "s2", Var "z"))
    Lam ("s", Lam ("z", Dup ("s1", "s2", Var "s", bod)))
  
  let idlam = Lam ("x", Var "x")

  let idapp = App (idlam, Lam ("y", Var "y"))

  let killer = Fre (Var "x", Lam ("x", Nil ()))

  let vanishing = Fre (idlam, Nil ())

  let checker1 = Chk (idlam, Arrow (Unit, Unit))

  let checker2 =
    let e = Arrow (Unit, Unit)
    let t = Arrow (Box e, e)
    Chk (church2, t)

  let dup =
    let bod = App (Var "s1", App (Var "s2", Var "z"))
    let lam = Lam ("s", Lam ("z", bod))
    Fre (Var "f1", Dup ("s1", "s2", Var "s", Dup ("f1", "f2", lam, Var "f2")))

  let checker3 =
    let e = Box (Arrow (Unit, Unit))
    let t = Arrow (e, Arrow (Unit, Unit))
    Chk (church2, Box t)
  

  [<EntryPoint>]
  let main _ =

    let foo t =
      printfn "original: %s" (t |> show)
      printfn "readback: %s" (t |> roundtrip |> show)
      let s, r = reduceSteps t
      printfn "reduced after %d steps: %s" s (show r)
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

    0