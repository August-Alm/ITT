namespace ITT

module Program =

  open FSharp.NativeInterop
  open Stacks
  open System.Collections.Generic
  open System.Diagnostics

  [<Struct>]
  type R = { X : bigint; Y : bigint }
  with
    static member One = { X = 1I; Y = 0I }
    static member Phi = { X = 0I; Y = 1I }

    static member (+) (a, b) =
      { X = a.X + b.X; Y = a.Y + b.Y }
    
    static member (-) (a, b) =
      { X = a.X - b.X; Y = a.Y - b.Y }
    
    static member (*) (a, b) =
      { X = a.X * b.X + a.Y * b.Y
        Y = a.X * b.Y + a.Y * b.X + a.Y * b.Y
      }
    
    static member (/) (a, b) =
      raise <| System.NotImplementedException "Only a ring"
    

  let fib n = (pown R.Phi n).Y


  let fibStack (n : int) =
    let bufPtr = NativePtr.stackalloc 30
    let mutable stack = VStack.ctor (30, bufPtr)
    let mutable a = bigint n
    VStack.push a &stack
    let mutable result = 0I
    while VStack.tryPop &stack &a do
      if a = 0I || a = 1I then
        result <- result + 1I
      else
        VStack.push (a - 1I) &stack
        VStack.push (a - 2I) &stack
    result
  
  let fibHeap (n : int) =
    let stack = Stack<bigint> 30
    let mutable a = bigint n
    stack.Push a
    let mutable result = 0I
    while stack.TryPop &a do
      if a = 0I || a = 1I then
        result <- result + 1I
      else
        stack.Push (a - 1I)
        stack.Push (a - 2I)
    result
  
  let rec fibRec (n : int) =
    if n = 0 || n = 1 then 1I
    else fibRec (n - 1) + fibRec (n - 2)
    // let rec loop a b n =
    //   if n = 0I then a
    //   else loop b (a + b) (n - 1I)
    // loop 1I 1I n
  
  open ITT.Core

  let church2 =
    let bod = App (Var "s1", App (Var "s2", Var "z"))
    Dup ("s1", "s2", Var "s", Lam ("s", Lam ("z", bod)))
  
  let churc2Alt =
    let bod = App (Var "s1", App (Var "s2", Var "z"))
    Lam ("s", Lam ("z", Dup ("s1", "s2", Var "s", bod)))

  let idlam = Lam ("x", Var "x")

  [<EntryPoint>]
  let main _ =
    let clock = Stopwatch ()
    let test1 label f =
      clock.Reset ()
      clock.Start ()
      for _ = 1 to 1000 do
        for i = 0 to 20 do
          f i |> ignore
      clock.Stop ()
      printfn "%s: %A" label clock.Elapsed
    clock.Start ()

    //test1 "Heap iteration" fibHeap
    //test1 "Stack iteration" fibStack
    //test1 "Tail recursion" fibRec
    //test1 "Golden mean" fib

    //let n = 1000000
    //clock.Reset ()
    //clock.Start ()
    //fib n |> ignore
    //clock.Stop ()
    //printfn "Golden mean F_%d: %A ms" n clock.Elapsed.Milliseconds

    let foo t =
      printfn "before: %s" (t |> show)
      printfn "after: %s" (t |> Net.roundtrip |> show)

    foo idlam

    foo church2

    foo churc2Alt

    0