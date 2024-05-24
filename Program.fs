namespace ITT

module Program =

(*
@{
  Requestbody = "{
    "data" : {
      "essentials" : { "alerRule" : "johana" }
    }
  }"
}
*)
  open FSharp.NativeInterop
  open Stacks
  open System.Collections.Generic
  open System
  open System.Diagnostics
  open System.Numerics

  type Nil () =
    let mutable s0 : obj = null
    member _.Slot
      with get i = if i <> 0 then failwith "out-of-range" else s0
      and set i nd = if i <> 0 then failwith "out-of-range" else s0 <- nd

  module DivideAndConquer =

    type Either<'a, 'b> = Left of 'a | Right of 'b

    type State<'s, 'a> = 's -> 'a * 's

    let inline retur (a : 'a) : State<'s, 'a> = fun s -> a, s

    let inline bind (m : State<'s, 'a>) (f : 'a -> State<'s, 'b>) : State<'s, 'b> =
      fun s -> let a, s1 = m s in f a s1
  
    let mapM (f : 'a -> State<'s, 'b>) (xs : 'a list) : State<'s, 'b list> =
      let rec loop (xs : 'a list) (acc : 'b list) : State<'s, 'b list> =
        match xs with
        | [] -> retur (List.rev acc)
        | x :: xs -> bind (f x) (fun y -> loop xs (y :: acc))
      loop xs []

    let memoize
      (t : ('a -> State<Map<'a, 'b>, 'b>) -> ('a -> State<Map<'a, 'b>, 'b>))
      (x : 'a) =
      let rec foo (x : 'a) : State<Map<'a, 'b>, 'b> =
        fun s ->
          match Map.tryFind x s with
          | Some y -> y, s
          | None -> bar x s
      and bar (x : 'a) : State<Map<'a, 'b>, 'b> =
        fun s ->
          let y1, s1 = (t foo) x s
          y1, Map.add x y1 s1
      fst (foo x Map.empty)

    type Recur<'a, 'b> = 'a -> Either<'b, 'a list * ('b list -> 'b)>

    let distr (go : Recur<'a, 'b>) : ('a -> State<Map<'a, 'b>, 'b>) -> ('a -> State<Map<'a, 'b>, 'b>) =
      fun u x ->
        match go x with
        | Left y -> retur y
        | Right (xs, h) -> bind (mapM u xs) (retur << h)
    
    let conquer (go : Recur<'a, 'b>) = memoize (distr go)

    let dividedFib : Recur<int, int>  =
      fun x ->
        if x < 2 then Left x
        else Right ([x - 1; x - 2], List.sum)
  
    let fib = conquer dividedFib



  let testInt () =
    let rec loop (n : int) (i : int) =
      printfn "loop %d %d" n i
      if i = 0 then n
      else loop (n + 1) (i + i)
    loop 0 1

  let MAGIC_MULTIPLIER = 100L * 0x1000000L + 10L * 0x10000L + 1L
  let DOT_DETECTOR = 0x10101000L
  let ASCII_TO_DIGIT_MASK = 0x0F000F0F00L
  
  let readInt (span : ReadOnlySpan<byte>) =
    let bufPtr = NativePtr.toVoidPtr (NativePtr.stackalloc<byte> 4)
    let buf = Span<byte> (bufPtr, 8)
    span.Slice(0, min 8 span.Length).CopyTo buf
    let u = NativePtr.read<int64> (NativePtr.ofVoidPtr bufPtr)
    let negated = ~~~u
    let broadcastSign = (negated <<< 59) >>> 63
    let maskToRemoveSign = ~~~(broadcastSign &&& 0xFF)
    let withSignRemoved = u &&& maskToRemoveSign
    let dotPos = BitOperations.TrailingZeroCount (negated &&& DOT_DETECTOR)
    let aligned = withSignRemoved <<< (28 - dotPos)
    let digits = aligned &&& ASCII_TO_DIGIT_MASK
    let absValue = ((digits * MAGIC_MULTIPLIER) >>> 32) &&& 0x3FFL
    let temp = (absValue ^^^ broadcastSign) - broadcastSign
    let nextLineStart = (dotPos >>> 3) + 3
    nextLineStart, int temp

  type Nat (plus : Nat -> Nat, mul : Nat -> Nat) =
    member private _.Plus = plus
    member private _.Mul = mul
    static member succ (n : Nat) = 
      let plus (x : Nat) = x.Plus n
      let mul (x : Nat) = x.Plus (n.Mul x)
      Nat (plus, mul)
    static member Zero =
      let plus (x : Nat) = x
      let mul (_ : Nat) = Nat.Zero
      Nat (plus, mul)

  module private Unsafe =
      let inline cast<'a, 'b> (a : 'a) : 'b =
  #if !FABLE_COMPILER
          (# "" a : 'b #)
  #else
          unbox<'b> a
  #endif

  let inline clt (a : int) (b : int) = (# "clt" a b : int #)

  let inline private minimum (a : int) (b : int) =
    (a ^^^ ((b ^^^ a) &&& -clt b  a))  

  let inline private boolToInt (b : bool) : int = (# "" b : int #) //int (# "" b : byte #)

  let private boolToIntSafe b = if b then 1 else 0

  let testBoolToInt (clock : Stopwatch) (accumulator : int byref) =
    let random = Random ()
    clock.Start ()
    for i = 1 to 100_000 do
      accumulator <- accumulator + boolToInt (random.Next () = 0)
    clock.Stop ()
    printfn "testBoolToInt: %A" clock.Elapsed
  
  let testBoolToIntSafe (clock : Stopwatch) (accumulator : int byref) =
    let random = Random ()
    clock.Start ()
    for i = 1 to 100_000 do
      accumulator <- accumulator + boolToIntSafe (random.Next () = 0)
    clock.Stop ()
    printfn "testBoolToIntSafe: %A" clock.Elapsed
    


  let refTest (clock : Stopwatch) (array : int array) =
    let mutable result = 0
    clock.Reset ()
    clock.Start ()
    for i = 0 to array.Length - 1 do
      let r : inref<int> = &array[i]
      result <- result + r
    clock.Stop ()
    printfn "Ref: %A" clock.Elapsed

  let fixedTest (clock : Stopwatch) (array : int array) =
    let mutable result = 0
    clock.Reset ()
    clock.Start ()
    use p = fixed array
    for i = 0 to array.Length - 1 do
      //let r : inref<int> = NativePtr.toByRef (NativePtr.add p i)
      let r = NativePtr.get p i
      result <- result + r
    clock.Stop ()
    printfn "Fixed: %A" clock.Elapsed

  let foreachTest (clock : Stopwatch) (array : int array) =
    let mutable result = 0
    clock.Reset ()
    clock.Start ()
    for r in array do
      result <- result + r
    clock.Stop ()
    printfn "Foreach: %A" clock.Elapsed
  

  [<Struct>]
  type ABC = A | B | C


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
      raise <| NotImplementedException "Only a ring"
    

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
    let e = Box (Arrow (Unit, Unit))
    let t = Arrow (e, Arrow (Unit, Unit))
    Chk (church2, t)

  let dup =
    let bod = App (Var "s1", App (Var "s2", Var "z"))
    let lam = Lam ("s", Lam ("z", bod))
    Dup ("s1", "s2", Var "s", Dup ("f1", "f2", lam, Fre (Var "f1", Var "f2")))
    //Fre (Var "f1", Dup ("s1", "s2", Var "s", Dup ("f1", "f2", lam, Var "f2")))
    //Dup ("f1", "f2", idlam, Fre (Var "f1", Var "f2"))
    //Fre (Var "a", Dup ("a", "b", Nil (), Var "b"))

  let checker3 =
    let e = Box (Arrow (Unit, Unit))
    let t = Arrow (e, Arrow (Unit, Unit))
    Chk (church2, Box t)

  let isEven x =
    boolToInt (x % 2 = 0)

  [<EntryPoint>]
  let main _ =

    //printfn "Conquered Fibonacci of 10: %A" (DivideAndConquer.fib 10)

    //printfn "testInt () = %d" (testInt ())

    //let span = ReadOnlySpan [| '1'B; '2'B; '.'B; '7'B; |]
    //let n = readInt span
    //printfn "Read int: %A" n

    //let span = ReadOnlySpan [| '-'B; '1'B; '2'B; '.'B; '7'B; |]
    //let n = readInt span
    //printfn "Read int: %A" n

    //let span = ReadOnlySpan [| '2'B; '.'B; '7'B; |]
    //let n = readInt span
    //printfn "Read int: %A" n

    
    //let x = minimum 3 4
    //printfn "Minimum of 3 and 4: %d" x

    //let x = minimum -4 3
    //printfn "Minimum of -4 and 3: %d" x

    //let clock = Stopwatch ()
    //let test1 label f =
    //  clock.Reset ()
    //  clock.Start ()
    //  for _ = 1 to 1000 do
    //    for i = 0 to 20 do
    //      f i |> ignore
    //  clock.Stop ()
    //  printfn "%s: %A" label clock.Elapsed
    //clock.Start ()

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
      printfn "original: %s" (t |> show)
      printfn "readback: %s" (t |> roundtrip |> show)
      printfn "reduced: %s" (t |> reduce |> show)
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

    //foo checker3

    //printfn "Cast 'true' as int: %d" (boolToInt true)
    //printfn "Cast 'false' as int: %d" (boolToInt false)

    //for i = 0 to 10 do
    //  printfn "%d is even: %d" i (isEven i)
    
    //let array = Array.init 100000000 id
    //refTest clock array
    //fixedTest clock array
    //foreachTest clock array

    //let mutable accumulator = 0
    //testBoolToInt clock &accumulator
    //testBoolToIntSafe clock &accumulator
    
    //printfn "size of ABC: %d" (sizeof<ABC>)
    //printfn "size of R: %d" (sizeof<R>)
    //printfn "size of bigint: %d" (sizeof<bigint>)

    0