namespace ITT

module Stacks =

  open FSharp.NativeInterop

  [<Struct>]
  type VStack<'a when 'a : unmanaged> =
    private
      { Capacity : int
        BufferPtr : nativeptr<'a>
        mutable Count : int
      }

  module VStack = 

    let ctor (capacity : int, bufferPtr : nativeptr<'a>) =
      { Capacity = capacity
        BufferPtr = bufferPtr
        Count = 0
      }

    let clear (stack : VStack<'a> byref) =
      stack.Count <- 0

    let push (x : 'a) (stack : VStack<'a> byref) =
      if stack.Count >= stack.Capacity then
        failwith "VStack overflow"
      NativePtr.write (NativePtr.add stack.BufferPtr stack.Count) x
      stack.Count <- stack.Count + 1

    let pop (stack : VStack<'a> byref) =
      if stack.Count = 0 then
        failwith "VStack underflow"
      stack.Count <- stack.Count - 1
      NativePtr.read (NativePtr.add stack.BufferPtr stack.Count)
    
    let tryPop (stack : VStack<'a> byref) (x : 'a byref) =
      if stack.Count = 0 then
        false
      else
        stack.Count <- stack.Count - 1
        x <- NativePtr.read (NativePtr.add stack.BufferPtr stack.Count)
        true


  type FixedStack<'a> (capacity : int) =
    let mutable count = 0
    let storage = Array.zeroCreate<'a> capacity

    member _.Count with get () = count

    member _.Push (x : 'a) = storage[count] <- x; count <- count + 1

    member _.Pop () = count <- count - 1; storage[count]

    member _.TryPop (x : 'a byref) =
      if count = 0 then false
      else
        count <- count - 1
        x <- storage[count]
        true
    
    member _.Clear () = count <- 0