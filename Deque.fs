namespace ITT

module Deque =

  type Deque<'a> (capacity : int) =
    do 
      if capacity < 1 then
        failwith "Deque capacity must be strictly positive"
    let mutable capacity = capacity
    let mutable capacity1 = capacity - 1
    let mutable count = 0
    let mutable buffer = Array.zeroCreate capacity
    let mutable front = 0
    let decrement idx = if idx = 0 then capacity1 else idx - 1
    let increment idx = if idx = capacity1 then 0 else idx + 1
    let mutable back = decrement front

    let expandBuffer () =
      let newCap = capacity * 2
      let newBuf = Array.zeroCreate newCap
      if count <> 0 then
        if front <= back then
          Array.blit buffer front newBuf front count
        else
          Array.blit buffer front newBuf front capacity
          Array.blit buffer 0 newBuf capacity (count - capacity)
      if back < front then
        back <- back + capacity
      buffer <- newBuf
      capacity <- newCap
      capacity1 <- newCap - 1

    member _.Capacity = capacity

    member _.Count = count
    
    member _.PeekFront () = buffer[front]

    member _.PeekBack () = buffer[back]

    member this.PopFront () =
      if count = 0 then
        ValueNone 
      else
        let x = this.PeekFront ()
        buffer[front] <- Unchecked.defaultof<'a>
        front <- increment front
        count <- count - 1
        ValueSome x
    
    member this.PopBack () =
      if count = 0 then
        ValueNone
      else
        let x = this.PeekBack ()
        buffer[back] <- Unchecked.defaultof<'a>
        back <- decrement back
        count <- count - 1
        ValueSome x
    
    member _.PushFront (x : 'a) =
      if count >= capacity then expandBuffer ()
      front <- decrement front
      buffer[front] <- x
      count <- count + 1
    
    member _.PushBack (x : 'a) =
      if count >= capacity then expandBuffer ()
      back <- increment back
      buffer[back] <- x
      count <- count + 1



