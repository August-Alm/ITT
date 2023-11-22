namespace ITT

module InteractionTypeTheory =

  open System.Collections.Generic
  open Deque

  type Path = Dictionary<uint32, Deque<byte>>

  type Log = Stack<string>

  let TAG = 28u
  let NIL = 0u
  let ORB = 1u
  let ERA = 2u
  let CON = 3u
  let ANN = 4u
  let FIX = 5u
  let DUP = 6u
  
  let inline port (address : uint32, slot : uint32) = (address <<< 2) ||| slot
  let inline address (port : uint32) = port >>> 2
  let inline slot (port : uint32) = port &&& 3u

  let ROOT = port (0u, 1u)
  
  type Net private (nodes : ResizeArray<uint32>, reuse : Stack<uint32>, rules : int) =
    let mutable rules = rules
    new () =
      let nodes = ResizeArray<uint32> 16
      let root = 1u
      nodes[int <| port (root, 0u)] <- port (root, 2u)
      nodes[int <| port (root, 1u)] <- port (root, 1u)
      Net (nodes, Stack<uint32> (), 0)

    member _.Rules = rules

    member _.NewNode (kind : uint32) =
      let address =
        match reuse.TryPop () with
        | true, address -> address
        | false, _ ->
          let len = nodes.Count
          nodes.EnsureCapacity (len + 4) |> ignore
          uint32 (len / 4)
      nodes[int <| port (address, 0u)] <- port (address, 0u)
      nodes[int <| port (address, 1u)] <- port (address, 1u)
      nodes[int <| port (address, 2u)] <- port (address, 2u)
      nodes[int <| port (address, 3u)] <- kind
      address
    
    member _.Link (ptrA : uint32) (ptrB : uint32) =
      nodes[int ptrA] <- ptrB
      nodes[int ptrB] <- ptrA 

    member _.Erase (address : uint32) =
      nodes[int <| port (address, 0u)] <- 0u
      nodes[int <| port (address, 1u)] <- 0u
      nodes[int <| port (address, 2u)] <- 0u
      nodes[int <| port (address, 3u)] <- NIL
      reuse.Push address

    member _.Kind (address : uint32) =
      nodes[int <| port (address, 3u)]

    member _.Enter (port : uint32) =
      nodes[int port]
    
    member _.Get (p : uint32) (slot : uint32) =
      nodes[int <| port (address p, slot)]

    member this.Compare step flip
      a0 aR (aPath : Path) (aLog : Log)
      b0 bR (bPath : Path) (bLog : Log) =
      let halt = 4096
      let step = step + 1
      let a1 = this.Enter a0
      let aS = slot a1
      let aK = this.Kind (address a1) 
      if step > halt || a1 = aR || a1 = ROOT then
        if flip then
          this.Compare 0 false
            b0 bR bPath bLog
            a0 aR aPath aLog
        else
          let av =
            match aPath.TryGetValue CON with
            | true, bs -> bs.Count
            | false, _ -> 0
          let bv =
            match bPath.TryGetValue CON with
            | true, bs -> bs.Count
            | false, _ -> 0
          av = bv
      elif aS = 0u then
        match aPath.TryGetValue aK with
        | true, bs when bs.Count > 0 ->
          let slot = bs.PopBack().Value 
          aLog.Push $"down({address a1}, {slot})"
          let a0 = port (address (this.Enter a0), uint32 slot)
          let eq =
            this.Compare step flip
              a0 aR aPath aLog
              b0 bR bPath bLog
          aLog.Pop () |> ignore
          match aPath.TryGetValue aK with
          | true, bs -> bs.PushBack slot
          | false, _ ->
            let bs = Deque 16
            bs.PushBack slot
            aPath.Add (aK, bs)
          eq
        | _ ->
          let mutable eq = true
          let mutable slot = 2u
          while eq && slot >= 1u do
            aLog.Push $"down({address a1}, {slot})"
            match bPath.TryGetValue aK with
            | true, bs -> bs.PushFront (byte slot)
            | false, _ ->
              let bs = Deque 16
              bs.PushFront (byte slot)
              bPath.Add (aK, bs)
            let a0 = port (address (this.Enter a0), uint32 slot)
            eq <-
              this.Compare step flip
                a0 aR aPath aLog
                b0 bR bPath bLog
            aLog.Pop () |> ignore
            bPath[aK].PopFront () |> ignore
            slot <- slot - 1u
          true
      elif aS > 0u then
        aLog.Push $"up({address a1}, {aS})"
        match aPath.TryGetValue aK with
        | true, bs -> bs.PushBack (byte (slot (this.Enter a0)))
        | false, _ ->
          let bs = Deque 16
          bs.PushBack (byte (slot (this.Enter a0)))
          aPath.Add (aK, bs)
        let a0 = port (address (this.Enter a0), 0u)
        let eq =
          this.Compare step flip
            a0 aR aPath aLog
            b0 bR bPath bLog
        aPath[aK].PopBack () |> ignore
        eq
      else
        failwith "unreachable"
    
    member this.Equal a b =
      let aPath = Path ()
      let aLog = Log ()
      let bPath = Path ()
      let bLog = Log ()
      this.Compare 0 true
        a a aPath aLog
        b b bPath bLog

    // Annihilation interaction.
    // ---|\     /|---    ---, ,---
    //    | |---| |    =>     X
    // ---|/     \|---    ---' '---
    member this.Annihilate (x : uint32) (y : uint32) =
      if this.Kind x = ORB && this.Kind y = ORB then
        if not (this.Equal (port (x, 1u)) (port (y, 1u))) then
          failwith "incoherent"
      let p0 = this.Enter (port (x, 1u))
      let p1 = this.Enter (port (y, 1u))
      this.Link p0 p1
      let q0 = this.Enter (port (x, 2u))
      let q1 = this.Enter (port (y, 2u))
      this.Link q0 q1
      this.Erase x
      this.Erase y
  
    // Commute interaction.
    //                        /|-------|\
    //                    ---|#|       | |---
    // ---|\     /|---        \|--, ,--|/
    //    | |---|#|    =>          X
    // ---|/     \|---        /|--' '--|\
    //                    ---|#|       | |---
    //
    member this.Commute (x : uint32) (y : uint32) =
      let a = this.NewNode (this.Kind x)
      let b = this.NewNode (this.Kind y)
      let t = this.Enter (port (x, 1u))
      this.Link (port (b, 0u)) t
      let t = this.Enter (port (x, 2u))
      this.Link (port (y, 0u)) t
      let t = this.Enter (port (y, 1u))
      this.Link (port (a, 0u)) t
      let t = this.Enter (port (y, 2u))
      this.Link (port (x, 0u)) t
      this.Link (port (a, 1u)) (port (b, 1u))
      this.Link (port (a, 2u)) (port (y, 1u))
      this.Link (port (b, 2u)) (port (x, 1u))
      this.Link (port (x, 2u)) (port (y, 2u))
  
    member this.Rewrite (x : uint32) (y : uint32) =
      if this.Kind (address x) = this.Kind (address y) then
        this.Annihilate x y
      else
        this.Commute (address x) (address y)

    member this.Reduce (root : uint32) =
      let path = Stack<uint32> 16
      let mutable prev = root
      let mutable todo = true
      while todo do
        let next = this.Enter prev
        if next = root then
          todo <- false
        elif slot next = 0u then
          if slot prev = 0u then
            rules <- rules + 1
            this.Rewrite prev next
            prev <- path.Pop ()
          else
            todo <- false
        else
          path.Push prev
          prev <- port (address next, 0u)
    
    member this.Normalize () =
      let mutable rs = 0
      let mutable todo = true
      while todo do
        let initRules = rs
        let upper = uint32 (nodes.Count / 4)
        let mutable innerTodo = true
        let mutable idx = 0u
        while innerTodo && idx <= upper do
          let k = this.Kind idx
          if k <> NIL then
            let prev = port (idx, 0u)
            let next = this.Enter prev
            if slot next = 0u then
              rs <- rs + 1
              this.Rewrite prev next
              innerTodo <- false
          idx <- idx + 1u
        todo <- initRules <> rs