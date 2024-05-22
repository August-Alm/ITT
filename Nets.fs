namespace ITT

module Nets =

    open System.Collections.Generic
    open Type

    type Kind =
      | ROOT
      | NIL
      | LAM
      | APP
      | SUP
      | ANN
      | CHK
      | FRE
      | DUP
    with
      static member arity (kind : Kind) =
        match kind with
        | ROOT | NIL | FRE -> 1
        | _ -> 3
      
      static member fromInt (i : int) =
        match i with
        | 0 -> ROOT
        | 1 -> NIL
        | 2 -> LAM
        | 3 -> APP
        | 4 -> SUP
        | 5 -> ANN
        | 6 -> CHK
        | 7 -> FRE
        | 8 -> DUP
        | _ -> failwith $"invalid kind: {i}"
      
      static member toInt (kind : Kind) =
        match kind with
        | ROOT -> 0
        | NIL -> 1
        | LAM -> 2
        | APP -> 3
        | SUP -> 4
        | ANN -> 5
        | CHK -> 6
        | FRE -> 7
        | DUP -> 8
    

    type Reuse () =
      let stack = Stack<int> ()
      let set = HashSet<int> ()

      member _.Push (node : int) =
        if set.Add node then
          stack.Push node
        else
          set.Remove node |> ignore
          failwith "node has already been freed!"
      
      member _.TryPop () =
        match stack.TryPop () with
        | true, node -> set.Remove node, node
        | false, _ -> false, 0
      
      member _.Contains node =
        set.Contains node

    
    type Net () =
      let nodes = ResizeArray<int> 512
      let types = ResizeArray<Type> 128
      let checkables = ResizeArray<Checkable> 128
      let reuse = Reuse ()
      let mutable rewrites = 0
      do nodes.AddRange [| 2; 1; 0; 0 |]
      member _.Nodes = nodes
      member _.Types = types
      member _.Checkables = checkables
      member _.Reuse = reuse
      member _.Rewrites with get () = rewrites and set v = rewrites <- v


    [<Measure>]
    type uomPort
    
    type Port = int<uomPort>

    [<RequireQualifiedAccess>]
    module Port =

      let inline mk (address : int) (slot : int) : Port =
        LanguagePrimitives.Int32WithMeasure ((address <<< 2) ||| slot)
      
      let inline address (port : Port) = int port >>> 2

      let inline slot (port : Port) = int port &&& 3
    

    let inline getRoot (net : Net) = 0

    let inline enter (net : Net) (port : Port) : Port =
      LanguagePrimitives.Int32WithMeasure net.Nodes[int port]
    
    let inline getFirst net =
      Port.address (enter net (Port.mk (getRoot net) 0))

    let inline kind (net : Net) (node : int) =
      Kind.fromInt (net.Nodes[int <| Port.mk node 3])
    
    let inline getType (net : Net) (node : int) =
      if kind net node <> Kind.ANN then
        failwith "only ANN nodes have a type"
      net.Types[net.Nodes[int <| Port.mk node 2]]
    
    let inline setType (net : Net) (node : int) (typ : Type) =
      if kind net node <> Kind.ANN then
        failwith "only ANN nodes have a type"
      net.Types[net.Nodes[int <| Port.mk node 2]] <- typ

    let inline getCheckable (net : Net) (node : int) =
      if kind net node <> Kind.CHK then
        failwith "only CHK nodes have a type"
      net.Checkables[net.Nodes[int <| Port.mk node 2]]

    let inline setCheckable (net : Net) (node : int) (a : Checkable) =
      if kind net node <> Kind.CHK then
        failwith "only CHK nodes have a type"
      net.Checkables[net.Nodes[int <| Port.mk node 2]] <- a

    let inline set (net : Net) (portA : Port) (portB : Port) =
      net.Nodes[int portA] <- int portB
    
    let inline link (net : Net) (portA : Port) (portB : Port) =
      set net portA portB; set net portB portA
    
    let mkNode (net : Net) (kind : Kind) =
      match net.Reuse.TryPop () with
      | true, addr -> 
        set net (Port.mk addr 0) (Port.mk addr 0)
        set net (Port.mk addr 1) (Port.mk addr 1)
        set net (Port.mk addr 2) (Port.mk addr 2)
        net.Nodes[int (Port.mk addr 3)] <- Kind.toInt kind
        addr
      | false, _ ->
        let len = net.Nodes.Count
        net.Nodes.EnsureCapacity (len + 4) |> ignore
        let addr = len / 4
        net.Nodes.Add (int (Port.mk addr 0))
        net.Nodes.Add (int (Port.mk addr 1))
        net.Nodes.Add (int (Port.mk addr 2))
        net.Nodes.Add (Kind.toInt kind)
        addr
    
    let mkChkNode (net : Net) (a : Checkable) =
      match net.Reuse.TryPop () with
      | true, addr -> 
        set net (Port.mk addr 0) (Port.mk addr 0)
        set net (Port.mk addr 1) (Port.mk addr 1)
        setCheckable net addr a
        net.Nodes[int (Port.mk addr 3)] <- Kind.toInt Kind.CHK
        addr
      | false, _ ->
        let len = net.Nodes.Count
        net.Nodes.EnsureCapacity (len + 4) |> ignore
        let addr = len / 4
        net.Nodes.Add (int (Port.mk addr 0))
        net.Nodes.Add (int (Port.mk addr 1))
        net.Nodes.Add (net.Checkables.Count)
        net.Checkables.Add a
        net.Nodes.Add (Kind.toInt Kind.CHK)
        addr
    
    let mkAnnNode (net : Net) (typ : Type) =
      match net.Reuse.TryPop () with
      | true, addr -> 
        set net (Port.mk addr 0) (Port.mk addr 0)
        set net (Port.mk addr 1) (Port.mk addr 1)
        setType net addr typ
        net.Nodes[int (Port.mk addr 3)] <- Kind.toInt Kind.ANN
        addr
      | false, _ ->
        let len = net.Nodes.Count
        net.Nodes.EnsureCapacity (len + 4) |> ignore
        let addr = len / 4
        net.Nodes.Add (int (Port.mk addr 0))
        net.Nodes.Add (int (Port.mk addr 1))
        net.Nodes.Add (net.Checkables.Count)
        net.Types.Add typ
        net.Nodes.Add (Kind.toInt Kind.ANN)
        addr

    let inline freeNode (net : Net) nd =
      net.Reuse.Push nd

    let annihilate (net : Net) (ndA : int) (ndB : int) =
      link net (enter net (Port.mk ndA 1)) (enter net (Port.mk ndB 1))
      link net (enter net (Port.mk ndA 2)) (enter net (Port.mk ndB 2))
    
    let erase net (nd : int) =
      match kind net nd with
      | ROOT | NIL | FRE -> ()
      | LAM ->
        let nil = mkNode net NIL
        let fre = mkNode net FRE
        link net (enter net (Port.mk nd 1)) (enter net (Port.mk nil 0))
        link net (enter net (Port.mk nd 2)) (enter net (Port.mk fre 0))
      | APP | CHK ->
        let nil = mkNode net NIL
        let fre = mkNode net FRE
        link net (enter net (Port.mk nd 1)) (enter net (Port.mk fre 0))
        link net (enter net (Port.mk nd 2)) (enter net (Port.mk nil 0))

    let commute net (ndA : int) (ndB : int) =
      let node1, node2, node3, node4 =
        match kind net ndA, kind net ndB with
        | LAM, DUP -> mkNode net SUP, mkNode net DUP, mkNode net LAM, mkNode net LAM
        | DUP, LAM -> mkNode net LAM, mkNode net LAM, mkNode net SUP, mkNode net DUP
        | ARR, DUP -> mkNode net DUP, mkNode net DUP, mkNode net ARR, mkNode net ARR
        | DUP, ARR -> mkNode net ARR, mkNode net ARR, mkNode net DUP, mkNode net DUP
        //| CHK, LAM -> mkNode net DEC, mkNode net LAM, mkNode net ANN, mkNode net CHK
        | SUP, CHK -> mkNode net CHK, mkNode net CHK, mkNode net DUP, mkNode net SUP
        | CHK, SUP -> mkNode net DUP, mkNode net SUP, mkNode net CHK, mkNode net CHK
        //| ANN, APP -> mkNode net DEC, mkNode net APP, mkNode net CHK, mkNode net ANN
        //| APP, ANN -> mkNode net CHK, mkNode net ANN, mkNode net DEC, mkNode net APP
        | SUP, APP -> mkNode net APP, mkNode net APP, mkNode net DUP, mkNode net SUP
        | APP, SUP -> mkNode net DUP, mkNode net SUP, mkNode net APP, mkNode net APP
        //| ARR, APP -> mkNode net APP, mkNode net APP, mkNode net DEC, mkNode net ARR
        //| APP, ARR -> mkNode net DEC, mkNode net ARR, mkNode net APP, mkNode net APP
        | SUP, DEC -> mkNode net DEC, mkNode net DEC, mkNode net SUP, mkNode net SUP
        | DEC, SUP -> mkNode net SUP, mkNode net SUP, mkNode net DEC, mkNode net DEC
        //| LAM, DEC -> mkNode net ARR, mkNode net DEC, mkNode net LAM, mkNode net LAM
        //| DEC, LAM -> mkNode net LAM, mkNode net LAM, mkNode net ARR, mkNode net DEC
        | kindA, kindB -> failwith $"cannot commute {kindA} and {kindB}"
      link net (Port.mk node1 1) (Port.mk node3 1)
      link net (Port.mk node1 2) (Port.mk node4 1)
      link net (Port.mk node2 1) (Port.mk node3 2)
      link net (Port.mk node2 2) (Port.mk node4 2)
      link net (Port.mk node1 0) (enter net (Port.mk ndA 1))
      link net (Port.mk node2 0) (enter net (Port.mk ndA 2))
      link net (Port.mk node3 0) (enter net (Port.mk ndB 1))
      link net (Port.mk node4 0) (enter net (Port.mk ndB 2))
    
    let interact net (ndA : int) (ndB : int) =
      match kind net ndA, kind net ndB with
      | NIL, _ | FRE, _ -> erase net ndB
      | _, NIL | _, FRE -> erase net ndA
      | LAM, APP | APP, LAM
      | DUP, SUP | SUP, DUP -> annihilate net ndA ndB
      | _ -> commute net ndA ndB
      freeNode net ndA
      freeNode net ndB

    