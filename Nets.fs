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
      | ANN | CHK -> 2
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
    let reuse = Reuse ()
    let redices = Stack<struct (int * int)> 512
    let mutable rewrites = 0
    do nodes.AddRange [| 2; 1; 0; 0 |]
    member _.Nodes = nodes
    member _.Types = types
    member _.Reuse = reuse
    member _.Redices = redices
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
  

  module Net =

    let inline getRoot (net : Net) = 0

    let getNodes (net : Net) =
      let result = ResizeArray<int> ()
      for addr = 1 to net.Nodes.Count / 4 - 1 do
        if not (net.Reuse.Contains addr) then
          result.Add addr
      result

    let inline enter (net : Net) (port : Port) : Port =
      LanguagePrimitives.Int32WithMeasure net.Nodes[int port]
  
    let kind (net : Net) (node : int) =
      Kind.fromInt (net.Nodes[int <| Port.mk node 3])
  
    let getFirst net =
      Port.address (enter net (Port.mk (getRoot net) 0))

    let getType (net : Net) (node : int) =
      match kind net node with
      |  Kind.ANN | Kind.CHK -> net.Types[net.Nodes[int <| Port.mk node 2]]
      | _ -> failwith "only ANN and CHK nodes have a type"
  
    let setType (net : Net) (node : int) (typ : Type) =
      match kind net node with
      |  Kind.ANN | Kind.CHK -> net.Types[net.Nodes[int <| Port.mk node 2]] <- typ
      | _ -> failwith "only ANN and CHK nodes have a type"

    let inline private set (net : Net) (portA : Port) (portB : Port) =
      net.Nodes[int portA] <- int portB
  
    let link (net : Net) (portA : Port) (portB : Port) =
      set net portA portB; set net portB portA
      let addrA = Port.address portA
      let addrB = Port.address portB
      if
        (Port.slot portA = 0 && Port.slot portB = 0) &&
        (addrA <> getRoot net) &&
        (addrB <> getRoot net) &&
        (addrA <> addrB)
      then
        net.Redices.Push (struct (addrA, addrB))
  
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
  
    let mkChkNode (net : Net) (typ : Type) =
      match net.Reuse.TryPop () with
      | true, addr -> 
        set net (Port.mk addr 0) (Port.mk addr 0)
        set net (Port.mk addr 1) (Port.mk addr 1)
        set net (Port.mk addr 2) (LanguagePrimitives.Int32WithMeasure net.Types.Count)
        net.Types.Add typ
        //setType net addr typ
        net.Nodes[int (Port.mk addr 3)] <- Kind.toInt Kind.CHK
        addr
      | false, _ ->
        let len = net.Nodes.Count
        net.Nodes.EnsureCapacity (len + 4) |> ignore
        let addr = len / 4
        net.Nodes.Add (int (Port.mk addr 0))
        net.Nodes.Add (int (Port.mk addr 1))
        net.Nodes.Add (net.Types.Count)
        net.Types.Add typ
        net.Nodes.Add (Kind.toInt Kind.CHK)
        addr
  
    let mkAnnNode (net : Net) (typ : Type) =
      match net.Reuse.TryPop () with
      | true, addr -> 
        set net (Port.mk addr 0) (Port.mk addr 0)
        set net (Port.mk addr 1) (Port.mk addr 1)
        set net (Port.mk addr 2) (LanguagePrimitives.Int32WithMeasure net.Types.Count)
        net.Types.Add typ
        //setType net addr typ
        net.Nodes[int (Port.mk addr 3)] <- Kind.toInt Kind.ANN
        addr
      | false, _ ->
        let len = net.Nodes.Count
        net.Nodes.EnsureCapacity (len + 4) |> ignore
        let addr = len / 4
        net.Nodes.Add (int (Port.mk addr 0))
        net.Nodes.Add (int (Port.mk addr 1))
        net.Nodes.Add (net.Types.Count)
        net.Types.Add typ
        net.Nodes.Add (Kind.toInt Kind.ANN)
        addr

    let inline freeNode (net : Net) nd =
      net.Reuse.Push nd


  module Interaction =

    open Net

    let interact_NIL_FRE net (nil : int) (fre : int) =
      freeNode net nil
      freeNode net fre

    let interact_NIL_APP net (nil : int) (app : int) =
      let fre = mkNode net FRE
      link net (Port.mk nil 0) (enter net (Port.mk app 2))
      link net (Port.mk fre 0) (enter net (Port.mk app 1))
      freeNode net app

    let interact_NIL_DUP net (nil : int) (dup : int) =
      let nil1 = nil
      let nil2 = mkNode net NIL
      link net (Port.mk nil1 0) (enter net (Port.mk dup 1))
      link net (Port.mk nil2 0) (enter net (Port.mk dup 2))
      freeNode net dup

    let interact_NIL_CHK net (nil : int) (chk : int) =
      link net (Port.mk nil 0) (enter net (Port.mk chk 1))
      freeNode net chk
    
    let interact_LAM_FRE net (lam : int) (fre : int) =
      let nil = mkNode net NIL
      link net (Port.mk fre 0) (enter net (Port.mk lam 2))
      link net (Port.mk nil 0) (enter net (Port.mk lam 1))
      freeNode net lam
    
    let interact_LAM_APP net (lam : int) (app : int) =
      link net (enter net (Port.mk app 1)) (enter net (Port.mk lam 1))
      link net (enter net (Port.mk app 2)) (enter net (Port.mk lam 2))
      freeNode net lam
      freeNode net app

    let interact_LAM_DUP net (lam : int) (dup : int) =
      let lam1 = mkNode net LAM
      let lam2 = mkNode net LAM
      let sup' = mkNode net SUP
      let dup' = mkNode net DUP
      link net (Port.mk lam1 0) (enter net (Port.mk dup 1))
      link net (Port.mk lam1 1) (Port.mk sup' 1)
      link net (Port.mk lam1 2) (Port.mk dup' 1)
      link net (Port.mk lam2 0) (enter net (Port.mk dup 2))
      link net (Port.mk lam2 1) (Port.mk sup' 2)
      link net (Port.mk lam2 2) (Port.mk dup' 2)
      link net (Port.mk dup' 0) (enter net (Port.mk lam 2))
      link net (Port.mk sup' 0) (enter net (Port.mk lam 1))
      freeNode net lam
      freeNode net dup
    
    let private interact_3_CHK net (nd : int) (chk : int) (typ : Type) =
      let nd' = mkNode net (kind net nd)
      let chk1 = mkChkNode net typ
      let chk2 = mkChkNode net typ
      let dup = mkNode net DUP
      let fre = mkNode net FRE
      link net (Port.mk nd' 0) (Port.mk chk1 0)
      link net (Port.mk nd' 1) (enter net (Port.mk nd 1))
      link net (Port.mk nd' 2) (enter net (Port.mk nd 2))
      link net (Port.mk chk1 1) (Port.mk dup 0)
      link net (Port.mk dup 1) (Port.mk fre 0)
      link net (Port.mk dup 2) (Port.mk chk2 0)
      link net (Port.mk chk2 1) (enter net (Port.mk nd 0))
      freeNode net nd
      freeNode net chk
    
    let interact_LAM_CHK net (lam : int) (chk : int) =
      match Type.reduce (getType net chk) with
      | Box t -> interact_3_CHK net lam chk t
      | Arrow (s, a) ->
        let chk' = mkChkNode net a
        let ann' = mkAnnNode net s
        let lam' = mkNode net LAM
        link net (Port.mk lam' 0) (enter net (Port.mk chk 1))
        link net (Port.mk lam' 1) (Port.mk ann' 1)
        link net (Port.mk lam' 2) (Port.mk chk' 1)
        link net (Port.mk ann' 0) (enter net (Port.mk lam 1))
        link net (Port.mk chk' 0) (enter net (Port.mk lam 2))
        freeNode net lam
        freeNode net chk
      | _ -> failwith "cannot check lambda against non-arrow type"
    
    let interact_SUP_FRE net (sup : int) (fre : int) =
      let fre1 = fre
      let fre2 = mkNode net FRE
      link net (Port.mk fre1 0) (enter net (Port.mk sup 1))
      link net (Port.mk fre2 0) (enter net (Port.mk sup 2))
      freeNode net sup
    
    let interact_SUP_APP net (sup : int) (app : int) =
      let app1 = mkNode net APP
      let app2 = mkNode net APP
      let sup' = mkNode net SUP
      let dup' = mkNode net DUP
      link net (Port.mk sup' 0) (enter net (Port.mk app 2))
      link net (Port.mk sup' 1) (Port.mk app1 2)
      link net (Port.mk sup' 2) (Port.mk app2 2)
      link net (Port.mk dup' 0) (enter net (Port.mk app 1))
      link net (Port.mk dup' 1) (Port.mk app1 1)
      link net (Port.mk dup' 2) (Port.mk app2 1)
      link net (Port.mk app1 0) (enter net (Port.mk sup 1))
      link net (Port.mk app2 0) (enter net (Port.mk sup 2))
      freeNode net sup
      freeNode net app
    
    let interact_SUP_DUP net (sup : int) (dup : int) =
      link net (enter net (Port.mk dup 1)) (enter net (Port.mk sup 1))
      link net (enter net (Port.mk dup 2)) (enter net (Port.mk sup 2))
      freeNode net sup
      freeNode net dup
    
    let interact_SUP_CHK net (sup : int) (chk : int) =
      match getType net chk with
      | Box t -> interact_3_CHK net sup chk t
      | Tuple (a, b) ->
        let chk1 = mkChkNode net a
        let chk2 = mkChkNode net b
        let sup' = mkNode net SUP
        link net (Port.mk sup' 0) (enter net (Port.mk chk 1))
        link net (Port.mk sup' 1) (Port.mk chk1 1)
        link net (Port.mk sup' 2) (Port.mk chk2 1)
        link net (Port.mk chk1 0) (enter net (Port.mk sup 1))
        link net (Port.mk chk2 0) (enter net (Port.mk sup 2))
        freeNode net sup
        freeNode net chk
      | _ -> failwith "cannot check tensor against non-tensor type"
    
    let interact_ANN_FRE net (ann : int) (fre : int) =
      link net (Port.mk fre 0) (enter net (Port.mk ann 1))
      freeNode net ann

    let interact_ANN_APP net (ann : int) (app : int) =
      match Type.reduce (getType net ann) with
      | Box (Arrow (s, t)) | Arrow (s, t) ->
        let ann' = mkAnnNode net t
        let chk' = mkChkNode net s
        let app' = mkNode net APP
        link net (Port.mk app' 0) (enter net (Port.mk ann 1))
        link net (Port.mk app' 1) (Port.mk chk' 1)
        link net (Port.mk app' 2) (Port.mk ann' 1)
        link net (Port.mk chk' 0) (enter net (Port.mk app 1))
        link net (Port.mk ann' 0) (enter net (Port.mk app 2))
        freeNode net ann
        freeNode net app
      | _ -> failwith "cannot apply non-arrow type"

    let interact_ANN_DUP net (ann : int) (dup : int) =
      match getType net ann with
      | Box _ as typ ->
        let ann1 = mkAnnNode net typ
        let ann2 = mkAnnNode net typ
        let dup' = mkNode net DUP
        link net (Port.mk dup' 0) (enter net (Port.mk ann 1))
        link net (Port.mk dup' 1) (Port.mk ann1 1)
        link net (Port.mk dup' 2) (Port.mk ann2 1)
        link net (Port.mk ann1 0) (enter net (Port.mk dup 1))
        link net (Port.mk ann2 0) (enter net (Port.mk dup 2))
        freeNode net ann
        freeNode net dup
      | _ -> failwith "cannot duplicate non-box type"

    let interact_ANN_CHK net (ann : int) (chk : int) =
      let t = getType net chk
      let s = getType net ann
      if Type.isSubtype s t then
        link net (enter net (Port.mk chk 1)) (enter net (Port.mk ann 1))
        freeNode net ann
        freeNode net chk
      else
        failwith "type mismatch"

    let interact (net : Net) nd1 nd2 =
      net.Rewrites <- net.Rewrites + 1
      match kind net nd1, kind net nd2 with
      | Kind.NIL, Kind.FRE -> interact_NIL_FRE net nd1 nd2
      | Kind.FRE, Kind.NIL -> interact_NIL_FRE net nd2 nd1
      | Kind.NIL, Kind.APP -> interact_NIL_APP net nd1 nd2
      | Kind.APP, Kind.NIL -> interact_NIL_APP net nd2 nd1
      | Kind.NIL, Kind.DUP -> interact_NIL_DUP net nd1 nd2
      | Kind.DUP, Kind.NIL -> interact_NIL_DUP net nd2 nd1
      | Kind.NIL, Kind.CHK -> interact_NIL_CHK net nd1 nd2
      | Kind.CHK, Kind.NIL -> interact_NIL_CHK net nd2 nd1
      | Kind.LAM, Kind.FRE -> interact_LAM_FRE net nd1 nd2
      | Kind.FRE, Kind.LAM -> interact_LAM_FRE net nd2 nd1
      | Kind.LAM, Kind.APP -> interact_LAM_APP net nd1 nd2
      | Kind.APP, Kind.LAM -> interact_LAM_APP net nd2 nd1
      | Kind.LAM, Kind.DUP -> interact_LAM_DUP net nd1 nd2
      | Kind.DUP, Kind.LAM -> interact_LAM_DUP net nd2 nd1
      | Kind.LAM, Kind.CHK -> interact_LAM_CHK net nd1 nd2
      | Kind.CHK, Kind.LAM -> interact_LAM_CHK net nd2 nd1
      | Kind.SUP, Kind.FRE -> interact_SUP_FRE net nd1 nd2
      | Kind.FRE, Kind.SUP -> interact_SUP_FRE net nd2 nd1
      | Kind.SUP, Kind.APP -> interact_SUP_APP net nd1 nd2
      | Kind.APP, Kind.SUP -> interact_SUP_APP net nd2 nd1
      | Kind.SUP, Kind.DUP -> interact_SUP_DUP net nd1 nd2
      | Kind.DUP, Kind.SUP -> interact_SUP_DUP net nd2 nd1
      | Kind.SUP, Kind.CHK -> interact_SUP_CHK net nd1 nd2
      | Kind.CHK, Kind.SUP -> interact_SUP_CHK net nd2 nd1
      | Kind.ANN, Kind.FRE -> interact_ANN_FRE net nd1 nd2
      | Kind.FRE, Kind.ANN -> interact_ANN_FRE net nd2 nd1
      | Kind.ANN, Kind.APP -> interact_ANN_APP net nd1 nd2
      | Kind.APP, Kind.ANN -> interact_ANN_APP net nd2 nd1
      | Kind.ANN, Kind.DUP -> interact_ANN_DUP net nd1 nd2
      | Kind.DUP, Kind.ANN -> interact_ANN_DUP net nd2 nd1
      | Kind.ANN, Kind.CHK -> interact_ANN_CHK net nd1 nd2
      | Kind.CHK, Kind.ANN -> interact_ANN_CHK net nd2 nd1
      | k1, k2 -> failwith $"invalid interaction: {k1} {k2}"
    
    let reduce (net : Net) =
      while net.Redices.Count > 0 do
        let struct (nd1, nd2) = net.Redices.Pop ()
        printfn "interaction %A ~~ %A" (kind net nd1) (kind net nd2)
        interact net nd1 nd2
      net.Rewrites