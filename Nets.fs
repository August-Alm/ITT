namespace ITT

module Nets =

  open System.Collections.Generic
  open LanguagePrimitives

  type Kind =
    | ROOT = 0
    | NIL = 1
    | LAM = 2
    | APP = 3
    | SUP = 4
    | THE = 5
    | CHK = 6
    | FRE = 7
    | DUP = 8
    | UNI = 9
  
  [<RequireQualifiedAccess>]
  module Kind =
    let inline toInt (kind : Kind) = int kind
    let inline ofInt (k : int) = EnumOfValue<int, Kind> k

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
    let reuse = Reuse ()
    let redices = Stack<struct (int * int)> 512
    let mutable rewrites = 0
    do nodes.AddRange [| 2; 1; 0; 0 |]
    member _.Nodes = nodes
    member _.Reuse = reuse
    member _.Redices = redices
    member _.Rewrites with get () = rewrites and set v = rewrites <- v


  [<Measure>]
  type uomPort
  
  type Port = int<uomPort>

  [<RequireQualifiedAccess>]
  module Port =

    let inline mk (address : int) (slot : int) : Port =
      Int32WithMeasure ((address <<< 2) ||| slot)
    
    let inline address (port : Port) = int port >>> 2

    let inline slot (port : Port) = int port &&& 3
  

  module Net =

    let inline getRoot (net : Net) = 0

    let getNodes (net : Net) =
      let result = ResizeArray<int> ()
      for addr = 1 to net.Nodes.Count / 4 - 1 do
        if not (net.Reuse.Contains addr) then
          result.Add addr
      Array.ofSeq result

    let enter (net : Net) (port : Port) : Port =
      Int32WithMeasure net.Nodes[int port]
  
    let kind (net : Net) (node : int) =
      Kind.ofInt (net.Nodes[int <| Port.mk node 3])
  
    let getFirst net =
      Port.address (enter net (Port.mk (getRoot net) 0))

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
  
    let inline freeNode (net : Net) nd =
      net.Reuse.Push nd


  module Interaction =

    open Net

    let interact_NIL_FRE net (nil : int) (fre : int) =
      freeNode net nil
      freeNode net fre

    let interact_NIL_APP net (nil : int) (app : int) =
      let fre = mkNode net Kind.FRE
      link net (Port.mk nil 0) (enter net (Port.mk app 2))
      link net (Port.mk fre 0) (enter net (Port.mk app 1))
      freeNode net app

    let interact_NIL_DUP net (nil : int) (dup : int) =
      let nil1 = nil
      let nil2 = mkNode net Kind.NIL
      link net (Port.mk nil1 0) (enter net (Port.mk dup 1))
      link net (Port.mk nil2 0) (enter net (Port.mk dup 2))
      freeNode net dup

    let interact_NIL_CHK net (nil : int) (chk : int) =
      link net (Port.mk nil 0) (enter net (Port.mk chk 1))
      freeNode net chk
    
    let interact_LAM_FRE net (lam : int) (fre : int) =
      let nil = mkNode net Kind.NIL
      link net (Port.mk fre 0) (enter net (Port.mk lam 2))
      link net (Port.mk nil 0) (enter net (Port.mk lam 1))
      freeNode net lam
    
    let interact_LAM_APP net (lam : int) (app : int) =
      link net (enter net (Port.mk app 1)) (enter net (Port.mk lam 1))
      link net (enter net (Port.mk app 2)) (enter net (Port.mk lam 2))
      freeNode net lam
      freeNode net app

    let interact_LAM_DUP net (lam : int) (dup : int) =
      let lam1 = mkNode net Kind.LAM
      let lam2 = mkNode net Kind.LAM
      let sup' = mkNode net Kind.SUP
      let dup' = mkNode net Kind.DUP
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
    
    let interact_SUP_FRE net (sup : int) (fre : int) =
      let fre1 = fre
      let fre2 = mkNode net Kind.FRE
      link net (Port.mk fre1 0) (enter net (Port.mk sup 1))
      link net (Port.mk fre2 0) (enter net (Port.mk sup 2))
      freeNode net sup
    
    let interact_SUP_APP net (sup : int) (app : int) =
      let app1 = mkNode net Kind.APP
      let app2 = mkNode net Kind.APP
      let sup' = mkNode net Kind.SUP
      let dup' = mkNode net Kind.DUP
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
      let chk1 = mkNode net Kind.CHK
      let chk2 = mkNode net Kind.CHK
      let sup' = mkNode net Kind.SUP
      let dup' = mkNode net Kind.DUP
      link net (Port.mk dup' 0) (enter net (Port.mk chk 2))
      link net (Port.mk dup' 1) (Port.mk chk1 2)
      link net (Port.mk dup' 2) (Port.mk chk2 2)
      link net (Port.mk sup' 0) (enter net (Port.mk chk 1))
      link net (Port.mk sup' 1) (Port.mk chk1 1)
      link net (Port.mk sup' 2) (Port.mk chk2 1)
      link net (Port.mk chk1 0) (enter net (Port.mk sup 1))
      link net (Port.mk chk2 0) (enter net (Port.mk sup 2))
      freeNode net sup
      freeNode net chk
    
    let interact_THE_FRE net (the : int) (fre : int) =
      let nil = mkNode net Kind.NIL
      link net (Port.mk fre 0) (enter net (Port.mk the 2))
      link net (Port.mk nil 0) (enter net (Port.mk the 1))
      freeNode net the
    
    let interact_THE_CHK net (the : int) (chk : int) =
      link net (enter net (Port.mk chk 2)) (enter net (Port.mk the 1))
      link net (enter net (Port.mk chk 1)) (enter net (Port.mk the 2))
      freeNode net the
      freeNode net chk

    let interact_THE_DUP net (the : int) (dup : int) =
      let the1 = mkNode net Kind.THE
      let the2 = mkNode net Kind.THE
      let sup' = mkNode net Kind.SUP
      let dup' = mkNode net Kind.DUP
      link net (Port.mk the1 0) (enter net (Port.mk dup 1))
      link net (Port.mk the1 1) (Port.mk sup' 1)
      link net (Port.mk the1 2) (Port.mk dup' 1)
      link net (Port.mk the2 0) (enter net (Port.mk dup 2))
      link net (Port.mk the2 1) (Port.mk sup' 2)
      link net (Port.mk the2 2) (Port.mk dup' 2)
      link net (Port.mk dup' 0) (enter net (Port.mk the 2))
      link net (Port.mk sup' 0) (enter net (Port.mk the 1))
      freeNode net the
      freeNode net dup

    let interact_UNI_FRE net (uni : int) (fre : int) =
      freeNode net uni
      freeNode net fre

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
      | Kind.LAM, Kind.CHK -> ()
      | Kind.CHK, Kind.LAM -> ()
      | Kind.SUP, Kind.FRE -> interact_SUP_FRE net nd1 nd2
      | Kind.FRE, Kind.SUP -> interact_SUP_FRE net nd2 nd1
      | Kind.SUP, Kind.APP -> interact_SUP_APP net nd1 nd2
      | Kind.APP, Kind.SUP -> interact_SUP_APP net nd2 nd1
      | Kind.SUP, Kind.DUP -> interact_SUP_DUP net nd1 nd2
      | Kind.DUP, Kind.SUP -> interact_SUP_DUP net nd2 nd1
      | Kind.SUP, Kind.CHK -> interact_SUP_CHK net nd1 nd2
      | Kind.CHK, Kind.SUP -> interact_SUP_CHK net nd2 nd1
      | Kind.THE, Kind.FRE -> interact_THE_FRE net nd1 nd2
      | Kind.FRE, Kind.THE -> interact_THE_FRE net nd2 nd1
      | Kind.THE, Kind.DUP -> interact_THE_DUP net nd1 nd2
      | Kind.DUP, Kind.THE -> interact_THE_DUP net nd2 nd1
      | Kind.THE, Kind.CHK -> interact_THE_CHK net nd1 nd2
      | Kind.CHK, Kind.THE -> interact_THE_CHK net nd2 nd1
      | Kind.THE, Kind.APP -> ()
      | Kind.APP, Kind.THE -> ()
      | Kind.UNI, Kind.FRE -> interact_UNI_FRE net nd1 nd2
      | Kind.FRE, Kind.UNI -> interact_UNI_FRE net nd2 nd1
      | Kind.CHK, Kind.UNI -> ()
      | Kind.UNI, Kind.CHK -> ()
      | k1, k2 -> failwith $"invalid interaction: {k1} {k2}"
    
    let reduce (net : Net) =
      while net.Redices.Count > 0 do
        let struct (nd1, nd2) = net.Redices.Pop ()
        Debug.printfn "interaction {kind net nd1} ~~ {kind net nd2}"
        interact net nd1 nd2
      net.Rewrites