namespace ITT

module Core =

  type Term =
    | Nil
    | Var of string
    | Lam of string * Term
    | App of Term * Term
    | Sup of Term * Term
    | Ann of Term * Term
    | Chk of Term * Term
    | Arr of Term * Term
    | Fre of Term * Term
    | Dup of string * string * Term * Term
    | Dec of string * string * Term * Term
  
  
  let rec show (trm : Term) =
    match trm with
    | Nil -> "()"
    | Var x -> x
    | Lam (x, t) -> $"λ{x}.{show t}"
    | App (f, a) -> $"({show f} {show a})"
    | Sup (t1, t2) -> $"({show t1} ⊗ {show t2})"
    | Ann (t, typ) -> $"({show t} : {show typ})"
    | Chk (t, typ) -> $"check[{show t}][{show typ}]"
    | Arr (a, b) -> $"({show a} → {show b})"
    | Fre (t, u) -> $"free[{show t}]; {show u}"
    | Dup (x, y, t, u) -> $"match {x} ⊗ {y} = {show t}; {show u}"
    | Dec (x, y, t, u) -> $"match {x} → {y} = {show t}; {show u}"


  module Net =

    open System.Collections.Generic

    type Kind =
      | ROOT
      | NIL
      | LAM
      | APP
      | SUP
      | ANN
      | CHK
      | ARR
      | FRE
      | DUP
      | DEC
    with
      static member inline arity (kind : Kind) =
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
        | 7 -> ARR
        | 8 -> FRE
        | 9 -> DUP
        | 10 -> DEC
        | _ -> failwith $"Invalid kind: {i}"
      
      static member toInt (kind : Kind) =
        match kind with
        | ROOT -> 0
        | NIL -> 1
        | LAM -> 2
        | APP -> 3
        | SUP -> 4
        | ANN -> 5
        | CHK -> 6
        | ARR -> 7
        | FRE -> 8
        | DUP -> 9
        | DEC -> 10
    
    type Net =
      { Nodes : ResizeArray<int>
        Reuse : Stack<int>
        mutable Rules : int
      }
    with
      static member ctor () =
        let nodes = ResizeArray<int> 256
        nodes.AddRange [| 2; 1; 0; 0 |]
        { Nodes = nodes
          Reuse = Stack<int> ()
          Rules = 0
        }

    [<Measure>]
    type uomPort
    
    type Port = int<uomPort>

    [<RequireQualifiedAccess>]
    module Port =

      let inline mk (address : int) (slot : int) : Port =
        LanguagePrimitives.Int32WithMeasure ((address <<< 2) ||| slot)
      
      let inline address (port : Port) = int port >>> 2

      let inline slot (port : Port) = int port &&& 3
    

    let mkNode (net : Net) (kind : Kind) =
      match net.Reuse.TryPop () with
      | true, nd -> 
        let addr = nd
        net.Nodes[int (Port.mk addr 0)] <- int (Port.mk addr 0)
        net.Nodes[int (Port.mk addr 1)] <- int (Port.mk addr 1)
        net.Nodes[int (Port.mk addr 2)] <- int (Port.mk addr 2)
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

    let enter (net : Net) (port : Port) : Port =
      LanguagePrimitives.Int32WithMeasure net.Nodes[int port]
    
    let kind (net : Net) (node : int) =
      Kind.fromInt (net.Nodes[int <| Port.mk node 3])
    
    let link (net : Net) (portA : Port) (portB : Port) =
      net.Nodes[int portA] <- int portB
      net.Nodes[int portB] <- int portA
    
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
      | DUP | DEC ->
        let nil1 = mkNode net NIL
        let nil2 = mkNode net NIL
        link net (enter net (Port.mk nd 1)) (enter net (Port.mk nil1 0))
        link net (enter net (Port.mk nd 2)) (enter net (Port.mk nil2 0))
      | SUP | ARR | ANN ->
        let fre1 = mkNode net FRE
        let fre2 = mkNode net FRE
        link net (enter net (Port.mk nd 1)) (enter net (Port.mk fre1 0))
        link net (enter net (Port.mk nd 2)) (enter net (Port.mk fre2 0))

    let commute net (ndA : int) (ndB : int) =
      let node1, node2, node3, node4 =
        match kind net ndA, kind net ndB with
        | LAM, DUP -> mkNode net SUP, mkNode net DUP, mkNode net LAM, mkNode net LAM
        | DUP, LAM -> mkNode net LAM, mkNode net LAM, mkNode net SUP, mkNode net DUP
        | ARR, DUP -> mkNode net DUP, mkNode net DUP, mkNode net ARR, mkNode net ARR
        | DUP, ARR -> mkNode net ARR, mkNode net ARR, mkNode net DUP, mkNode net DUP
        | LAM, CHK -> mkNode net ANN, mkNode net CHK, mkNode net DEC, mkNode net LAM
        | CHK, LAM -> mkNode net DEC, mkNode net LAM, mkNode net ANN, mkNode net CHK
        | SUP, CHK -> mkNode net CHK, mkNode net CHK, mkNode net DUP, mkNode net SUP
        | CHK, SUP -> mkNode net DUP, mkNode net SUP, mkNode net CHK, mkNode net CHK
        | ANN, APP -> mkNode net DEC, mkNode net APP, mkNode net CHK, mkNode net ANN
        | APP, ANN -> mkNode net CHK, mkNode net ANN, mkNode net DEC, mkNode net APP
        | SUP, APP -> mkNode net APP, mkNode net APP, mkNode net DUP, mkNode net SUP
        | APP, SUP -> mkNode net DUP, mkNode net SUP, mkNode net APP, mkNode net APP
        | ARR, APP -> mkNode net APP, mkNode net APP, mkNode net DEC, mkNode net ARR
        | APP, ARR -> mkNode net DEC, mkNode net ARR, mkNode net APP, mkNode net APP
        | SUP, DEC -> mkNode net DEC, mkNode net DEC, mkNode net SUP, mkNode net SUP
        | DEC, SUP -> mkNode net SUP, mkNode net SUP, mkNode net DEC, mkNode net DEC
        | LAM, DEC -> mkNode net ARR, mkNode net DEC, mkNode net LAM, mkNode net LAM
        | DEC, LAM -> mkNode net LAM, mkNode net LAM, mkNode net ARR, mkNode net DEC
        | kindA, kindB -> failwith $"cannot commute {kindA} and {kindB}"
      link net (Port.mk node1 1) (Port.mk node3 1)
      link net (Port.mk node1 2) (Port.mk node4 1)
      link net (Port.mk node2 1) (Port.mk node3 2)
      link net (Port.mk node2 2) (Port.mk node4 2)
      link net (Port.mk node1 0) (enter net (Port.mk ndA 1))
      link net (Port.mk node2 0) (enter net (Port.mk ndA 2))
      link net (Port.mk node3 0) (enter net (Port.mk ndB 1))
      link net (Port.mk node4 0) (enter net (Port.mk ndB 2))
    
    // Assumes the nodes form an active pair.
    let interact net (ndA : int) (ndB : int) =
      match kind net ndA, kind net ndB with
      | NIL, _ | FRE, _ -> erase net ndB
      | _, NIL | _, FRE -> erase net ndA
      | LAM, APP | APP, LAM
      | DUP, SUP | SUP, DUP
      | ARR, DEC | DEC, ARR
      | CHK, ANN | ANN, CHK -> annihilate net ndA ndB
      | _ -> commute net ndA ndB

    let rec encode net
      (scope : Dictionary<string, Port>)
      (vars : ResizeArray<string * Port>)
      (up : Port)
      (trm : Term) =
      let inline go u t = encode net scope vars u t
      match trm with
      | Nil ->
        let nil = mkNode net NIL
        Port.mk nil 0
      | Var x ->
        vars.Add (x, up)
        up
      | Lam (x, t) ->
        let lam = mkNode net LAM
        scope.Add (x, Port.mk lam 1)
        link net (Port.mk lam 2) (go (Port.mk lam 2) t)
        Port.mk lam 0
      | App (f, a) ->
        let app = mkNode net APP
        link net (Port.mk app 0) (go (Port.mk app 0) f)
        link net (Port.mk app 1) (go (Port.mk app 1) a)
        Port.mk app 2
      | Sup (t1, t2) ->
        let sup = mkNode net SUP
        link net (Port.mk sup 1) (go (Port.mk sup 1) t1)
        link net (Port.mk sup 2) (go (Port.mk sup 2) t2)
        Port.mk sup 0
      | Dup (x, y, t, u) ->
        let dup = mkNode net DUP
        scope.Add (x, Port.mk dup 1)
        scope.Add (y, Port.mk dup 2)
        link net (Port.mk dup 0) (go (Port.mk dup 0) t)
        go up u
      | Fre (t, u) ->
        let fre = mkNode net FRE
        link net (Port.mk fre 0) (go (Port.mk fre 0) t)
        go up u
      | Dec (x, y, t, u) ->
        let dec = mkNode net DEC
        scope.Add (x, Port.mk dec 1)
        scope.Add (y, Port.mk dec 2)
        link net (Port.mk dec 0) (go (Port.mk dec 0) t)
        go up u
      | Arr (a, b) ->
        let arr = mkNode net ARR
        link net (Port.mk arr 1) (go (Port.mk arr 1) a)
        link net (Port.mk arr 2) (go (Port.mk arr 2) b)
        Port.mk arr 0
      | Ann (t, typ) ->
        let ann = mkNode net ANN
        link net (Port.mk ann 1) (go (Port.mk ann 1) typ)
        link net (Port.mk ann 2) (go (Port.mk ann 2) t)
        Port.mk ann 0
      | Chk (t, typ) ->
        let chk = mkNode net CHK
        link net (Port.mk chk 1) (go (Port.mk chk 1) typ)
        link net (Port.mk chk 0) (go (Port.mk chk 0) t)
        Port.mk chk 2

    let inject net (host : Port) (term : Term) =
      let scope = Dictionary<string, Port> ()
      let vars = ResizeArray<string * Port> ()
      let root = encode net scope vars host term
      for x, port in vars do
        match scope.TryGetValue x with
        | true, next ->
          if enter net next <> next then
            failwith $"Variable {x} is bound more than once."
          link net port next
        | false, _ -> failwith $"Variable {x} is not bound."
        scope[x] <- port
      for KeyValue (_, port) in scope do
        if enter net port = port then
          let fre = mkNode net FRE
          link net (Port.mk fre 0) port
      link net (enter net host) root
    
    let fromTerm (term : Term) =
      let net = Net.ctor ()
      let root = mkNode net ROOT
      inject net (Port.mk root 0) term
      root

    let indexToName (index : int) =
      let sb = System.Text.StringBuilder ()
      let mutable idx = index
      while idx > 0 do
        sb.Append (char ((idx - 1) % 26 + 97)) |> ignore
        idx <- idx / 26
      sb.ToString ()
    
    let nameOf (vars : Dictionary<Port, string>) (varPort : Port) =
      match vars.TryGetValue varPort with
      | true, name -> name
      | false, _ ->
        let name = indexToName (vars.Count + 1)
        vars.Add (varPort, name)
        name
    
    type Uniques =
      { Vec : ResizeArray<int>
        Set : HashSet<int>
      }
    with
      static member ctor () =
        { Vec = ResizeArray<int> ()
          Set = HashSet<int> ()
        }
      member this.Add (node : int) =
        if this.Set.Add node then this.Vec.Add node
      
    
    let rec readTerm net
      (fres : Uniques)
      (dups : Uniques)
      (decs : Uniques)
      (vars : Dictionary<Port, string>)
      (seen : HashSet<Port>)
      (next : Port) =
      if not (seen.Add next) then
        Var "..."
      else
        let inline go p = readTerm net fres dups decs vars seen p
        match kind net (Port.address next) with
        | ROOT -> go (enter net next)
        | NIL -> Nil
        | LAM ->
          match Port.slot next with
          | 0 ->
            let x = nameOf vars (Port.mk (Port.address next) 1)
            let t = enter net (Port.mk (Port.address next) 2)
            Lam (x, go t)
          | 1 ->
            Var (nameOf vars next)
          | _ -> failwith "Invalid port"
        | APP ->
          let f = enter net (Port.mk (Port.address next) 0)
          let a = enter net (Port.mk (Port.address next) 1)
          App (go f, go a)
        | SUP ->
          let t1 = enter net (Port.mk (Port.address next) 1)
          let t2 = enter net (Port.mk (Port.address next) 2)
          Sup (go t1, go t2)
        | ANN ->
          let t = enter net (Port.mk (Port.address next) 2)
          let typ = enter net (Port.mk (Port.address next) 1)
          Ann (go t, go typ)
        | CHK ->
          let t = enter net (Port.mk (Port.address next) 0)
          let typ = enter net (Port.mk (Port.address next) 1)
          Chk (go t, go typ)
        | ARR ->
          let a = enter net (Port.mk (Port.address next) 1)
          let b = enter net (Port.mk (Port.address next) 2)
          Arr (go a, go b)
        | FRE ->
          fres.Add (Port.address next)
          Var (nameOf vars next)
        | DUP ->
          dups.Add (Port.address next)
          Var (nameOf vars next)
        | DEC ->
          decs.Add (Port.address next)
          Var (nameOf vars next)

    let toTerm net (host : Port) =
      let fres = Uniques.ctor ()
      let dups = Uniques.ctor ()
      let decs = Uniques.ctor ()
      let vars = Dictionary<Port, string> ()
      let seen = HashSet<Port> ()
      let inline go port = readTerm net fres dups decs vars seen port
      let mutable res = go host
      for freNode in fres.Vec do
        let t = go (enter net (Port.mk freNode 0))
        res <- Fre (t, res)
      for dupNode in dups.Vec do
        let t = go (enter net (Port.mk dupNode 0))
        let x = nameOf vars (Port.mk dupNode 1)
        let y = nameOf vars (Port.mk dupNode 2)
        res <- Dup (x, y, t, res)
      for decNode in decs.Vec do
        let t = go (enter net (Port.mk decNode 0))
        let x = nameOf vars (Port.mk decNode 1)
        let y = nameOf vars (Port.mk decNode 2)
        res <- Dec (x, y, t, res)
      res
    
    let roundtrip (term : Term) =
      let net = Net.ctor ()
      let root = mkNode net ROOT
      inject net (Port.mk root 0) term
      let res = toTerm net (enter net (Port.mk root 0))
      res