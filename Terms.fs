namespace ITT

module Terms =

  open Nets
  open System.Collections.Generic
  open System


  [<AbstractClass; AllowNullLiteral>]
  type Term () = class end
  
  type Nil () =
    inherit Term ()
  
  type Var (name) =
    inherit Term ()
    member val Name : string = name with get, set
  
  type Lam (name, body) =
    inherit Term ()
    member val Name : string = name with get, set
    member val Body : Term = body with get, set
  
  type App (func, argm) =
    inherit Term ()
    member val Func : Term = func with get, set
    member val Argm : Term = argm with get, set
  
  type Sup (left, right) =
    inherit Term ()
    member val Left : Term = left with get, set
    member val Right : Term = right with get, set
  
  type Ann (trm, typ) =
    inherit Term ()
    member val Term : Term = trm with get, set
    member val Type : Term = typ with get, set

  type Chk (trm, typ) =
    inherit Term ()
    member val Term : Term = trm with get, set
    member val Type : Term = typ with get, set
  
  type Arr (dom, cod) =
    inherit Term ()
    member val Domain : Term = dom with get, set
    member val Codomain : Term = cod with get, set
  
  type Fre (trm, bod) =
    inherit Term ()
    member val Term : Term = trm with get, set
    member val Body : Term = bod with get, set
  
  type Dup (left, right, trm, bod) =
    inherit Term ()
    member val Left : string = left with get, set
    member val Right : string = right with get, set
    member val Term : Term = trm with get, set
    member val Body : Term = bod with get, set
  
  type Dec (left, right, typ, bod) =
    inherit Term ()
    member val Left : string = left with get, set
    member val Right : string = right with get, set
    member val Type : Term = typ with get, set
    member val Body : Term = bod with get, set


  //⇓ ⇒ ← →
  let rec show (trm : Term) =
    match trm with
    | null -> failwith "null term"
    | :? Nil -> "()"
    | :? Var as var -> var.Name
    | :? Lam as lam -> $"λ{lam.Name}.{show lam.Body}"
    | :? App as app -> $"({show app.Func} {show app.Argm})"
    | :? Sup as sup -> $"{show sup.Left} ⊗ {show sup.Right})"
    | :? Ann as ann -> $"({show ann.Term} : {show ann.Type})"
    | :? Chk as chk -> $"{show chk.Term} ⇓ {show chk.Type}"
    | :? Arr as arr -> $"{show arr.Domain} ⇒ {show arr.Codomain}"
    | :? Fre as fre -> $"free {show fre.Term}; {show fre.Body}"
    | :? Dup as dup -> $"{dup.Left} ⊗ {dup.Right} ← {show dup.Term}; {show dup.Body}"
    | :? Dec as dec -> $"{dec.Left} ⇒ {dec.Right} ← {show dec.Type}; {show dec.Body}"
    | _ -> failwith "invalid term"

  let rec encode net
    (scope : Dictionary<string, Port>)
    (vars : ResizeArray<string * Port>)
    (up : Port)
    (trm : Term) =
    let inline go u t = encode net scope vars u t
    match trm with
    | :? Nil ->
      let nil = mkNode net NIL
      link net (Port.mk nil 1) (Port.mk nil 2)
      Port.mk nil 0
    | :? Var as trm ->
      vars.Add (trm.Name, up)
      up
    | :? Lam as trm ->
      let lam = mkNode net LAM
      scope.Add (trm.Name, Port.mk lam 1)
      link net (Port.mk lam 2) (go (Port.mk lam 2) trm.Body)
      Port.mk lam 0
    | :? App as trm ->
      let app = mkNode net APP
      link net (Port.mk app 0) (go (Port.mk app 0) trm.Func)
      link net (Port.mk app 1) (go (Port.mk app 1) trm.Argm)
      Port.mk app 2
    | :? Sup as trm ->
      let sup = mkNode net SUP
      link net (Port.mk sup 1) (go (Port.mk sup 1) trm.Left)
      link net (Port.mk sup 2) (go (Port.mk sup 2) trm.Right)
      Port.mk sup 0
    | :? Dup as trm ->
      let dup = mkNode net DUP
      scope.Add (trm.Left, Port.mk dup 1)
      scope.Add (trm.Right, Port.mk dup 2)
      link net (Port.mk dup 0) (go (Port.mk dup 0) trm.Term)
      go up trm.Body
    | :? Fre as trm ->
      let fre = mkNode net FRE
      link net (Port.mk fre 1) (Port.mk fre 2)
      link net (Port.mk fre 0) (go (Port.mk fre 0) trm.Term)
      go up trm.Body
    | :? Dec as trm ->
      let dec = mkNode net DEC
      scope.Add (trm.Left, Port.mk dec 1)
      scope.Add (trm.Right, Port.mk dec 2)
      link net (Port.mk dec 0) (go (Port.mk dec 0) trm.Type)
      go up trm.Body
    | :? Arr as trm ->
      let arr = mkNode net ARR
      link net (Port.mk arr 1) (go (Port.mk arr 1) trm.Domain)
      link net (Port.mk arr 2) (go (Port.mk arr 2) trm.Codomain)
      Port.mk arr 0
    | :? Ann as trm ->
      let ann = mkNode net ANN
      link net (Port.mk ann 1) (go (Port.mk ann 1) trm.Type)
      link net (Port.mk ann 2) (go (Port.mk ann 2) trm.Term)
      Port.mk ann 0
    | :? Chk as trm ->
      let chk = mkNode net CHK
      link net (Port.mk chk 1) (go (Port.mk chk 1) trm.Type)
      link net (Port.mk chk 0) (go (Port.mk chk 0) trm.Term)
      Port.mk chk 2

  let inject net (host : Port) (term : Term) =
    let scope = Dictionary<string, Port> ()
    let vars = ResizeArray<string * Port> ()
    let main = encode net scope vars host term
    for x, port in vars do
      match scope.TryGetValue x with
      | true, next ->
        if enter net next <> next then
          failwith $"Variable {x} is bound more than once."
        link net port next
      | false, _ -> failwith $"Variable {x} is not bound."
    for KeyValue (_, port) in scope do
      if enter net port = port then
        let fre = mkNode net FRE
        link net (Port.mk fre 1) (Port.mk fre 2)
        link net (Port.mk fre 0) port
    link net host main
  
  let build (term : Term) =
    let net = Net ()
    inject net (Port.mk (getRoot net) 0) term
    net

  let indexToName (index : int) =
    let sb = Text.StringBuilder ()
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
  
  let getNodes (net : Net) =
    let result = ResizeArray<int> ()
    for addr = 1 to net.Nodes.Count / 4 - 1 do
      if not (net.Reuse.Contains addr) then
        result.Add addr
    result

  let termOfNode net vars node =
    match kind net node with
    | ROOT -> failwith "cannot convert root node to expression"
    | NIL -> Nil () :> Term
    | LAM -> Lam (nameOf vars (Port.mk node 1), null)
    | APP -> App (null, null)
    | SUP -> Sup (null, null)
    | ANN -> Ann (null, null)
    | CHK -> Chk (null, null)
    | ARR -> Arr (null, null)
    | FRE -> Fre (null, null)
    | DUP -> 
      let x = nameOf vars (Port.mk node 1)
      let y = nameOf vars (Port.mk node 2)
      Dup (x, y, null, null)
    | DEC ->
      let x = nameOf vars (Port.mk node 1)
      let y = nameOf vars (Port.mk node 2)
      Dec (x, y, null, null)
  
  let connect net
    (vars : Dictionary<Port, string>)
    (trms : Dictionary<int, Term>)
    (fres : ResizeArray<Fre>)
    (dups : ResizeArray<Dup>)
    (decs : ResizeArray<Dec>)
    node =
    let getTerm slot =
      let port = enter net (Port.mk node slot)
      match vars.TryGetValue port with
      | true, name -> (Var name) :> Term
      | false, _ -> trms[Port.address port]
    match kind net node with
    | ROOT -> failwith "cannot connect root node"
    | NIL -> ()
    | LAM ->
      let lam = trms[node] :?> Lam
      lam.Body <- getTerm 2
    | APP ->
      let app = trms[node] :?> App
      app.Func <- getTerm 0
      app.Argm <- getTerm 1
    | SUP ->
      let sup = trms[node] :?> Sup
      sup.Left <- getTerm 1
      sup.Right <- getTerm 2
    | ANN ->
      let ann = trms[node] :?> Ann
      ann.Term <- getTerm 2
      ann.Type <- getTerm 1
    | CHK ->
      let chk = trms[node] :?> Chk
      chk.Term <- getTerm 0
      chk.Type <- getTerm 1
    | ARR ->
      let arr = trms[node] :?> Arr
      arr.Domain <- getTerm 1
      arr.Codomain <- getTerm 2
    | FRE ->
      let fre = trms[node] :?> Fre
      fre.Term <- getTerm 0
      fres.Add fre
    | DUP ->
      let dup = trms[node] :?> Dup
      dup.Term <- getTerm 0
      dups.Add dup
    | DEC ->
      let dec = trms[node] :?> Dec
      dec.Type <- getTerm 1
      dec.Body <- getTerm 0
      decs.Add dec
  
  let readback net =
    let nodes = getNodes net
    let fres = ResizeArray<Fre> ()
    let dups = ResizeArray<Dup> ()
    let decs = ResizeArray<Dec> ()
    let vars = Dictionary<Port, string> ()
    let trms = Dictionary<int, Term> ()
    for node in nodes do
      let trm = termOfNode net vars node
      trms.Add (node, trm)
    for node in nodes do
      connect net vars trms fres dups decs node
    let mutable res = trms[getFirst net]
    for dup in dups do
      dup.Body <- res
      res <- dup
    for dec in decs do
      dec.Body <- res
      res <- dec
    for fre in fres do
      fre.Body <- res
      res <- fre
    res
  
  let roundtrip (term : Term) =
    readback (build term)
  