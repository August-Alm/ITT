namespace ITT

module Terms =

  open Nets
  open System.Collections.Generic
  open System


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
  
  //⇓ ⇒ ← →
  let rec show (trm : Term) =
    match trm with
    | Nil -> "()"
    | Var x -> x
    | Lam (x, t) -> $"λ{x}.{show t}"
    | App (f, a) -> $"({show f} {show a})"
    | Sup (t1, t2) -> $"{show t1} ⊗ {show t2})"
    | Ann (t, typ) -> $"({show t} : {show typ})"
    | Chk (t, typ) -> $"{show t} ⇓ {show typ}"
    | Arr (a, b) -> $"{show a} ⇒ {show b}"
    | Fre (t, u) -> $"free {show t}; {show u}"
    | Dup (x, y, t, u) -> $"{x} ⊗ {y} ← {show t}; {show u}"
    | Dec (x, y, t, u) -> $"{x} ⇒ {y} ← {show t}; {show u}"
  
  

  [<RequireQualifiedAccess>]
  type Expr =
    | Nil
    | Var of Var
    | Lam of Lam
    | App of App
    | Sup of Sup
    | Ann of Ann
    | Chk of Chk
    | Arr of Arr
    | Fre of Fre
    | Dup of Dup
    | Dec of Dec
  and Var =
    { mutable Name : string }
  and Lam =
    { mutable Name : string
      mutable Body : Expr option
    }
  and App =
    { mutable Fun : Expr option
      mutable Arg : Expr option
    }
  and Sup =
    { mutable Left : Expr option
      mutable Right : Expr option
    }
  and Ann =
    { mutable Term : Expr option
      mutable Type : Expr option
    }
  and Chk =
    { mutable Term : Expr option
      mutable Type : Expr option
    }
  and Arr =
    { mutable Domain : Expr option
      mutable Codomain : Expr option
    }
  and Fre =
    { mutable Term : Expr option
      mutable Body : Expr option
    }
  and Dup =
    { mutable Left : string
      mutable Right : string
      mutable Term : Expr option
      mutable Body : Expr option
    }
  and Dec =
    { mutable Left : string
      mutable Right : string
      mutable Type : Expr option
      mutable Body : Expr option
    }
  
  let inline nontrivial s = not (String.IsNullOrEmpty s)
  
  let rec exprToTerm (expr : Expr) =
    match expr with
    | Expr.Nil -> Nil
    | Expr.Var var ->
      if nontrivial var.Name then Var var.Name
      else failwith "variable name is empty"
    | Expr.Lam lam ->
      match lam.Body with
      | Some body -> Lam (lam.Name, exprToTerm body)
      | None -> failwith "lambda body is missing"
    | Expr.App app ->
      match app.Fun, app.Arg with
      | Some f, Some a -> App (exprToTerm f, exprToTerm a)
      | None, _ -> failwith "application function is missing"
      | _, None -> failwith "application argument is missing"
    | Expr.Sup sup ->
      match sup.Left, sup.Right with
      | Some l, Some r -> Sup (exprToTerm l, exprToTerm r)
      | None, _ -> failwith "superposition left is missing"
      | _, None -> failwith "superposition right is missing"
    | Expr.Ann ann ->
      match ann.Term, ann.Type with
      | Some t, Some typ -> Ann (exprToTerm t, exprToTerm typ)
      | None, _ -> failwith "annotation term is missing"
      | _, None -> failwith "annotaion type is missing"
    | Expr.Chk chk ->
      match chk.Term, chk.Type with
      | Some t, Some typ -> Chk (exprToTerm t, exprToTerm typ)
      | None, _ -> failwith "check term is missing"
      | _, None -> failwith "check type is missing"
    | Expr.Arr arr ->
      match arr.Domain, arr.Codomain with
      | Some a, Some b -> Arr (exprToTerm a, exprToTerm b)
      | None, _ -> failwith "arrow domain is missing"
      | _, None -> failwith "arrow codomain is missing"
    | Expr.Fre fre ->
      match fre.Term, fre.Body with
      | Some t, Some u -> Fre (exprToTerm t, exprToTerm u)
      | None, _ -> failwith "free term is missing"
      | _, None -> failwith "free body is missing" 
    | Expr.Dup dup ->
      match dup.Left, dup.Right, dup.Term, dup.Body with
      | l, r, Some t, Some u ->
        if nontrivial l then
          if nontrivial r then
            Dup (l, r, exprToTerm t, exprToTerm u)
          else failwith "duplication right name is empty"
        else failwith "duplication left name is empty"
      | _, _, None, _ -> failwith "duplication term is missing"
      | _, _, _, None -> failwith "duplication body is missing"
    | Expr.Dec dec ->
      match dec.Left, dec.Right, dec.Type, dec.Body with
      | l, r, Some typ, Some u ->
        if nontrivial l then
          if nontrivial r then
            Dec (l, r, exprToTerm typ, exprToTerm u)
          else failwith "decomposition right name is empty"
        else failwith "decomposition left name is empty"
      | _, _, None, _ -> failwith "decomposition type is missing"
      | _, _, _, None -> failwith "decomposition body is missing"


  let rec encode net
    (scope : Dictionary<string, Port>)
    (vars : ResizeArray<string * Port>)
    (up : Port)
    (trm : Term) =
    let inline go u t = encode net scope vars u t
    match trm with
    | Nil ->
      let nil = mkNode net NIL
      link net (Port.mk nil 1) (Port.mk nil 2)
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
      link net (Port.mk fre 1) (Port.mk fre 2)
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
    let net = Net.ctor ()
    let root = getRoot net
    inject net (Port.mk root 0) term
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

  let exprOfNode net vars node =
    match kind net node with
    | ROOT -> failwith "cannot convert root node to expression"
    | NIL -> Expr.Nil
    | LAM ->
      let x = nameOf vars (Port.mk node 1)
      Expr.Lam { Name = x; Body = None }
    | APP -> Expr.App { Fun = None; Arg = None }
    | SUP -> Expr.Sup { Left = None; Right = None }
    | ANN -> Expr.Ann { Term = None; Type = None }
    | CHK -> Expr.Chk { Term = None; Type = None }
    | ARR -> Expr.Arr { Domain = None; Codomain = None }
    | FRE -> Expr.Fre { Term = None; Body = None }
    | DUP ->
      let x = nameOf vars (Port.mk node 1)
      let y = nameOf vars (Port.mk node 2)
      Expr.Dup { Left = x; Right = y; Term = None; Body = None }
    | DEC ->
      let x = nameOf vars (Port.mk node 1)
      let y = nameOf vars (Port.mk node 2)
      Expr.Dec { Left = x; Right = y; Type = None; Body = None }
  
  let connect net
    (vars : Dictionary<Port, string>)
    (exprs : Dictionary<int, Expr>)
    (fres : ResizeArray<Fre>)
    (dups : ResizeArray<Dup>)
    (decs : ResizeArray<Dec>)
    node =
    let getExpr port =
      match vars.TryGetValue port with
      | true, name -> Some (Expr.Var { Name = name })
      | false, _ ->
        match exprs.TryGetValue (Port.address port) with
        | true, expr -> Some expr
        | false, _ -> None
    match kind net node with
    | ROOT -> failwith "cannot connect root node"
    | NIL -> ()
    | LAM ->
      match exprs.TryGetValue node with
      | true, Expr.Lam lam ->
        lam.Body <- getExpr (enter net (Port.mk node 2))
      | _ -> failwith "expected lambda node"
    | APP ->
      match exprs.TryGetValue node with
      | true, Expr.App app ->
        app.Fun <- getExpr (enter net (Port.mk node 0))
        app.Arg <- getExpr (enter net (Port.mk node 1))
      | _ -> failwith "expected application node"
    | SUP ->
      match exprs.TryGetValue node with
      | true, Expr.Sup sup ->
        sup.Left <- getExpr (enter net (Port.mk node 1))
        sup.Right <- getExpr (enter net (Port.mk node 2))
      | _ -> failwith "expected sup node"
    | ANN ->
      match exprs.TryGetValue node with
      | true, Expr.Ann ann ->
        ann.Term <- getExpr (enter net (Port.mk node 2))
        ann.Type <- getExpr (enter net (Port.mk node 1))
      | _ -> failwith "expected ann node"
    | CHK ->
      match exprs.TryGetValue node with
      | true, Expr.Chk chk ->
        chk.Term <- getExpr (enter net (Port.mk node 0))
        chk.Type <- getExpr (enter net (Port.mk node 1))
      | _ -> failwith "expected chk node"
    | ARR ->
      match exprs.TryGetValue node with
      | true, Expr.Arr arr ->
        arr.Domain <- getExpr (enter net (Port.mk node 1))
        arr.Codomain <- getExpr (enter net (Port.mk node 2))
      | _ -> failwith "expected arr node"
    | FRE ->
      match exprs.TryGetValue node with
      | true, Expr.Fre fre ->
        fre.Term <- getExpr (enter net (Port.mk node 0))
        fres.Add fre
      | _ -> failwith "expected fre node"
    | DUP ->
      match exprs.TryGetValue node with
      | true, Expr.Dup dup ->
        dup.Term <- getExpr (enter net (Port.mk node 0))
        dups.Add dup
      | _ -> failwith "expected dup node"
    | DEC ->
      match exprs.TryGetValue node with
      | true, Expr.Dec dec ->
        dec.Type <- getExpr (enter net (Port.mk node 1))
        dec.Body <- getExpr (enter net (Port.mk node 0))
        decs.Add dec
      | _ -> failwith "expected dec node"
  
  let readback net =
    let nodes = getNodes net
    let fres = ResizeArray<Fre> ()
    let dups = ResizeArray<Dup> ()
    let decs = ResizeArray<Dec> ()
    let vars = Dictionary<Port, string> ()
    let exprs = Dictionary<int, Expr> ()
    for node in nodes do
      let expr = exprOfNode net vars node
      exprs.Add (node, expr)
    for node in nodes do
      connect net vars exprs fres dups decs node
    let mutable expr = exprs[getFirst net]
    for dup in dups do
      dup.Body <- Some expr
      expr <- Expr.Dup dup
    for dec in decs do
      dec.Body <- Some expr
      expr <- Expr.Dec dec
    for fre in fres do
      fre.Body <- Some expr
      expr <- Expr.Fre fre
    exprToTerm expr
  
  let roundtrip (term : Term) =
    readback (build term)
  