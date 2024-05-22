

namespace FSharp

namespace ITT
    
    module Type =
        
        type Type =
            | Unit
            | Tuple of Type * Type
            | Arrow of Type * Type
            | Box of Type
        
        type Checkable =
            | CUnit
            | CTuple of Checkable * Checkable
            | CArrow of Type * Checkable
        
        [<RequireQualifiedAccess>]
        module Type =
            
            val reduce: typ: Type -> Type
            
            val show: typ: Type -> string
            
            val isSubtype: typ1: Type -> typ2: Type -> bool
        
        [<RequireQualifiedAccess>]
        module Checkable =
            
            val toType: a: Checkable -> Type
            
            val show: (Checkable -> string)
            
            val isSubtype: typ: Type -> a: Checkable -> bool

namespace ITT
    
    module Stacks =
        
        [<Struct>]
        type VStack<'a when 'a: unmanaged> =
            private {
                      Capacity: int
                      BufferPtr: nativeptr<'a>
                      mutable Count: int
                    }
        
        module VStack =
            
            val ctor:
              capacity: int * bufferPtr: nativeptr<'a> -> VStack<'a>
                when 'a: unmanaged
            
            val clear: stack: byref<VStack<'a>> -> unit when 'a: unmanaged
            
            val push:
              x: 'a -> stack: byref<VStack<'a>> -> unit when 'a: unmanaged
            
            val pop: stack: byref<VStack<'a>> -> 'a when 'a: unmanaged
            
            val tryPop:
              stack: byref<VStack<'a>> -> x: byref<'a> -> bool
                when 'a: unmanaged
        
        type FixedStack<'a> =
            
            new: capacity: int -> FixedStack<'a>
            
            member Clear: unit -> unit
            
            member Pop: unit -> 'a
            
            member Push: x: 'a -> unit
            
            member TryPop: x: byref<'a> -> bool
            
            member Count: int

namespace ITT
    
    module Deque =
        
        type Deque<'a> =
            
            new: capacity: int -> Deque<'a>
            
            member PeekBack: unit -> 'a
            
            member PeekFront: unit -> 'a
            
            member PopBack: unit -> 'a voption
            
            member PopFront: unit -> 'a voption
            
            member PushBack: x: 'a -> unit
            
            member PushFront: x: 'a -> unit
            
            member Capacity: int
            
            member Count: int

namespace ITT
    
    module Nets =
        
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
            
            static member arity: kind: Kind -> int
            
            static member fromInt: i: int -> Kind
            
            static member toInt: kind: Kind -> int
        
        type Reuse =
            
            new: unit -> Reuse
            
            member Contains: node: int -> bool
            
            member Push: node: int -> unit
            
            member TryPop: unit -> bool * int
        
        type Net =
            
            new: unit -> Net
            
            member Checkables: ResizeArray<Type.Checkable>
            
            member Nodes: ResizeArray<int>
            
            member Reuse: Reuse
            
            member Rewrites: int with get, set
            
            member Types: ResizeArray<Type.Type>
        
        [<Measure>]
        type uomPort
        
        type Port = int<uomPort>
        
        [<RequireQualifiedAccess>]
        module Port =
            
            val inline mk: address: int -> slot: int -> Port
            
            val inline address: port: Port -> int
            
            val inline slot: port: Port -> int
        
        val inline getRoot: net: Net -> int
        
        val inline enter: net: Net -> port: Port -> Port
        
        val inline getFirst: net: Net -> int
        
        val inline kind: net: Net -> node: int -> Kind
        
        val inline getType: net: Net -> node: int -> Type.Type
        
        val inline setType: net: Net -> node: int -> typ: Type.Type -> unit
        
        val inline getCheckable: net: Net -> node: int -> Type.Checkable
        
        val inline setCheckable:
          net: Net -> node: int -> a: Type.Checkable -> unit
        
        val inline set: net: Net -> portA: Port -> portB: Port -> unit
        
        val inline link: net: Net -> portA: Port -> portB: Port -> unit
        
        val mkNode: net: Net -> kind: Kind -> int
        
        val mkChkNode: net: Net -> a: Type.Checkable -> int
        
        val mkAnnNode: net: Net -> typ: Type.Type -> int
        
        val inline freeNode: net: Net -> nd: int -> unit
        
        val annihilate: net: Net -> ndA: int -> ndB: int -> unit
        
        val erase: net: Net -> nd: int -> unit
        
        val commute: net: Net -> ndA: int -> ndB: int -> unit
        
        val interact: net: Net -> ndA: int -> ndB: int -> unit

namespace ITT
    
    module Terms =
        
        [<AbstractClass; AllowNullLiteral>]
        type Term =
            
            new: unit -> Term
        
        type Nil =
            inherit Term
            
            new: unit -> Nil
        
        type Var =
            inherit Term
            
            new: name: string -> Var
            
            member Name: string with get, set
        
        type Lam =
            inherit Term
            
            new: name: string * body: Term -> Lam
            
            member Body: Term with get, set
            
            member Name: string with get, set
        
        type App =
            inherit Term
            
            new: func: Term * argm: Term -> App
            
            member Argm: Term with get, set
            
            member Func: Term with get, set
        
        type Sup =
            inherit Term
            
            new: left: Term * right: Term -> Sup
            
            member Left: Term with get, set
            
            member Right: Term with get, set
        
        type Ann =
            inherit Term
            
            new: trm: Term * typ: Type.Type -> Ann
            
            member Term: Term with get, set
            
            member Type: Type.Type with get, set
        
        type Chk =
            inherit Term
            
            new: trm: Term * typ: Type.Checkable -> Chk
            
            member Term: Term with get, set
            
            member Type: Type.Checkable with get, set
        
        type Fre =
            inherit Term
            
            new: trm: Term * bod: Term -> Fre
            
            member Body: Term with get, set
            
            member Term: Term with get, set
        
        type Dup =
            inherit Term
            
            new: left: string * right: string * trm: Term * bod: Term -> Dup
            
            member Body: Term with get, set
            
            member Left: string with get, set
            
            member Right: string with get, set
            
            member Term: Term with get, set
        
        val show: trm: Term -> string
        
        val encode:
          net: Nets.Net ->
            scope: System.Collections.Generic.Dictionary<string,Nets.Port> ->
            vars: ResizeArray<string * Nets.Port> ->
            up: Nets.Port -> trm: Term -> Nets.Port
        
        val inject: net: Nets.Net -> host: Nets.Port -> term: Term -> unit
        
        val build: term: Term -> Nets.Net
        
        val indexToName: index: int -> string
        
        val nameOf:
          vars: System.Collections.Generic.Dictionary<Nets.Port,string> ->
            varPort: Nets.Port -> string
        
        val getNodes: net: Nets.Net -> ResizeArray<int>
        
        val termOfNode:
          net: Nets.Net ->
            vars: System.Collections.Generic.Dictionary<Nets.Port,string> ->
            node: int -> Term
        
        val connect:
          net: Nets.Net ->
            vars: System.Collections.Generic.Dictionary<Nets.Port,string> ->
            trms: System.Collections.Generic.Dictionary<int,Term> ->
            fres: ResizeArray<Fre> ->
            dups: ResizeArray<Dup> -> node: int -> unit
        
        val readback: net: Nets.Net -> Term
        
        val roundtrip: term: Term -> Term

namespace ITT
    
    module InteractionTypeTheory =
        
        type Path =
            System.Collections.Generic.Dictionary<uint32,Deque.Deque<byte>>
        
        type Log = System.Collections.Generic.Stack<string>
        
        val TAG: uint32
        
        val NIL: uint32
        
        val ORB: uint32
        
        val ERA: uint32
        
        val CON: uint32
        
        val ANN: uint32
        
        val FIX: uint32
        
        val DUP: uint32
        
        val inline port: address: uint32 * slot: uint32 -> uint32
        
        val inline address: port: uint32 -> uint32
        
        val inline slot: port: uint32 -> uint32
        
        val ROOT: uint32
        
        type Net =
            
            new: unit -> Net
            
            private new: nodes: ResizeArray<uint32> *
                         reuse: System.Collections.Generic.Stack<uint32> *
                         rules: int -> Net
            
            member Annihilate: x: uint32 -> y: uint32 -> unit
            
            member Commute: x: uint32 -> y: uint32 -> unit
            
            member
              Compare: step: int ->
                         flip: bool ->
                         a0: uint32 ->
                         aR: uint32 ->
                         aPath: Path ->
                         aLog: Log ->
                         b0: uint32 ->
                         bR: uint32 -> bPath: Path -> bLog: Log -> bool
            
            member Enter: port: uint32 -> uint32
            
            member Equal: a: uint32 -> b: uint32 -> bool
            
            member Erase: address: uint32 -> unit
            
            member Get: p: uint32 -> slot: uint32 -> uint32
            
            member Kind: address: uint32 -> uint32
            
            member Link: ptrA: uint32 -> ptrB: uint32 -> unit
            
            member NewNode: kind: uint32 -> uint32
            
            member Normalize: unit -> unit
            
            member Reduce: root: uint32 -> unit
            
            member Rewrite: x: uint32 -> y: uint32 -> unit
            
            member Rules: int

namespace ITT
    
    module Program =
        
        type Nil =
            
            new: unit -> Nil
            
            member Slot: i: int -> obj with get
            
            member Slot: i: int -> obj with set
        
        module DivideAndConquer =
            
            type Either<'a,'b> =
                | Left of 'a
                | Right of 'b
            
            type State<'s,'a> = 's -> 'a * 's
            
            val inline retur: a: 'a -> s: 's -> 'a * 's
            
            val inline bind:
              m: State<'s,'a> -> f: ('a -> 's -> 'b * 's) -> s: 's -> 'b * 's
            
            val mapM:
              f: ('a -> 's -> 'b * 's) -> xs: 'a list -> State<'s,'b list>
            
            val memoize:
              t: (('a -> Map<'a,'b> -> 'b * Map<'a,'b>) ->
                    'a -> Map<'a,'b> -> 'b * Map<'a,'b>) -> x: 'a -> 'b
                when 'a: comparison
            
            type Recur<'a,'b> = 'a -> Either<'b,('a list * ('b list -> 'b))>
            
            val distr:
              go: Recur<'a,'b> ->
                u: ('a -> Map<'a,'b> -> 'b * Map<'a,'b>) ->
                x: 'a -> State<Map<'a,'b>,'b> when 'a: comparison
            
            val conquer: go: Recur<'a,'b> -> ('a -> 'b) when 'a: comparison
            
            val dividedFib: x: int -> Either<int,(int list * (int list -> int))>
            
            val fib: (int -> int)
        
        val testInt: unit -> int
        
        val MAGIC_MULTIPLIER: int64
        
        val DOT_DETECTOR: int64
        
        val ASCII_TO_DIGIT_MASK: int64
        
        val readInt: span: System.ReadOnlySpan<byte> -> int * int
        
        type Nat =
            
            new: plus: (Nat -> Nat) * mul: (Nat -> Nat) -> Nat
            
            static member succ: n: Nat -> Nat
            
            member private Mul: (Nat -> Nat)
            
            member private Plus: (Nat -> Nat)
            
            static member Zero: Nat
        
        module private Unsafe =
            
            val inline cast: a: 'a -> 'b
        
        val inline clt: a: int -> b: int -> int
        
        val inline private minimum: a: int -> b: int -> int
        
        val inline private boolToInt: b: bool -> int
        
        val private boolToIntSafe: b: bool -> int
        
        val testBoolToInt:
          clock: System.Diagnostics.Stopwatch -> accumulator: byref<int> -> unit
        
        val testBoolToIntSafe:
          clock: System.Diagnostics.Stopwatch -> accumulator: byref<int> -> unit
        
        val refTest:
          clock: System.Diagnostics.Stopwatch -> array: int array -> unit
        
        val fixedTest:
          clock: System.Diagnostics.Stopwatch -> array: int array -> unit
        
        val foreachTest:
          clock: System.Diagnostics.Stopwatch -> array: int array -> unit
        
        [<Struct>]
        type ABC =
            | A
            | B
            | C
        
        [<Struct>]
        type R =
            {
              X: bigint
              Y: bigint
            }
            
            static member ( * ) : a: R * b: R -> R
            
            static member (+) : a: R * b: R -> R
            
            static member (-) : a: R * b: R -> R
            
            static member (/) : a: 'a * b: 'b -> 'c
            
            static member One: R
            
            static member Phi: R
        
        val fib: n: int -> bigint
        
        val fibStack: n: int -> System.Numerics.BigInteger
        
        val fibHeap: n: int -> System.Numerics.BigInteger
        
        val fibRec: n: int -> System.Numerics.BigInteger
        
        val church2: Terms.Dup
        
        val churc2Alt: Terms.Lam
        
        val idlam: Terms.Lam
        
        val killer: Terms.Fre
        
        val vanishing: Terms.Fre
        
        val checker: Terms.Chk
        
        val isEven: x: int -> int
        
        val main: string array -> int

