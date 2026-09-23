/-- A node of the circuit, identified by an id. -/
structure Node where
  id : Nat
deriving Repr, DecidableEq

/-- A resistor between two nodes, carrying a signed current from `from_` to `to_`. -/
structure Edge where
  from_ : Nat
  to_ : Nat
  current : Int
deriving Repr, DecidableEq

/-- The circuit as a graph: just its edges. -/
structure Circuit where
  edges : List Edge
deriving Repr

/-- A closed mesh: a cyclic sequence of nodes. `[a, b, c]` means the cycle a→b→c→a. -/
structure Loop where
  nodes : List Nat
deriving Repr

def edgeContribution (n : Nat) (e : Edge) : Int :=
  (if e.to_ = n then e.current else 0) - (if e.from_ = n then e.current else 0)

/-- Net current entering `n` minus leaving it, summed over every edge of the circuit. -/
def Circuit.nodeBalance (c : Circuit) (n : Nat) : Int :=
  (c.edges.map (edgeContribution n)).sum

/-- Consecutive directed pairs of a cyclic node sequence: `[a,b,c] ↦ [(a,b),(b,c),(c,a)]`. -/
def loopPairs : List Nat → List (Nat × Nat)
  | [] => []
  | n :: rest => List.zip (n :: rest) (rest ++ [n])

def isLoopEdge (loop : Loop) (e : Edge) : Bool :=
  (loopPairs loop.nodes).contains (e.from_, e.to_)

/-- Adds `delta` to the current of every edge that belongs to the loop. -/
def Circuit.addLoopCurrent (c : Circuit) (loop : Loop) (delta : Int) : Circuit :=
  { c with edges := c.edges.map (fun e =>
      if isLoopEdge loop e then { e with current := e.current + delta } else e) }
