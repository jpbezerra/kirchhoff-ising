import Base
import ../int.bend as Int

# A resistor between two nodes, carrying a signed current from `from_` to `to_`.
type Edge is Data:
  Edge{from_: Nat, to_: Nat, current: Int.SInt}

# The circuit as a graph: just its edges.
type Circuit is Data:
  Circuit{edges: +List<Edge>}

# A closed mesh: a cyclic sequence of nodes. [a,b,c] means the cycle a->b->c->a.
type Loop is Data:
  Loop{nodes: +List<Nat>}

def edge_contribution.go(is_to: Bool, is_from: Bool, cur: Int.SInt) -> Int.SInt:
  match is_to is_from:
    case True{} True{}:
      Int.SInt.zero()
    case True{} False{}:
      cur
    case False{} True{}:
      Int.SInt.neg(cur)
    case False{} False{}:
      Int.SInt.zero()

def edge_contribution(+n: Nat, e: Edge) -> Int.SInt:
  match e:
    case Edge{f, t, cur}:
      edge_contribution.go(Nat.is_eq(t, n), Nat.is_eq(f, n), cur)

# Direct head+rest recursion (not an accumulator fold) -- mirrors
# node_balance_delta.go below and ising/lattice.bend's updown.row/rows.
# Keeps the "how does node_balance change under an edge update" induction a
# single SInt.add per step, reassociated via sint_add_assoc, instead of
# needing to thread a growing accumulator through every step.
def node_balance.go(edges: +List<Edge>, +n: Nat) -> Int.SInt:
  match edges:
    case Nil{}:
      Int.SInt.zero()
    case e <> t:
      Int.SInt.add(edge_contribution(n, e), node_balance.go(t, n))

# Net current entering `n` minus leaving it, summed over every edge of the circuit.
def node_balance(+n: Nat, c: Circuit) -> Int.SInt:
  match c:
    case Circuit{edges}:
      node_balance.go(edges, n)

# Consecutive directed pairs of a cyclic node sequence, as two parallel lists:
# [a,b,c] -> froms=[a,b,c], tos=[b,c,a] (so pair i is (froms[i], tos[i])).
def loop_pairs.rot(nodes: +List<Nat>, first: Nat) -> +List<Nat>:
  match nodes:
    case Nil{}:
      [first]
    case n <> t:
      n <> loop_pairs.rot(t, first)

def loop_pairs(nodes: +List<Nat>) -> +List<Nat> & +List<Nat>:
  match nodes:
    case Nil{}:
      (Nil{}, Nil{})
    case +n <> +t:
      (n <> t, loop_pairs.rot(t, n))

def is_loop_pair(froms: +List<Nat>, tos: +List<Nat>, +from_: Nat, +to_: Nat) -> Bool:
  match froms tos:
    case Nil{} _:
      False{}
    case _ Nil{}:
      False{}
    case a <> as_ b <> bs:
      Bool.pick(Bool, Bool.and(Nat.is_eq(a, from_), Nat.is_eq(b, to_)),
        True{}, is_loop_pair(as_, bs, from_, to_))

def is_loop_edge.check(pair: +List<Nat> & +List<Nat>, f: Nat, t: Nat) -> Bool:
  (froms, tos) = pair
  is_loop_pair(froms, tos, f, t)

def is_loop_edge(loop: Loop, e: Edge) -> Bool:
  match loop e:
    case Loop{nodes} Edge{f, t, cur}:
      is_loop_edge.check(loop_pairs(nodes), f, t)

def add_loop_current.update(matched: Bool, e: Edge, delta: Int.SInt) -> Edge:
  match matched e:
    case True{} Edge{f, tt, cur}:
      Edge{f, tt, Int.SInt.add(cur, delta)}
    case False{} _:
      e

def add_loop_current.go(edges: +List<Edge>, +loop: Loop, +delta: Int.SInt) -> +List<Edge>:
  match edges:
    case Nil{}:
      Nil{}
    case +e <> t:
      add_loop_current.update(is_loop_edge(loop, e), e, delta) <> add_loop_current.go(t, loop, delta)

# Adds `delta` to the current of every edge that belongs to the loop.
def add_loop_current(c: Circuit, loop: Loop, delta: Int.SInt) -> Circuit:
  match c:
    case Circuit{edges}:
      Circuit{add_loop_current.go(edges, loop, delta)}

# How much a mesh current of `delta` around `loop` would shift node n's
# balance -- +delta per loop edge entering n, -delta per loop edge leaving it.
# node_balance_delta below is the delta=of_nat(1n) instance, used by LAWS.bend
# to state the "loop is a genuine circulation at n" hypothesis (mirrors
# Lean's nodeBalanceDelta in lean/Laws.lean). Non-loop edges are
# SKIPPED entirely (not summed as an explicit +zero() term) -- this matters
# for the proof in circuit_assoc.bend: padding with a literal zero() would
# force proving {add(zero(),x)==x} for an opaque x, which is false at the
# single non-canonical value SInt{False,0n} (see sint_laws.bend's comments).
# Skipping the term outright needs no such lemma.
def node_balance_delta_scaled.edge.go(nodes: +List<Nat>, +n: Nat, +f: Nat, +t: Nat, +delta: Int.SInt) -> Int.SInt:
  +is_loop = is_loop_edge.check(loop_pairs(nodes), f, t)
  edge_contribution.go(Bool.and(is_loop, Nat.is_eq(t, n)), Bool.and(is_loop, Nat.is_eq(f, n)), delta)

def node_balance_delta_scaled.edge(loop: Loop, +n: Nat, e: Edge, +delta: Int.SInt) -> Int.SInt:
  match loop e:
    case Loop{nodes} Edge{f, t, cur}:
      node_balance_delta_scaled.edge.go(nodes, n, f, t, delta)

def node_balance_delta_scaled.go(edges: +List<Edge>, +loop: Loop, +n: Nat, +delta: Int.SInt) -> Int.SInt:
  match edges:
    case Nil{}:
      Int.SInt.zero()
    case +e <> +t:
      Bool.pick(Int.SInt, is_loop_edge(loop, e),
        Int.SInt.add(node_balance_delta_scaled.edge(loop, n, e, delta), node_balance_delta_scaled.go(t, loop, n, delta)),
        node_balance_delta_scaled.go(t, loop, n, delta))

def node_balance_delta_scaled(c: Circuit, loop: Loop, +n: Nat, +delta: Int.SInt) -> Int.SInt:
  match c:
    case Circuit{edges}:
      node_balance_delta_scaled.go(edges, loop, n, delta)

def node_balance_delta.go(edges: +List<Edge>, +loop: Loop, +n: Nat) -> Int.SInt:
  node_balance_delta_scaled.go(edges, loop, n, Int.SInt.of_nat(1n))

def node_balance_delta(c: Circuit, loop: Loop, +n: Nat) -> Int.SInt:
  match c:
    case Circuit{edges}:
      node_balance_delta.go(edges, loop, n)

# node_balance for every node in a list, for the loop_current_conserves_total law.
def node_balance_map(ns: +List<Nat>, +c: Circuit) -> +List<Int.SInt>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> t:
      node_balance(n, c) <> node_balance_map(t, c)
