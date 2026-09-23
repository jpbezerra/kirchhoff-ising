# Circuit -- the laws (Module A: the resistive circuit graph).

import Base
import ./circuit.bend as Circuit
import ../int.bend as Int

# Not namespaced "Circuit.is_circulation"/"Circuit.all_circulations" on
# purpose: a def prefixed with the same name as an import alias ("Circuit",
# from `import ./circuit.bend as Circuit` above) breaks once this file is
# imported by another one -- confirmed against the real compiler (a small
# isolated repro), the self-reference inside all_circulations's recursive
# case fails to resolve with "expected: a defined name, observed:
# Circuit.all_circulations" as soon as PROOF.bend imports this file. Bare
# names avoid the collision entirely.

# `loop` is a genuine closed walk in `c`, at node `n`: among the loop's own
# edges, exactly as many enter `n` as leave it (mirrors Lean's
# Circuit.IsCirculation -- see Laws.lean for the full rationale: a loop
# naming node pairs with no matching edge isn't required to preserve
# balance, since you can't run a mesh current around a path that doesn't
# exist).
def is_circulation(c: Circuit.Circuit, loop: Circuit.Loop, +n: Nat) -> Type:
  {Circuit.node_balance_delta(c, loop, n) == Int.SInt.zero() : Int.SInt}

# `loop` is a circulation at every node in `ns` -- Bend has no `for all x in
# xs` quantifier sugar (unlike Lean's `∀ n ∈ ns, ...`), so this is spelled
# out as a recursive conjunction of is_circulation over the list.
def all_circulations(+c: Circuit.Circuit, +loop: Circuit.Loop, ns: +List<Nat>) -> Type:
  match ns:
    case Nil{}:
      Unit
    case +n <> t:
      is_circulation(c, loop, n) & all_circulations(c, loop, t)

# LAW: applying a +delta mesh current around `loop` doesn't change node n's
# balance, as long as loop is a genuine circulation at n.
law preserves_node_balance:
  for +c: Circuit.Circuit
  for +loop: Circuit.Loop
  for +delta: Int.SInt
  for +n: Nat
  for circ: is_circulation(c, loop, n)
  {Circuit.node_balance(n, Circuit.add_loop_current(c, loop, delta)) == Circuit.node_balance(n, c) : Int.SInt}

# LAW: summing node_balance over any fixed list of nodes is likewise
# unaffected, as long as the loop is a circulation at each of them -- an
# easy corollary of preserves_node_balance. Read as "the local invariant
# summed pointwise over a chosen node list", not a new global-sum law --
# a literal "sum of all currents" reading isn't true in general (adding
# delta to K loop edges changes their raw sum by delta*K).
law loop_current_conserves_total:
  for +c: Circuit.Circuit
  for +loop: Circuit.Loop
  for +delta: Int.SInt
  for +ns: +List<Nat>
  for circ: all_circulations(c, loop, ns)
  {Circuit.node_balance_map(ns, Circuit.add_loop_current(c, loop, delta)) == Circuit.node_balance_map(ns, c) : +List<Int.SInt>}
