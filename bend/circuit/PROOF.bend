# Circuit -- the proofs.
#
# preserves_node_balance's core difficulty was general associativity of the
# hand-rolled sign+magnitude SInt type (add_loop_current can touch arbitrarily
# many edges, each by an arbitrary delta:SInt, so there's no single final
# from_diff conversion to defer to the way Ising's flip_changes_magnetization
# has -- the induction genuinely needs to reassociate a growing sum at every
# step). sint_add_assoc (bend/tests/sint_laws.bend) closes that.
#
# The remaining gap was bridging the LAW's unit-delta circulation hypothesis
# (node_balance_delta, delta=of_nat(1n) hardcoded) to an arbitrary mesh
# current delta. That needs counting: how many loop edges touch n as a "to"
# edge vs a "from" edge (two Nat counts), because the raw SInt sum by itself
# doesn't structurally decompose under induction -- partial sums can be
# nonzero even when the total is zero. bend/tests/circuit_assoc.bend works
# this out in full:
#   - node_balance_map_update: updating every loop edge's current by delta
#     shifts node n's balance by exactly node_balance_delta_scaled (the
#     delta-parameterized generalization of node_balance_delta).
#   - char_correspondence: node_balance_delta_scaled equals the touch counts
#     (ct, cf) scaled by +-delta (repeat_add), proven by induction alongside
#     node_balance_delta_scaled's own recursion.
#   - char_unit + from_diff_zero_implies_eq: at delta=of_nat(1n), the
#     circulation hypothesis forces ct==cf (via a discriminator/absurd
#     argument on Nat.cmp's impossible branches -- confirmed Bend supports
#     this pattern).
#   - repeat_add_cancel: once ct==cf, the scaled sum at ANY delta cancels to
#     zero (add(repeat_add(ct,delta), repeat_add(ct,neg(delta)))==zero()).
# One subtlety threads through all of it: SInt's zero has a non-canonical
# twin (SInt{False,0n}, never produced by from_diff but reachable via a
# user-chosen delta or a raw Edge.current), so {add(x,zero())==x} is FALSE in
# general. node_balance_delta_scaled and repeat_add are both defined to never
# need that identity for an opaque value (skip-based recursion / uniform
# successor case), and the few places a "prepend zero" step was still
# unavoidable (add_zero_r_nb, add_zero_l_repeat/_sum) prove it only for
# concretely-known-safe values, never for an arbitrary opaque SInt.

import Base
import ../circuit/circuit.bend as Circuit
import ../int.bend as Int
import ./LAWS.bend as Laws
import ../tests/circuit_assoc.bend as CA

def Laws.preserves_node_balance(c, loop, delta, n, circ):
  match c loop:
    case Circuit.Circuit{edges} Circuit.Loop{nodes}:
      Equal.trans(Int.SInt,
        Circuit.node_balance.go(Circuit.add_loop_current.go(edges, Circuit.Loop{nodes}, delta), n),
        Int.SInt.add(Circuit.node_balance.go(edges, n), Circuit.node_balance_delta_scaled.go(edges, Circuit.Loop{nodes}, n, delta)),
        Circuit.node_balance.go(edges, n),
        CA.node_balance_map_update(edges, nodes, delta, n),
        Equal.trans(Int.SInt,
          Int.SInt.add(Circuit.node_balance.go(edges, n), Circuit.node_balance_delta_scaled.go(edges, Circuit.Loop{nodes}, n, delta)),
          Int.SInt.add(Circuit.node_balance.go(edges, n), Int.SInt.zero()),
          Circuit.node_balance.go(edges, n),
          Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Circuit.node_balance.go(edges, n), x), Circuit.node_balance_delta_scaled.go(edges, Circuit.Loop{nodes}, n, delta), Int.SInt.zero(),
            CA.circulation_implies_scaled_zero(edges, nodes, n, delta, circ)),
          CA.add_zero_r_nb(edges, n)))

def Laws.loop_current_conserves_total(c, loop, delta, ns, circ):
  match ns:
    case Nil{}:
      {==}
    case n <> t:
      (circ_n, circ_t) = circ
      Equal.trans(+List<Int.SInt>,
        Circuit.node_balance(n, Circuit.add_loop_current(c, loop, delta)) <> Circuit.node_balance_map(t, Circuit.add_loop_current(c, loop, delta)),
        Circuit.node_balance(n, c) <> Circuit.node_balance_map(t, Circuit.add_loop_current(c, loop, delta)),
        Circuit.node_balance(n, c) <> Circuit.node_balance_map(t, c),
        Equal.cong(Int.SInt, +List<Int.SInt>, x => x <> Circuit.node_balance_map(t, Circuit.add_loop_current(c, loop, delta)), Circuit.node_balance(n, Circuit.add_loop_current(c, loop, delta)), Circuit.node_balance(n, c),
          Laws.preserves_node_balance(c, loop, delta, n, circ_n)),
        Equal.cong(+List<Int.SInt>, +List<Int.SInt>, x => Circuit.node_balance(n, c) <> x, Circuit.node_balance_map(t, Circuit.add_loop_current(c, loop, delta)), Circuit.node_balance_map(t, c),
          Laws.loop_current_conserves_total(c, loop, delta, t, circ_t)))
