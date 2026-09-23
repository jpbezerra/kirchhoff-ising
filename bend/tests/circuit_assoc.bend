import Base
import ../circuit/circuit.bend as Circuit
import ../int.bend as Int
import ./sint_laws.bend as SL

# neg(from_diff(x,y)) == from_diff(y,x) -- negating a "ups - downs" value
# swaps ups and downs. Base cases are all free computation (0-vs-anything
# is a single manifest-pattern match); the recursive case peels one layer
# off both sides via SL.shift_invariant, same pattern as diff_inc/diff_dec.
def neg_from_diff_swap(+x: Nat, +y: Nat) -> {Int.SInt.neg(Int.SInt.from_diff(x, y)) == Int.SInt.from_diff(y, x) : Int.SInt}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+yp:
      {==}
    case 1n+xp 0n:
      {==}
    case 1n+xp 1n+yp:
      Equal.trans(Int.SInt, Int.SInt.neg(Int.SInt.from_diff(1n+xp, 1n+yp)), Int.SInt.neg(Int.SInt.from_diff(xp, yp)), Int.SInt.from_diff(1n+yp, 1n+xp),
        Equal.cong(Int.SInt, Int.SInt, Int.SInt.neg, Int.SInt.from_diff(1n+xp, 1n+yp), Int.SInt.from_diff(xp, yp), SL.shift_invariant(xp, yp)),
        Equal.trans(Int.SInt, Int.SInt.neg(Int.SInt.from_diff(xp, yp)), Int.SInt.from_diff(yp, xp), Int.SInt.from_diff(1n+yp, 1n+xp),
          neg_from_diff_swap(xp, yp),
          Equal.sym(Int.SInt, Int.SInt.from_diff(1n+yp, 1n+xp), Int.SInt.from_diff(yp, xp), SL.shift_invariant(yp, xp))))

# neg is additive: neg(add(a,b)) == add(neg(a),neg(b)). Needed because
# add_loop_current adds delta to an edge's current, and a "leaving" edge's
# contribution is neg(current) -- so relating the updated contribution to
# the old one plus delta's own contribution needs neg to distribute over add.
def neg_add_hom(+a: Int.SInt, +b: Int.SInt) -> {Int.SInt.neg(Int.SInt.add(a, b)) == Int.SInt.add(Int.SInt.neg(a), Int.SInt.neg(b)) : Int.SInt}:
  match a b:
    case Int.SInt{True{}, 0n} Int.SInt{True{}, 0n}:
      {==}
    case Int.SInt{True{}, 0n} Int.SInt{True{}, 1n+bmp}:
      {==}
    case Int.SInt{True{}, 1n+amp} Int.SInt{True{}, 0n}:
      %SL.nat_add_zero_r(amp) : {Int.SInt{False{}, 1n+Nat.add(amp, 0n)} == Int.SInt{False{}, 1n+_} : Int.SInt}
      {==}
    case Int.SInt{True{}, 1n+amp} Int.SInt{True{}, 1n+bmp}:
      {==}
    case Int.SInt{False{}, am} Int.SInt{False{}, bm}:
      {==}
    case Int.SInt{True{}, 0n} Int.SInt{False{}, 0n}:
      neg_from_diff_swap(0n, 0n)
    case Int.SInt{True{}, 0n} Int.SInt{False{}, 1n+bmp}:
      neg_from_diff_swap(0n, 1n+bmp)
    case Int.SInt{True{}, 1n+amp} Int.SInt{False{}, 0n}:
      neg_from_diff_swap(1n+amp, 0n)
    case Int.SInt{True{}, 1n+amp} Int.SInt{False{}, 1n+bmp}:
      neg_from_diff_swap(1n+amp, 1n+bmp)
    case Int.SInt{False{}, 0n} Int.SInt{True{}, 0n}:
      {==}
    case Int.SInt{False{}, 0n} Int.SInt{True{}, 1n+bmp}:
      {==}
    case Int.SInt{False{}, 1n+amp} Int.SInt{True{}, 0n}:
      %SL.nat_add_zero_r(amp) : {Int.SInt{True{}, 1n+_} == Int.SInt{True{}, 1n+Nat.add(amp, 0n)} : Int.SInt}
      {==}
    case Int.SInt{False{}, 1n+amp} Int.SInt{True{}, 1n+bmp}:
      Equal.trans(Int.SInt, Int.SInt.neg(Int.SInt.from_diff(1n+bmp, 1n+amp)), Int.SInt.from_diff(1n+amp, 1n+bmp), Int.SInt.add(Int.SInt{True{}, 1n+amp}, Int.SInt.neg(Int.SInt{True{}, 1n+bmp})),
        neg_from_diff_swap(1n+bmp, 1n+amp),
        {==})

def main() -> Nat:
  0n

# edge_contribution.go is additive in its current/delta argument, regardless
# of whether the edge is a loop edge -- this is exactly what
# add_loop_current's update needs: the new contribution equals the old one
# plus the contribution delta would make on its own.
def edge_contribution_go_additive(+is_to: Bool, +is_from: Bool, +cur: Int.SInt, +delta: Int.SInt)
  -> {Circuit.edge_contribution.go(is_to, is_from, Int.SInt.add(cur, delta)) == Int.SInt.add(Circuit.edge_contribution.go(is_to, is_from, cur), Circuit.edge_contribution.go(is_to, is_from, delta)) : Int.SInt}:
  match is_to is_from:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      neg_add_hom(cur, delta)
    case False{} False{}:
      {==}

# The "middle four exchange" identity: (a+b)+(c+d) == (a+c)+(b+d). General,
# needs only associativity+commutativity (both already proven in
# sint_laws.bend). Used to merge a per-edge update with the recursive tail's
# induction hypothesis in one step.
def four_term_swap(+a: Int.SInt, +b: Int.SInt, +c: Int.SInt, +d: Int.SInt)
  -> {Int.SInt.add(Int.SInt.add(a, b), Int.SInt.add(c, d)) == Int.SInt.add(Int.SInt.add(a, c), Int.SInt.add(b, d)) : Int.SInt}:
  # T0=(a+b)+(c+d) ==T1== a+(b+(c+d)) ==T2== a+((b+c)+d) ==T3== a+((c+b)+d)
  # ==T4== a+(c+(b+d)) ==T5== (a+c)+(b+d)
  Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.add(a, b), Int.SInt.add(c, d)), Int.SInt.add(a, Int.SInt.add(b, Int.SInt.add(c, d))), Int.SInt.add(Int.SInt.add(a, c), Int.SInt.add(b, d)),
    Equal.sym(Int.SInt, Int.SInt.add(a, Int.SInt.add(b, Int.SInt.add(c, d))), Int.SInt.add(Int.SInt.add(a, b), Int.SInt.add(c, d)), SL.sint_add_assoc(a, b, Int.SInt.add(c, d))),
    Equal.trans(Int.SInt, Int.SInt.add(a, Int.SInt.add(b, Int.SInt.add(c, d))), Int.SInt.add(a, Int.SInt.add(Int.SInt.add(b, c), d)), Int.SInt.add(Int.SInt.add(a, c), Int.SInt.add(b, d)),
      Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(a, x), Int.SInt.add(b, Int.SInt.add(c, d)), Int.SInt.add(Int.SInt.add(b, c), d), SL.sint_add_assoc(b, c, d)),
      Equal.trans(Int.SInt, Int.SInt.add(a, Int.SInt.add(Int.SInt.add(b, c), d)), Int.SInt.add(a, Int.SInt.add(Int.SInt.add(c, b), d)), Int.SInt.add(Int.SInt.add(a, c), Int.SInt.add(b, d)),
        Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(a, Int.SInt.add(x, d)), Int.SInt.add(b, c), Int.SInt.add(c, b), SL.sint_add_comm(b, c)),
        Equal.trans(Int.SInt, Int.SInt.add(a, Int.SInt.add(Int.SInt.add(c, b), d)), Int.SInt.add(a, Int.SInt.add(c, Int.SInt.add(b, d))), Int.SInt.add(Int.SInt.add(a, c), Int.SInt.add(b, d)),
          Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(a, x), Int.SInt.add(Int.SInt.add(c, b), d), Int.SInt.add(c, Int.SInt.add(b, d)),
            Equal.sym(Int.SInt, Int.SInt.add(c, Int.SInt.add(b, d)), Int.SInt.add(Int.SInt.add(c, b), d), SL.sint_add_assoc(c, b, d))),
          SL.sint_add_assoc(a, c, Int.SInt.add(b, d))))))

# add(node_balance.go(edges,n), zero()) == node_balance.go(edges,n), for
# ANY edges (no well-formedness needed on Edge.current). This is NOT the
# same as the false-in-general {add(x,zero())==x} for arbitrary opaque
# x:SInt (that fails when x is the non-canonical SInt{False,0n} -- from_diff
# never produces it, but SInt.add's False,False branch or a raw user Edge
# current in principle could). Associativity pushes the "+zero()" past the
# head all the way to the tail, where it lands on a strictly smaller
# instance of this SAME lemma -- bottoming out at Nil+Nil, both concrete
# zero()s, never needing the general (false) identity for an opaque value.
def add_zero_r_nb(+edges: +List<Circuit.Edge>, +n: Nat) -> {Int.SInt.add(Circuit.node_balance.go(edges, n), Int.SInt.zero()) == Circuit.node_balance.go(edges, n) : Int.SInt}:
  match edges:
    case Nil{}:
      {==}
    case e <> t:
      Equal.trans(Int.SInt, Int.SInt.add(Circuit.node_balance.go(e <> t, n), Int.SInt.zero()), Int.SInt.add(Circuit.edge_contribution(n, e), Int.SInt.add(Circuit.node_balance.go(t, n), Int.SInt.zero())), Circuit.node_balance.go(e <> t, n),
        Equal.sym(Int.SInt, Int.SInt.add(Circuit.edge_contribution(n, e), Int.SInt.add(Circuit.node_balance.go(t, n), Int.SInt.zero())), Int.SInt.add(Circuit.node_balance.go(e <> t, n), Int.SInt.zero()),
          SL.sint_add_assoc(Circuit.edge_contribution(n, e), Circuit.node_balance.go(t, n), Int.SInt.zero())),
        Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Circuit.edge_contribution(n, e), x), Int.SInt.add(Circuit.node_balance.go(t, n), Int.SInt.zero()), Circuit.node_balance.go(t, n),
          add_zero_r_nb(t, n)))

# The per-edge step of node_balance_map_update, generalized over a bare `is_loop:
# Bool` parameter (not the computed `is_loop_edge(loop,e)` expression itself --
# Bend can't `match` a computed value, only a function's own parameter; the
# caller below applies this lemma AT that computed, possibly-stuck expression,
# which Bend accepts as ordinary application and substitutes correctly).
# `Bool.pick` mirrors exactly how add_loop_current.update (match) and
# node_balance_delta_scaled.go (Bool.pick) themselves branch on this same
# is_loop value, so the two sides below line up with what those defs actually
# unfold to once applied to the real is_loop_edge(loop,e) argument.
def node_balance_map_update.edge_step(+is_loop: Bool, +is_to: Bool, +is_from: Bool, +cur: Int.SInt, +delta: Int.SInt, +nb_t: Int.SInt, +nbds_t: Int.SInt)
  -> {Int.SInt.add(Circuit.edge_contribution.go(is_to, is_from, Bool.pick(Int.SInt, is_loop, Int.SInt.add(cur, delta), cur)), Int.SInt.add(nb_t, nbds_t))
      == Int.SInt.add(Int.SInt.add(Circuit.edge_contribution.go(is_to, is_from, cur), nb_t),
           Bool.pick(Int.SInt, is_loop, Int.SInt.add(Circuit.edge_contribution.go(Bool.and(is_loop, is_to), Bool.and(is_loop, is_from), delta), nbds_t), nbds_t))
      : Int.SInt}:
  match is_loop:
    case True{}:
      Equal.trans(Int.SInt, Int.SInt.add(Circuit.edge_contribution.go(is_to, is_from, Int.SInt.add(cur, delta)), Int.SInt.add(nb_t, nbds_t)),
        Int.SInt.add(Int.SInt.add(Circuit.edge_contribution.go(is_to, is_from, cur), Circuit.edge_contribution.go(is_to, is_from, delta)), Int.SInt.add(nb_t, nbds_t)),
        Int.SInt.add(Int.SInt.add(Circuit.edge_contribution.go(is_to, is_from, cur), nb_t), Int.SInt.add(Circuit.edge_contribution.go(is_to, is_from, delta), nbds_t)),
        Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(x, Int.SInt.add(nb_t, nbds_t)), Circuit.edge_contribution.go(is_to, is_from, Int.SInt.add(cur, delta)), Int.SInt.add(Circuit.edge_contribution.go(is_to, is_from, cur), Circuit.edge_contribution.go(is_to, is_from, delta)),
          edge_contribution_go_additive(is_to, is_from, cur, delta)),
        four_term_swap(Circuit.edge_contribution.go(is_to, is_from, cur), Circuit.edge_contribution.go(is_to, is_from, delta), nb_t, nbds_t))
    case False{}:
      SL.sint_add_assoc(Circuit.edge_contribution.go(is_to, is_from, cur), nb_t, nbds_t)

# Bridges add_loop_current.update's own `match` branching (used to build the
# updated Edge) with edge_step's `Bool.pick` formulation of the same
# case split -- both compile from the same is_loop parameter, but Bend
# doesn't identify a match-expression with a Bool.pick call just because
# they're semantically the same function; this makes the link explicit.
def edge_contribution_after_update(+is_loop: Bool, +f: Nat, +tt: Nat, +n: Nat, +cur: Int.SInt, +delta: Int.SInt)
  -> {Circuit.edge_contribution(n, Circuit.add_loop_current.update(is_loop, Circuit.Edge{f, tt, cur}, delta))
      == Circuit.edge_contribution.go(Nat.is_eq(tt, n), Nat.is_eq(f, n), Bool.pick(Int.SInt, is_loop, Int.SInt.add(cur, delta), cur))
      : Int.SInt}:
  match is_loop:
    case True{}:
      {==}
    case False{}:
      {==}

# The main structural fact: updating every loop edge's current by `delta`
# shifts node n's balance by exactly node_balance_delta_scaled -- proven by
# induction on edges. Takes `nodes` (the loop's raw node list) instead of a
# `Loop` so that every place is_loop_edge/node_balance_delta_scaled would
# otherwise get stuck on an abstract `loop` parameter instead reduces down to
# the SAME shared, syntactically-identical (if still abstract) boolean
# `is_loop_edge.check(loop_pairs(nodes), f, tt)` -- letting edge_step's
# Bool.pick-shaped conclusion line up with what node_balance.go/
# node_balance_delta_scaled.go actually unfold to on a manifest Loop{nodes}.
def node_balance_map_update(+edges: +List<Circuit.Edge>, +nodes: +List<Nat>, +delta: Int.SInt, +n: Nat)
  -> {Circuit.node_balance.go(Circuit.add_loop_current.go(edges, Circuit.Loop{nodes}, delta), n)
      == Int.SInt.add(Circuit.node_balance.go(edges, n), Circuit.node_balance_delta_scaled.go(edges, Circuit.Loop{nodes}, n, delta))
      : Int.SInt}:
  match edges:
    case Nil{}:
      {==}
    case e <> t:
      match e:
        case Circuit.Edge{f, tt, cur}:
          +is_loop = Circuit.is_loop_edge.check(Circuit.loop_pairs(nodes), f, tt)
          +is_to = Nat.is_eq(tt, n)
          +is_from = Nat.is_eq(f, n)
          +nb_t = Circuit.node_balance.go(t, n)
          +nbds_t = Circuit.node_balance_delta_scaled.go(t, Circuit.Loop{nodes}, n, delta)
          Equal.trans(Int.SInt,
            Int.SInt.add(Circuit.edge_contribution(n, Circuit.add_loop_current.update(is_loop, Circuit.Edge{f, tt, cur}, delta)), Circuit.node_balance.go(Circuit.add_loop_current.go(t, Circuit.Loop{nodes}, delta), n)),
            Int.SInt.add(Circuit.edge_contribution.go(is_to, is_from, Bool.pick(Int.SInt, is_loop, Int.SInt.add(cur, delta), cur)), Circuit.node_balance.go(Circuit.add_loop_current.go(t, Circuit.Loop{nodes}, delta), n)),
            Int.SInt.add(Circuit.node_balance.go(e <> t, n), Circuit.node_balance_delta_scaled.go(e <> t, Circuit.Loop{nodes}, n, delta)),
            Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(x, Circuit.node_balance.go(Circuit.add_loop_current.go(t, Circuit.Loop{nodes}, delta), n)),
              Circuit.edge_contribution(n, Circuit.add_loop_current.update(is_loop, Circuit.Edge{f, tt, cur}, delta)), Circuit.edge_contribution.go(is_to, is_from, Bool.pick(Int.SInt, is_loop, Int.SInt.add(cur, delta), cur)),
              edge_contribution_after_update(is_loop, f, tt, n, cur, delta)),
            Equal.trans(Int.SInt,
              Int.SInt.add(Circuit.edge_contribution.go(is_to, is_from, Bool.pick(Int.SInt, is_loop, Int.SInt.add(cur, delta), cur)), Circuit.node_balance.go(Circuit.add_loop_current.go(t, Circuit.Loop{nodes}, delta), n)),
              Int.SInt.add(Circuit.edge_contribution.go(is_to, is_from, Bool.pick(Int.SInt, is_loop, Int.SInt.add(cur, delta), cur)), Int.SInt.add(nb_t, nbds_t)),
              Int.SInt.add(Circuit.node_balance.go(e <> t, n), Circuit.node_balance_delta_scaled.go(e <> t, Circuit.Loop{nodes}, n, delta)),
              Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Circuit.edge_contribution.go(is_to, is_from, Bool.pick(Int.SInt, is_loop, Int.SInt.add(cur, delta), cur)), x),
                Circuit.node_balance.go(Circuit.add_loop_current.go(t, Circuit.Loop{nodes}, delta), n), Int.SInt.add(nb_t, nbds_t),
                node_balance_map_update(t, nodes, delta, n)),
              node_balance_map_update.edge_step(is_loop, is_to, is_from, cur, delta, nb_t, nbds_t)))

# --- Bridging the unit-delta circulation hypothesis to arbitrary delta -----

def mag_of(x: Int.SInt) -> Nat:
  match x:
    case Int.SInt{s, m}:
      m

# from_diff(m,m) is always zero -- needed to close add_neg_self's mixed-sign
# cases (adding a value to its own negation always lands on a "ups==downs"
# from_diff call).
def from_diff_diag(+m: Nat) -> {Int.SInt.from_diff(m, m) == Int.SInt.zero() : Int.SInt}:
  match m:
    case 0n:
      {==}
    case 1n+mp:
      Equal.trans(Int.SInt, Int.SInt.from_diff(1n+mp, 1n+mp), Int.SInt.from_diff(mp, mp), Int.SInt.zero(),
        SL.shift_invariant(mp, mp), from_diff_diag(mp))

# add(x, neg(x)) == zero() for ALL x (no non-canonical-zero exception here --
# unlike add(x,zero()), this one holds unconditionally, since it always
# routes through from_diff(m,m) or a manifestly-zero same-sign case).
def add_neg_self(+x: Int.SInt) -> {Int.SInt.add(x, Int.SInt.neg(x)) == Int.SInt.zero() : Int.SInt}:
  match x:
    case Int.SInt{True{}, 0n}:
      {==}
    case Int.SInt{True{}, 1n+mp}:
      from_diff_diag(1n+mp)
    case Int.SInt{False{}, m}:
      from_diff_diag(m)

# u==d whenever from_diff(u,d)==zero() -- proven directly by structural
# induction on (u,d) (not via Nat.cmp/Nat.sub), using shift_invariant to peel
# layers and a bare `mag_of` projection to read off a Nat equality from the
# (impossible, but assumed) SInt equality in the two mismatched base cases.
def from_diff_zero_implies_eq(+u: Nat, +d: Nat, +h: {Int.SInt.from_diff(u, d) == Int.SInt.zero() : Int.SInt}) -> {u == d : Nat}:
  match u d:
    case 0n 0n:
      {==}
    case 0n 1n+dp:
      Equal.sym(Nat, 1n+dp, 0n, Equal.cong(Int.SInt, Nat, mag_of, Int.SInt.from_diff(0n, 1n+dp), Int.SInt.zero(), h))
    case 1n+up 0n:
      Equal.cong(Int.SInt, Nat, mag_of, Int.SInt.from_diff(1n+up, 0n), Int.SInt.zero(), h)
    case 1n+up 1n+dp:
      Equal.cong(Nat, Nat, x => 1n+x, up, dp,
        from_diff_zero_implies_eq(up, dp,
          Equal.trans(Int.SInt, Int.SInt.from_diff(up, dp), Int.SInt.from_diff(1n+up, 1n+dp), Int.SInt.zero(),
            Equal.sym(Int.SInt, Int.SInt.from_diff(1n+up, 1n+dp), Int.SInt.from_diff(up, dp), SL.shift_invariant(up, dp)),
            h)))

# add(of_nat(a), neg(of_nat(b))) == from_diff(a,b) -- connects Nat-count
# arithmetic to from_diff so the circulation hypothesis (stated via
# node_balance_delta, itself defined through from_diff/edge_contribution)
# can be read as a fact about two plain touch-counts.
def of_nat_diff(+a: Nat, +b: Nat) -> {Int.SInt.add(Int.SInt.of_nat(a), Int.SInt.neg(Int.SInt.of_nat(b))) == Int.SInt.from_diff(a, b) : Int.SInt}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+ap 0n:
      %SL.nat_add_zero_r(ap) : {Int.SInt{True{}, 1n+Nat.add(ap, 0n)} == Int.SInt{True{}, 1n+_} : Int.SInt}
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      {==}

# repeat_add(k,x): x added to itself k times (zero() for k=0). Deliberately
# the SIMPLE uniform recursion (no special k=1 case) -- the "successor" fact
# repeat_add(1+k,x)==add(x,repeat_add(k,x)) is then TRUE BY DEFINITION for
# every k including 0, so combining steps below only ever needs associativity
# and add_neg_self, never the false {add(x,zero())==x} for opaque x.
def repeat_add(+k: Nat, +x: Int.SInt) -> Int.SInt:
  match k:
    case 0n:
      Int.SInt.zero()
    case 1n+kp:
      Int.SInt.add(x, repeat_add(kp, x))

def repeat_add_cancel(+k: Nat, +delta: Int.SInt) -> {Int.SInt.add(repeat_add(k, delta), repeat_add(k, Int.SInt.neg(delta))) == Int.SInt.zero() : Int.SInt}:
  match k:
    case 0n:
      {==}
    case 1n+kp:
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.add(delta, repeat_add(kp, delta)), Int.SInt.add(Int.SInt.neg(delta), repeat_add(kp, Int.SInt.neg(delta)))),
        Int.SInt.add(Int.SInt.add(delta, Int.SInt.neg(delta)), Int.SInt.add(repeat_add(kp, delta), repeat_add(kp, Int.SInt.neg(delta)))),
        Int.SInt.zero(),
        four_term_swap(delta, repeat_add(kp, delta), Int.SInt.neg(delta), repeat_add(kp, Int.SInt.neg(delta))),
        Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.add(delta, Int.SInt.neg(delta)), Int.SInt.add(repeat_add(kp, delta), repeat_add(kp, Int.SInt.neg(delta)))),
          Int.SInt.add(Int.SInt.zero(), Int.SInt.add(repeat_add(kp, delta), repeat_add(kp, Int.SInt.neg(delta)))),
          Int.SInt.zero(),
          Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(x, Int.SInt.add(repeat_add(kp, delta), repeat_add(kp, Int.SInt.neg(delta)))), Int.SInt.add(delta, Int.SInt.neg(delta)), Int.SInt.zero(), add_neg_self(delta)),
          Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.zero(), Int.SInt.add(repeat_add(kp, delta), repeat_add(kp, Int.SInt.neg(delta)))),
            Int.SInt.add(Int.SInt.zero(), Int.SInt.zero()),
            Int.SInt.zero(),
            Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Int.SInt.zero(), x), Int.SInt.add(repeat_add(kp, delta), repeat_add(kp, Int.SInt.neg(delta))), Int.SInt.zero(), repeat_add_cancel(kp, delta)),
            {==})))

def repeat_add_of_nat(+k: Nat) -> {repeat_add(k, Int.SInt.of_nat(1n)) == Int.SInt.of_nat(k) : Int.SInt}:
  match k:
    case 0n:
      {==}
    case 1n+kp:
      Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Int.SInt.of_nat(1n), x), repeat_add(kp, Int.SInt.of_nat(1n)), Int.SInt.of_nat(kp), repeat_add_of_nat(kp))

def repeat_add_neg_of_nat.combine(+kp: Nat) -> {Int.SInt.add(Int.SInt.neg(Int.SInt.of_nat(1n)), Int.SInt.neg(Int.SInt.of_nat(kp))) == Int.SInt.neg(Int.SInt.of_nat(1n+kp)) : Int.SInt}:
  match kp:
    case 0n:
      {==}
    case 1n+kpp:
      {==}

def repeat_add_neg_of_nat(+k: Nat) -> {repeat_add(k, Int.SInt.neg(Int.SInt.of_nat(1n))) == Int.SInt.neg(Int.SInt.of_nat(k)) : Int.SInt}:
  match k:
    case 0n:
      {==}
    case 1n+kp:
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.neg(Int.SInt.of_nat(1n)), repeat_add(kp, Int.SInt.neg(Int.SInt.of_nat(1n)))),
        Int.SInt.add(Int.SInt.neg(Int.SInt.of_nat(1n)), Int.SInt.neg(Int.SInt.of_nat(kp))),
        Int.SInt.neg(Int.SInt.of_nat(1n+kp)),
        Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Int.SInt.neg(Int.SInt.of_nat(1n)), x), repeat_add(kp, Int.SInt.neg(Int.SInt.of_nat(1n))), Int.SInt.neg(Int.SInt.of_nat(kp)), repeat_add_neg_of_nat(kp)),
        repeat_add_neg_of_nat.combine(kp))

# --- add(zero(), X) == X, but ONLY for X-shapes that are provably safe -----
# (never the pathological SInt{False,0n}) -- direct facts for the two
# manifest-shape SInt cases, plus a from-scratch induction for the
# pathological shape itself (repeat_add HEALS it to canonical zero at every
# step, so the fact is still true there, just needs a different argument).

def add_zero_l_true(+xm: Nat) -> {Int.SInt.add(Int.SInt.zero(), Int.SInt{True{}, xm}) == Int.SInt{True{}, xm} : Int.SInt}:
  {==}

def add_zero_l_false_pos(+xmp: Nat) -> {Int.SInt.add(Int.SInt.zero(), Int.SInt{False{}, 1n+xmp}) == Int.SInt{False{}, 1n+xmp} : Int.SInt}:
  {==}

def add_zero_l_false_zero_repeat(+k: Nat) -> {repeat_add(k, Int.SInt{False{}, 0n}) == Int.SInt.zero() : Int.SInt}:
  match k:
    case 0n:
      {==}
    case 1n+kp:
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt{False{}, 0n}, repeat_add(kp, Int.SInt{False{}, 0n})), Int.SInt.add(Int.SInt{False{}, 0n}, Int.SInt.zero()), Int.SInt.zero(),
        Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Int.SInt{False{}, 0n}, x), repeat_add(kp, Int.SInt{False{}, 0n}), Int.SInt.zero(), add_zero_l_false_zero_repeat(kp)),
        {==})

# add(zero(), repeat_add(k,x)) == repeat_add(k,x) whenever x is NOT the
# pathological value. For True/False-nonzero x, one assoc step + the direct
# add_zero_l_* fact for x itself suffices (no k-induction needed at all).
def add_zero_l_repeat_safe(+k: Nat, +x: Int.SInt, +hx: {Int.SInt.add(Int.SInt.zero(), x) == x : Int.SInt}) -> {Int.SInt.add(Int.SInt.zero(), repeat_add(k, x)) == repeat_add(k, x) : Int.SInt}:
  match k:
    case 0n:
      {==}
    case 1n+kp:
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.zero(), Int.SInt.add(x, repeat_add(kp, x))), Int.SInt.add(Int.SInt.add(Int.SInt.zero(), x), repeat_add(kp, x)), Int.SInt.add(x, repeat_add(kp, x)),
        SL.sint_add_assoc(Int.SInt.zero(), x, repeat_add(kp, x)),
        Equal.cong(Int.SInt, Int.SInt, y => Int.SInt.add(y, repeat_add(kp, x)), Int.SInt.add(Int.SInt.zero(), x), x, hx))

def add_zero_l_repeat(+k: Nat, +x: Int.SInt) -> {Int.SInt.add(Int.SInt.zero(), repeat_add(k, x)) == repeat_add(k, x) : Int.SInt}:
  match x:
    case Int.SInt{True{}, xm}:
      add_zero_l_repeat_safe(k, Int.SInt{True{}, xm}, add_zero_l_true(xm))
    case Int.SInt{False{}, 0n}:
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.zero(), repeat_add(k, Int.SInt{False{}, 0n})), Int.SInt.add(Int.SInt.zero(), Int.SInt.zero()), repeat_add(k, Int.SInt{False{}, 0n}),
        Equal.cong(Int.SInt, Int.SInt, y => Int.SInt.add(Int.SInt.zero(), y), repeat_add(k, Int.SInt{False{}, 0n}), Int.SInt.zero(), add_zero_l_false_zero_repeat(k)),
        Equal.sym(Int.SInt, repeat_add(k, Int.SInt{False{}, 0n}), Int.SInt.zero(), add_zero_l_false_zero_repeat(k)))
    case Int.SInt{False{}, 1n+xmp}:
      add_zero_l_repeat_safe(k, Int.SInt{False{}, 1n+xmp}, add_zero_l_false_pos(xmp))

# Lifting add_zero_l_repeat over a sum: only needs the fact for the FIRST
# summand -- pure associativity carries it the rest of the way, regardless
# of what the second summand is.
def add_zero_l_sum(+a: Int.SInt, +b: Int.SInt, +ha: {Int.SInt.add(Int.SInt.zero(), a) == a : Int.SInt}) -> {Int.SInt.add(Int.SInt.zero(), Int.SInt.add(a, b)) == Int.SInt.add(a, b) : Int.SInt}:
  Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.zero(), Int.SInt.add(a, b)), Int.SInt.add(Int.SInt.add(Int.SInt.zero(), a), b), Int.SInt.add(a, b),
    SL.sint_add_assoc(Int.SInt.zero(), a, b),
    Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(x, b), Int.SInt.add(Int.SInt.zero(), a), a, ha))

# add(a,add(b,c)) == add(b,add(a,c)) -- general, safe for all a,b,c (pure
# assoc+comm, no zero involved).
def middle_swap(+a: Int.SInt, +b: Int.SInt, +c: Int.SInt) -> {Int.SInt.add(a, Int.SInt.add(b, c)) == Int.SInt.add(b, Int.SInt.add(a, c)) : Int.SInt}:
  Equal.trans(Int.SInt, Int.SInt.add(a, Int.SInt.add(b, c)), Int.SInt.add(Int.SInt.add(a, b), c), Int.SInt.add(b, Int.SInt.add(a, c)),
    SL.sint_add_assoc(a, b, c),
    Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.add(a, b), c), Int.SInt.add(Int.SInt.add(b, a), c), Int.SInt.add(b, Int.SInt.add(a, c)),
      Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(x, c), Int.SInt.add(a, b), Int.SInt.add(b, a), SL.sint_add_comm(a, b)),
      Equal.sym(Int.SInt, Int.SInt.add(b, Int.SInt.add(a, c)), Int.SInt.add(Int.SInt.add(b, a), c), SL.sint_add_assoc(b, a, c))))

# --- Touch counts and the CHAR correspondence -------------------------------

def touch_to.go(edges: +List<Circuit.Edge>, +nodes: +List<Nat>, +n: Nat) -> Nat:
  match edges:
    case Nil{}:
      0n
    case +e <> +t:
      match e:
        case Circuit.Edge{f, tt, cur}:
          +is_loop = Circuit.is_loop_edge.check(Circuit.loop_pairs(nodes), f, tt)
          Bool.pick(Nat, Bool.and(is_loop, Nat.is_eq(tt, n)), 1n+touch_to.go(t, nodes, n), touch_to.go(t, nodes, n))

def touch_from.go(edges: +List<Circuit.Edge>, +nodes: +List<Nat>, +n: Nat) -> Nat:
  match edges:
    case Nil{}:
      0n
    case +e <> +t:
      match e:
        case Circuit.Edge{f, tt, cur}:
          +is_loop = Circuit.is_loop_edge.check(Circuit.loop_pairs(nodes), f, tt)
          Bool.pick(Nat, Bool.and(is_loop, Nat.is_eq(f, n)), 1n+touch_from.go(t, nodes, n), touch_from.go(t, nodes, n))

# The per-edge step of CHAR, generalized over bare is_loop/is_to/is_from Bool
# parameters (same "wrap the computed value as a matchable parameter" trick
# as node_balance_map_update.edge_step).
def char_step(+is_loop: Bool, +is_to: Bool, +is_from: Bool, +delta: Int.SInt, +ct_t: Nat, +cf_t: Nat, +tail: Int.SInt,
    +h: {tail == Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta))) : Int.SInt})
  -> {Bool.pick(Int.SInt, is_loop, Int.SInt.add(Circuit.edge_contribution.go(Bool.and(is_loop, is_to), Bool.and(is_loop, is_from), delta), tail), tail)
      == Int.SInt.add(repeat_add(Bool.pick(Nat, Bool.and(is_loop, is_to), 1n+ct_t, ct_t), delta), repeat_add(Bool.pick(Nat, Bool.and(is_loop, is_from), 1n+cf_t, cf_t), Int.SInt.neg(delta)))
      : Int.SInt}:
  match is_loop:
    case False{}:
      h
    case True{}:
      match is_to is_from:
        case True{} True{}:
          Equal.trans(Int.SInt,
            Int.SInt.add(Int.SInt.zero(), tail),
            Int.SInt.add(Int.SInt.zero(), Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta)))),
            Int.SInt.add(repeat_add(1n+ct_t, delta), repeat_add(1n+cf_t, Int.SInt.neg(delta))),
            Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Int.SInt.zero(), x), tail, Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta))), h),
            Equal.trans(Int.SInt,
              Int.SInt.add(Int.SInt.zero(), Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta)))),
              Int.SInt.add(Int.SInt.add(delta, Int.SInt.neg(delta)), Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta)))),
              Int.SInt.add(repeat_add(1n+ct_t, delta), repeat_add(1n+cf_t, Int.SInt.neg(delta))),
              Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(x, Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta)))), Int.SInt.zero(), Int.SInt.add(delta, Int.SInt.neg(delta)),
                Equal.sym(Int.SInt, Int.SInt.add(delta, Int.SInt.neg(delta)), Int.SInt.zero(), add_neg_self(delta))),
              Equal.trans(Int.SInt,
                Int.SInt.add(Int.SInt.add(delta, Int.SInt.neg(delta)), Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta)))),
                Int.SInt.add(Int.SInt.add(delta, repeat_add(ct_t, delta)), Int.SInt.add(Int.SInt.neg(delta), repeat_add(cf_t, Int.SInt.neg(delta)))),
                Int.SInt.add(repeat_add(1n+ct_t, delta), repeat_add(1n+cf_t, Int.SInt.neg(delta))),
                four_term_swap(delta, Int.SInt.neg(delta), repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta))),
                {==})))
        case True{} False{}:
          Equal.trans(Int.SInt, Int.SInt.add(Circuit.edge_contribution.go(True{}, False{}, delta), tail), Int.SInt.add(delta, tail), Int.SInt.add(repeat_add(1n+ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta))),
            {==},
            Equal.trans(Int.SInt, Int.SInt.add(delta, tail), Int.SInt.add(delta, Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta)))), Int.SInt.add(repeat_add(1n+ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta))),
              Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(delta, x), tail, Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta))), h),
              SL.sint_add_assoc(delta, repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta)))))
        case False{} True{}:
          Equal.trans(Int.SInt, Int.SInt.add(Circuit.edge_contribution.go(False{}, True{}, delta), tail), Int.SInt.add(Int.SInt.neg(delta), tail), Int.SInt.add(repeat_add(ct_t, delta), repeat_add(1n+cf_t, Int.SInt.neg(delta))),
            {==},
            Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.neg(delta), tail), Int.SInt.add(Int.SInt.neg(delta), Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta)))), Int.SInt.add(repeat_add(ct_t, delta), repeat_add(1n+cf_t, Int.SInt.neg(delta))),
              Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Int.SInt.neg(delta), x), tail, Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta))), h),
              middle_swap(Int.SInt.neg(delta), repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta)))))
        case False{} False{}:
          Equal.trans(Int.SInt, Int.SInt.add(Circuit.edge_contribution.go(False{}, False{}, delta), tail), Int.SInt.add(Int.SInt.zero(), tail), Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta))),
            {==},
            Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.zero(), tail), Int.SInt.add(Int.SInt.zero(), Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta)))), Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta))),
              Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Int.SInt.zero(), x), tail, Int.SInt.add(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta))), h),
              add_zero_l_sum(repeat_add(ct_t, delta), repeat_add(cf_t, Int.SInt.neg(delta)), add_zero_l_repeat(ct_t, delta))))

# The counting correspondence: node_balance_delta_scaled equals the touch
# counts scaled by +-delta.
def char_correspondence(+edges: +List<Circuit.Edge>, +nodes: +List<Nat>, +n: Nat, +delta: Int.SInt)
  -> {Circuit.node_balance_delta_scaled.go(edges, Circuit.Loop{nodes}, n, delta)
      == Int.SInt.add(repeat_add(touch_to.go(edges, nodes, n), delta), repeat_add(touch_from.go(edges, nodes, n), Int.SInt.neg(delta)))
      : Int.SInt}:
  match edges:
    case Nil{}:
      {==}
    case e <> t:
      match e:
        case Circuit.Edge{f, tt, cur}:
          char_step(Circuit.is_loop_edge.check(Circuit.loop_pairs(nodes), f, tt), Nat.is_eq(tt, n), Nat.is_eq(f, n), delta,
            touch_to.go(t, nodes, n), touch_from.go(t, nodes, n), Circuit.node_balance_delta_scaled.go(t, Circuit.Loop{nodes}, n, delta),
            char_correspondence(t, nodes, n, delta))

# The unit-delta touch counts satisfy from_diff(ct,cf)==node_balance_delta,
# via char_correspondence + the closed forms for repeat_add at of_nat(1n).
def char_unit(+edges: +List<Circuit.Edge>, +nodes: +List<Nat>, +n: Nat)
  -> {Int.SInt.from_diff(touch_to.go(edges, nodes, n), touch_from.go(edges, nodes, n)) == Circuit.node_balance_delta.go(edges, Circuit.Loop{nodes}, n) : Int.SInt}:
  +ct = touch_to.go(edges, nodes, n)
  +cf = touch_from.go(edges, nodes, n)
  Equal.trans(Int.SInt, Int.SInt.from_diff(ct, cf), Int.SInt.add(Int.SInt.of_nat(ct), Int.SInt.neg(Int.SInt.of_nat(cf))), Circuit.node_balance_delta.go(edges, Circuit.Loop{nodes}, n),
    Equal.sym(Int.SInt, Int.SInt.add(Int.SInt.of_nat(ct), Int.SInt.neg(Int.SInt.of_nat(cf))), Int.SInt.from_diff(ct, cf), of_nat_diff(ct, cf)),
    Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.of_nat(ct), Int.SInt.neg(Int.SInt.of_nat(cf))), Int.SInt.add(repeat_add(ct, Int.SInt.of_nat(1n)), repeat_add(cf, Int.SInt.neg(Int.SInt.of_nat(1n)))), Circuit.node_balance_delta.go(edges, Circuit.Loop{nodes}, n),
      Equal.sym(Int.SInt, Int.SInt.add(repeat_add(ct, Int.SInt.of_nat(1n)), repeat_add(cf, Int.SInt.neg(Int.SInt.of_nat(1n)))), Int.SInt.add(Int.SInt.of_nat(ct), Int.SInt.neg(Int.SInt.of_nat(cf))),
        Equal.trans(Int.SInt, Int.SInt.add(repeat_add(ct, Int.SInt.of_nat(1n)), repeat_add(cf, Int.SInt.neg(Int.SInt.of_nat(1n)))), Int.SInt.add(Int.SInt.of_nat(ct), repeat_add(cf, Int.SInt.neg(Int.SInt.of_nat(1n)))), Int.SInt.add(Int.SInt.of_nat(ct), Int.SInt.neg(Int.SInt.of_nat(cf))),
          Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(x, repeat_add(cf, Int.SInt.neg(Int.SInt.of_nat(1n)))), repeat_add(ct, Int.SInt.of_nat(1n)), Int.SInt.of_nat(ct), repeat_add_of_nat(ct)),
          Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Int.SInt.of_nat(ct), x), repeat_add(cf, Int.SInt.neg(Int.SInt.of_nat(1n))), Int.SInt.neg(Int.SInt.of_nat(cf)), repeat_add_neg_of_nat(cf)))),
      Equal.sym(Int.SInt, Circuit.node_balance_delta.go(edges, Circuit.Loop{nodes}, n), Int.SInt.add(repeat_add(ct, Int.SInt.of_nat(1n)), repeat_add(cf, Int.SInt.neg(Int.SInt.of_nat(1n)))),
        char_correspondence(edges, nodes, n, Int.SInt.of_nat(1n)))))

# Main bridge: given the (unit-delta) circulation hypothesis, the
# arbitrary-delta scaled sum is also zero.
def circulation_implies_scaled_zero(+edges: +List<Circuit.Edge>, +nodes: +List<Nat>, +n: Nat, +delta: Int.SInt,
    +circ: {Circuit.node_balance_delta.go(edges, Circuit.Loop{nodes}, n) == Int.SInt.zero() : Int.SInt})
  -> {Circuit.node_balance_delta_scaled.go(edges, Circuit.Loop{nodes}, n, delta) == Int.SInt.zero() : Int.SInt}:
  +ct = touch_to.go(edges, nodes, n)
  +cf = touch_from.go(edges, nodes, n)
  +ct_eq_cf = from_diff_zero_implies_eq(ct, cf, Equal.trans(Int.SInt, Int.SInt.from_diff(ct, cf), Circuit.node_balance_delta.go(edges, Circuit.Loop{nodes}, n), Int.SInt.zero(), char_unit(edges, nodes, n), circ))
  Equal.trans(Int.SInt, Circuit.node_balance_delta_scaled.go(edges, Circuit.Loop{nodes}, n, delta), Int.SInt.add(repeat_add(ct, delta), repeat_add(cf, Int.SInt.neg(delta))), Int.SInt.zero(),
    char_correspondence(edges, nodes, n, delta),
    Equal.trans(Int.SInt, Int.SInt.add(repeat_add(ct, delta), repeat_add(cf, Int.SInt.neg(delta))), Int.SInt.add(repeat_add(ct, delta), repeat_add(ct, Int.SInt.neg(delta))), Int.SInt.zero(),
      Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(repeat_add(ct, delta), x), repeat_add(cf, Int.SInt.neg(delta)), repeat_add(ct, Int.SInt.neg(delta)),
        Equal.cong(Nat, Int.SInt, x => repeat_add(x, Int.SInt.neg(delta)), cf, ct, Equal.sym(Nat, ct, cf, ct_eq_cf))),
      repeat_add_cancel(ct, delta)))
