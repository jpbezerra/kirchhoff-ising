# Scratch/exploratory proof of SInt.from_diff's "shift invariance" and the
# diff_inc/diff_dec step lemmas -- the pieces that unlocked
# bend/ising/PROOF.bend's flip_changes_magnetization_by_two (previously an
# open ?TODO). The real, in-use copies of these lemmas live in
# bend/ising/PROOF.bend; this file is kept as a standalone, independently
# checkable record of how they were derived. Run with `bend
# bend/tests/sint_laws.bend`.

import Base
import ../int.bend as Int

def from_diff_cmp_shift(c: Cmp, +x: Nat, +y: Nat) -> {Int.SInt.from_diff.cmp(c, 1n+x, 1n+y) == Int.SInt.from_diff.cmp(c, x, y) : Int.SInt}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def shift_invariant(+x: Nat, +y: Nat) -> {Int.SInt.from_diff(1n+x, 1n+y) == Int.SInt.from_diff(x, y) : Int.SInt}:
  from_diff_cmp_shift(Nat.cmp(x, y), x, y)

# Nat.add facts (Bend has no `omega`; proven once by hand, same pattern as
# GUIDE.md's add_zero example).

def nat_add_zero_r.succ(+p: Nat, rec: {Nat.add(p, 0n) == p : Nat}) -> {Nat.add(1n+p, 0n) == 1n+p : Nat}:
  %rec : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
  {==}

def nat_add_zero_r(+n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_add_zero_r.succ(p, nat_add_zero_r(p))

def nat_add_succ_r.succ(+p: Nat, +m: Nat, rec: {Nat.add(p, 1n+m) == 1n+Nat.add(p, m) : Nat}) -> {Nat.add(1n+p, 1n+m) == 1n+Nat.add(1n+p, m) : Nat}:
  %rec : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
  {==}

def nat_add_succ_r(+n: Nat, +m: Nat) -> {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_add_succ_r.succ(p, m, nat_add_succ_r(p, m))

def nat_add_comm.zero(+m: Nat) -> {Nat.add(0n, m) == Nat.add(m, 0n) : Nat}:
  %nat_add_zero_r(m) : {_ == Nat.add(m, 0n) : Nat}
  {==}

def nat_add_comm.succ(+p: Nat, +m: Nat, rec: {Nat.add(p, m) == Nat.add(m, p) : Nat}) -> {Nat.add(1n+p, m) == Nat.add(m, 1n+p) : Nat}:
  %Equal.sym(Nat, Nat.add(m, 1n+p), 1n+Nat.add(m, p), nat_add_succ_r(m, p)) : {1n+Nat.add(p, m) == _ : Nat}
  %rec : {1n+Nat.add(p, m) == 1n+_ : Nat}
  {==}

def nat_add_comm(+n: Nat, +m: Nat) -> {Nat.add(n, m) == Nat.add(m, n) : Nat}:
  match n:
    case 0n:
      nat_add_comm.zero(m)
    case 1n+p:
      nat_add_comm.succ(p, m, nat_add_comm(p, m))

# diff_inc: moving one spin from "down" to "up" raises the magnetization by
# exactly 2. The base cases (one side literally 0) resolve by pure
# computation once split on the OTHER side's shape (0n vs 1n+_) -- no
# recursion needed there, just structural peeling of Nat.cmp/Nat.sub, which
# happens for free even with an abstract tail variable. The recursive case
# uses shift_invariant twice to strip a layer off both sides at once.
def diff_inc(+a: Nat, +b: Nat) -> {Int.SInt.from_diff(1n+a, b) == Int.SInt.add(Int.SInt.from_diff(a, 1n+b), Int.SInt{True{}, 2n}) : Int.SInt}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n:
      {==}
    case 0n 2n+bpp:
      {==}
    case 1n 0n:
      {==}
    case 2n+app 0n:
      %nat_add_comm(2n, app) : {Int.SInt{True{}, 3n+app} == Int.SInt{True{}, 1n+_} : Int.SInt}
      {==}
    case 1n+ap 1n+bp:
      %Equal.sym(Int.SInt, Int.SInt.from_diff(1n+(1n+ap), 1n+bp), Int.SInt.from_diff(1n+ap, bp), shift_invariant(1n+ap, bp))
        : {_ == Int.SInt.add(Int.SInt.from_diff(1n+ap, 1n+(1n+bp)), Int.SInt{True{}, 2n}) : Int.SInt}
      %Equal.sym(Int.SInt, Int.SInt.from_diff(1n+ap, 1n+(1n+bp)), Int.SInt.from_diff(ap, 1n+bp), shift_invariant(ap, 1n+bp))
        : {Int.SInt.from_diff(1n+ap, bp) == Int.SInt.add(_, Int.SInt{True{}, 2n}) : Int.SInt}
      diff_inc(ap, bp)

# SInt.add commutativity. Only the same-sign cases need Nat.add_comm; the
# mixed-sign cases are free (both sides reduce to the identical
# from_diff(am,bm) call, since SInt.add's own True/False and False/True
# arms are already symmetric by construction).
def sint_add_comm(+a: Int.SInt, +b: Int.SInt) -> {Int.SInt.add(a, b) == Int.SInt.add(b, a) : Int.SInt}:
  match a b:
    case Int.SInt{True{}, am} Int.SInt{True{}, bm}:
      %nat_add_comm(am, bm) : {Int.SInt{True{}, Nat.add(am, bm)} == Int.SInt{True{}, _} : Int.SInt}
      {==}
    case Int.SInt{False{}, am} Int.SInt{False{}, bm}:
      %nat_add_comm(am, bm) : {Int.SInt{False{}, Nat.add(am, bm)} == Int.SInt{False{}, _} : Int.SInt}
      {==}
    case Int.SInt{True{}, am} Int.SInt{False{}, bm}:
      {==}
    case Int.SInt{False{}, am} Int.SInt{True{}, bm}:
      {==}

def main() -> Nat:
  0n

# diff_dec: moving one spin from "up" to "down" lowers the magnetization by
# exactly 2 -- mirror of diff_inc.
def diff_dec(+a: Nat, +b: Nat) -> {Int.SInt.from_diff(a, 1n+b) == Int.SInt.add(Int.SInt.from_diff(1n+a, b), Int.SInt{False{}, 2n}) : Int.SInt}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      match bp:
        case 0n:
          {==}
        case 1n+bpp:
          %nat_add_comm(2n, bpp) : {Int.SInt{False{}, 3n+bpp} == Int.SInt{False{}, 1n+_} : Int.SInt}
          {==}
    case 1n 0n:
      {==}
    case 2n+app 0n:
      {==}
    case 1n+ap 1n+bp:
      %Equal.sym(Int.SInt, Int.SInt.from_diff(1n+ap, 1n+(1n+bp)), Int.SInt.from_diff(ap, 1n+bp), shift_invariant(ap, 1n+bp))
        : {_ == Int.SInt.add(Int.SInt.from_diff(1n+(1n+ap), 1n+bp), Int.SInt{False{}, 2n}) : Int.SInt}
      %Equal.sym(Int.SInt, Int.SInt.from_diff(1n+(1n+ap), 1n+bp), Int.SInt.from_diff(1n+ap, bp), shift_invariant(1n+ap, bp))
        : {Int.SInt.from_diff(ap, 1n+bp) == Int.SInt.add(_, Int.SInt{False{}, 2n}) : Int.SInt}
      diff_dec(ap, bp)

# nat_add_assoc, needed for SInt.add associativity below.
def nat_add_assoc.succ(+p: Nat, +m: Nat, +k: Nat, rec: {Nat.add(Nat.add(p, m), k) == Nat.add(p, Nat.add(m, k)) : Nat}) -> {Nat.add(Nat.add(1n+p, m), k) == Nat.add(1n+p, Nat.add(m, k)) : Nat}:
  %rec : {1n+Nat.add(Nat.add(p, m), k) == 1n+_ : Nat}
  {==}

def nat_add_assoc(+n: Nat, +m: Nat, +k: Nat) -> {Nat.add(Nat.add(n, m), k) == Nat.add(n, Nat.add(m, k)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_add_assoc.succ(p, m, k, nat_add_assoc(p, m, k))

def add_zero_left(+u2: Nat, +d2: Nat) -> {Int.SInt.add(Int.SInt.zero(), Int.SInt.from_diff(u2, d2)) == Int.SInt.from_diff(u2, d2) : Int.SInt}:
  match u2 d2:
    case 0n 0n:
      {==}
    case 0n 1n+d2p:
      {==}
    case 1n+u2p 0n:
      {==}
    case 1n+u2p 1n+d2p:
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.zero(), Int.SInt.from_diff(1n+u2p, 1n+d2p)), Int.SInt.add(Int.SInt.zero(), Int.SInt.from_diff(u2p, d2p)), Int.SInt.from_diff(1n+u2p, 1n+d2p),
        Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Int.SInt.zero(), x), Int.SInt.from_diff(1n+u2p, 1n+d2p), Int.SInt.from_diff(u2p, d2p), shift_invariant(u2p, d2p)),
        Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.zero(), Int.SInt.from_diff(u2p, d2p)), Int.SInt.from_diff(u2p, d2p), Int.SInt.from_diff(1n+u2p, 1n+d2p),
          add_zero_left(u2p, d2p),
          Equal.sym(Int.SInt, Int.SInt.from_diff(1n+u2p, 1n+d2p), Int.SInt.from_diff(u2p, d2p), shift_invariant(u2p, d2p))))

def add_false_from_diff(+dm: Nat, +u2: Nat, +d2: Nat) -> {Int.SInt.add(Int.SInt{False{}, dm}, Int.SInt.from_diff(u2, d2)) == Int.SInt.from_diff(u2, Nat.add(dm, d2)) : Int.SInt}:
  match u2 d2:
    case 0n 0n:
      %nat_add_zero_r(dm) : {Int.SInt.from_diff(0n, _) == Int.SInt.from_diff(0n, Nat.add(dm, 0n)) : Int.SInt}
      {==}
    case 0n 1n+d2p:
      %Equal.sym(Nat, Nat.add(dm, 1n+d2p), 1n+Nat.add(dm, d2p), nat_add_succ_r(dm, d2p)) : {Int.SInt{False{}, _} == Int.SInt.from_diff(0n, Nat.add(dm, 1n+d2p)) : Int.SInt}
      %Equal.sym(Nat, Nat.add(dm, 1n+d2p), 1n+Nat.add(dm, d2p), nat_add_succ_r(dm, d2p)) : {Int.SInt{False{}, 1n+Nat.add(dm, d2p)} == Int.SInt.from_diff(0n, _) : Int.SInt}
      {==}
    case 1n+u2p 0n:
      %nat_add_zero_r(dm) : {Int.SInt.from_diff(1n+u2p, _) == Int.SInt.from_diff(1n+u2p, Nat.add(dm, 0n)) : Int.SInt}
      {==}
    case 1n+u2p 1n+d2p:
      %Equal.sym(Nat, Nat.add(dm, 1n+d2p), 1n+Nat.add(dm, d2p), nat_add_succ_r(dm, d2p)) : {Int.SInt.add(Int.SInt{False{}, dm}, Int.SInt.from_diff(1n+u2p, 1n+d2p)) == Int.SInt.from_diff(1n+u2p, _) : Int.SInt}
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt{False{}, dm}, Int.SInt.from_diff(1n+u2p, 1n+d2p)), Int.SInt.add(Int.SInt{False{}, dm}, Int.SInt.from_diff(u2p, d2p)), Int.SInt.from_diff(1n+u2p, 1n+Nat.add(dm, d2p)),
        Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Int.SInt{False{}, dm}, x), Int.SInt.from_diff(1n+u2p, 1n+d2p), Int.SInt.from_diff(u2p, d2p), shift_invariant(u2p, d2p)),
        Equal.trans(Int.SInt, Int.SInt.add(Int.SInt{False{}, dm}, Int.SInt.from_diff(u2p, d2p)), Int.SInt.from_diff(u2p, Nat.add(dm, d2p)), Int.SInt.from_diff(1n+u2p, 1n+Nat.add(dm, d2p)),
          add_false_from_diff(dm, u2p, d2p),
          Equal.sym(Int.SInt, Int.SInt.from_diff(1n+u2p, 1n+Nat.add(dm, d2p)), Int.SInt.from_diff(u2p, Nat.add(dm, d2p)), shift_invariant(u2p, Nat.add(dm, d2p)))))

# add_true_from_diff (the True-side mirror of add_false_from_diff).
#
# The mirror case looked identical to add_false_from_diff at first, but
# isn't: from_diff(X, 0n) only reduces for free when X is *manifestly*
# 0n/1n+_ (a visible outer constructor) -- for an opaque expression like
# Nat.add(um, 0n) (um a bare, un-cased function parameter), Nat.cmp is
# stuck on the FIRST argument's shape regardless of the second argument
# being literal 0n. add_false_from_diff's base cases avoided this because
# their stuck argument was always already wrapped in a literal 1n+_.
# Fixed by an *additional* case-split on `um` itself (0n vs 1n+ump),
# crossed with the existing u2/d2 split. The um=0n case collapses to
# add_zero_left exactly (SInt{True,0n} == SInt.zero()); the um=1n+ump case
# needs its own 4-way split on (u2,d2), each closing with the same
# shift_invariant/nat_add_succ_r/zero_r kit used throughout this file.

def add_true_from_diff.pos(+ump: Nat, +u2: Nat, +d2: Nat)
  -> {Int.SInt.add(Int.SInt{True{}, 1n+ump}, Int.SInt.from_diff(u2, d2)) == Int.SInt.from_diff(1n+Nat.add(ump, u2), d2) : Int.SInt}:
  match u2 d2:
    case 0n 0n:
      {==}
    case 0n 1n+d2p:
      %Equal.sym(Nat, Nat.add(ump, 0n), ump, nat_add_zero_r(ump))
        : {Int.SInt.add(Int.SInt{True{}, 1n+ump}, Int.SInt.from_diff(0n, 1n+d2p)) == Int.SInt.from_diff(1n+_, 1n+d2p) : Int.SInt}
      {==}
    case 1n+u2p 0n:
      {==}
    case 1n+u2p 1n+d2p:
      %Equal.sym(Nat, Nat.add(ump, 1n+u2p), 1n+Nat.add(ump, u2p), nat_add_succ_r(ump, u2p))
        : {Int.SInt.add(Int.SInt{True{}, 1n+ump}, Int.SInt.from_diff(1n+u2p, 1n+d2p)) == Int.SInt.from_diff(1n+_, 1n+d2p) : Int.SInt}
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt{True{}, 1n+ump}, Int.SInt.from_diff(1n+u2p, 1n+d2p)), Int.SInt.add(Int.SInt{True{}, 1n+ump}, Int.SInt.from_diff(u2p, d2p)), Int.SInt.from_diff(1n+(1n+Nat.add(ump, u2p)), 1n+d2p),
        Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(Int.SInt{True{}, 1n+ump}, x), Int.SInt.from_diff(1n+u2p, 1n+d2p), Int.SInt.from_diff(u2p, d2p), shift_invariant(u2p, d2p)),
        Equal.trans(Int.SInt, Int.SInt.add(Int.SInt{True{}, 1n+ump}, Int.SInt.from_diff(u2p, d2p)), Int.SInt.from_diff(1n+Nat.add(ump, u2p), d2p), Int.SInt.from_diff(1n+(1n+Nat.add(ump, u2p)), 1n+d2p),
          add_true_from_diff.pos(ump, u2p, d2p),
          Equal.sym(Int.SInt, Int.SInt.from_diff(1n+(1n+Nat.add(ump, u2p)), 1n+d2p), Int.SInt.from_diff(1n+Nat.add(ump, u2p), d2p), shift_invariant(1n+Nat.add(ump, u2p), d2p))))

def add_true_from_diff(+um: Nat, +u2: Nat, +d2: Nat) -> {Int.SInt.add(Int.SInt{True{}, um}, Int.SInt.from_diff(u2, d2)) == Int.SInt.from_diff(Nat.add(um, u2), d2) : Int.SInt}:
  match um:
    case 0n:
      add_zero_left(u2, d2)
    case 1n+ump:
      add_true_from_diff.pos(ump, u2, d2)

# LEMMA A: adding two from_diff values equals from_diff of the componentwise
# Nat sums. If this holds, general SInt.add associativity follows from it
# plus nat_add_assoc plus the fact that SInt{True,m}==from_diff(m,0n) always
# (canonicalizes SInt.add's non-from_diff branches into from_diff calls).
def from_diff_add(+u1: Nat, +d1: Nat, +u2: Nat, +d2: Nat)
  -> {Int.SInt.add(Int.SInt.from_diff(u1, d1), Int.SInt.from_diff(u2, d2)) == Int.SInt.from_diff(Nat.add(u1, u2), Nat.add(d1, d2)) : Int.SInt}:
  match u1 d1:
    case 0n 0n:
      add_zero_left(u2, d2)
    case 0n 1n+d1p:
      add_false_from_diff(1n+d1p, u2, d2)
    case 1n+u1p 0n:
      add_true_from_diff(1n+u1p, u2, d2)
    case 1n+u1p 1n+d1p:
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.from_diff(1n+u1p, 1n+d1p), Int.SInt.from_diff(u2, d2)), Int.SInt.add(Int.SInt.from_diff(u1p, d1p), Int.SInt.from_diff(u2, d2)), Int.SInt.from_diff(1n+Nat.add(u1p, u2), 1n+Nat.add(d1p, d2)),
        Equal.cong(Int.SInt, Int.SInt, x => Int.SInt.add(x, Int.SInt.from_diff(u2, d2)), Int.SInt.from_diff(1n+u1p, 1n+d1p), Int.SInt.from_diff(u1p, d1p), shift_invariant(u1p, d1p)),
        Equal.trans(Int.SInt, Int.SInt.add(Int.SInt.from_diff(u1p, d1p), Int.SInt.from_diff(u2, d2)), Int.SInt.from_diff(Nat.add(u1p, u2), Nat.add(d1p, d2)), Int.SInt.from_diff(1n+Nat.add(u1p, u2), 1n+Nat.add(d1p, d2)),
          from_diff_add(u1p, d1p, u2, d2),
          Equal.sym(Int.SInt, Int.SInt.from_diff(1n+Nat.add(u1p, u2), 1n+Nat.add(d1p, d2)), Int.SInt.from_diff(Nat.add(u1p, u2), Nat.add(d1p, d2)), shift_invariant(Nat.add(u1p, u2), Nat.add(d1p, d2)))))

# General SInt.add associativity. Falls out directly now: canonicalize every
# operand as from_diff of a (magnitude, 0n) or (0n, magnitude) pair (free,
# since from_diff(X,0n)/from_diff(0n,X) reduce to SInt{True,X}/SInt{False,X}
# for a MANIFEST X -- and a,b,c are already SInt{True,_}/SInt{False,_}
# literals, matched directly, not opaque expressions), then chain
# from_diff_add twice against nat_add_assoc.
# This does NOT go through a general "canonicalize every operand as
# from_diff" step (which was the original plan) -- that needs
# {SInt{False,m} == from_diff(0n,m)}, which is FALSE at m=0n (from_diff
# never produces the non-canonical SInt{False,0n}; SInt.add's own
# False,False branch technically could if both operands already are 0, but
# a clean input never is -- still, a *general* lemma quantified over
# arbitrary m must hold for m=0n too, and this one doesn't). Every one of
# add_zero_left/add_false_from_diff/add_true_from_diff sidesteps this by
# only ever converting a "None,None" TO from_diff, never a "None" alone in
# isolation. So instead: match all three signs directly (8 cases), and in
# each, use whichever of add_true_from_diff/add_false_from_diff/
# sint_add_comm/nat_add_comm/nat_add_assoc applies to the concrete shape
# SInt.add's own definition produces -- never inventing a canonical form
# that doesn't already exist as a proven lemma.
def sint_add_assoc(+a: Int.SInt, +b: Int.SInt, +c: Int.SInt)
  -> {Int.SInt.add(a, Int.SInt.add(b, c)) == Int.SInt.add(Int.SInt.add(a, b), c) : Int.SInt}:
  match a b c:
    case Int.SInt{True{}, am} Int.SInt{True{}, bm} Int.SInt{True{}, cm}:
      %nat_add_assoc(am, bm, cm) : {Int.SInt{True{}, _} == Int.SInt{True{}, Nat.add(Nat.add(am, bm), cm)} : Int.SInt}
      {==}
    case Int.SInt{False{}, am} Int.SInt{False{}, bm} Int.SInt{False{}, cm}:
      %nat_add_assoc(am, bm, cm) : {Int.SInt{False{}, _} == Int.SInt{False{}, Nat.add(Nat.add(am, bm), cm)} : Int.SInt}
      {==}
    case Int.SInt{True{}, am} Int.SInt{True{}, bm} Int.SInt{False{}, cm}:
      add_true_from_diff(am, bm, cm)
    case Int.SInt{False{}, am} Int.SInt{False{}, bm} Int.SInt{True{}, cm}:
      add_false_from_diff(am, cm, bm)
    case Int.SInt{True{}, am} Int.SInt{False{}, bm} Int.SInt{True{}, cm}:
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt{True{}, am}, Int.SInt.from_diff(cm, bm)), Int.SInt.from_diff(Nat.add(am, cm), bm), Int.SInt.add(Int.SInt.from_diff(am, bm), Int.SInt{True{}, cm}),
        add_true_from_diff(am, cm, bm),
        Equal.trans(Int.SInt, Int.SInt.from_diff(Nat.add(am, cm), bm), Int.SInt.from_diff(Nat.add(cm, am), bm), Int.SInt.add(Int.SInt.from_diff(am, bm), Int.SInt{True{}, cm}),
          Equal.cong(Nat, Int.SInt, x => Int.SInt.from_diff(x, bm), Nat.add(am, cm), Nat.add(cm, am), nat_add_comm(am, cm)),
          Equal.trans(Int.SInt, Int.SInt.from_diff(Nat.add(cm, am), bm), Int.SInt.add(Int.SInt{True{}, cm}, Int.SInt.from_diff(am, bm)), Int.SInt.add(Int.SInt.from_diff(am, bm), Int.SInt{True{}, cm}),
            Equal.sym(Int.SInt, Int.SInt.add(Int.SInt{True{}, cm}, Int.SInt.from_diff(am, bm)), Int.SInt.from_diff(Nat.add(cm, am), bm), add_true_from_diff(cm, am, bm)),
            sint_add_comm(Int.SInt{True{}, cm}, Int.SInt.from_diff(am, bm)))))
    case Int.SInt{True{}, am} Int.SInt{False{}, bm} Int.SInt{False{}, cm}:
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt{True{}, am}, Int.SInt{False{}, Nat.add(bm, cm)}), Int.SInt.from_diff(am, Nat.add(bm, cm)), Int.SInt.add(Int.SInt.from_diff(am, bm), Int.SInt{False{}, cm}),
        {==},
        Equal.trans(Int.SInt, Int.SInt.from_diff(am, Nat.add(bm, cm)), Int.SInt.from_diff(am, Nat.add(cm, bm)), Int.SInt.add(Int.SInt.from_diff(am, bm), Int.SInt{False{}, cm}),
          Equal.cong(Nat, Int.SInt, x => Int.SInt.from_diff(am, x), Nat.add(bm, cm), Nat.add(cm, bm), nat_add_comm(bm, cm)),
          Equal.trans(Int.SInt, Int.SInt.from_diff(am, Nat.add(cm, bm)), Int.SInt.add(Int.SInt{False{}, cm}, Int.SInt.from_diff(am, bm)), Int.SInt.add(Int.SInt.from_diff(am, bm), Int.SInt{False{}, cm}),
            Equal.sym(Int.SInt, Int.SInt.add(Int.SInt{False{}, cm}, Int.SInt.from_diff(am, bm)), Int.SInt.from_diff(am, Nat.add(cm, bm)), add_false_from_diff(cm, am, bm)),
            sint_add_comm(Int.SInt{False{}, cm}, Int.SInt.from_diff(am, bm)))))
    case Int.SInt{False{}, am} Int.SInt{True{}, bm} Int.SInt{True{}, cm}:
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt{False{}, am}, Int.SInt{True{}, Nat.add(bm, cm)}), Int.SInt.from_diff(Nat.add(bm, cm), am), Int.SInt.add(Int.SInt.from_diff(bm, am), Int.SInt{True{}, cm}),
        {==},
        Equal.trans(Int.SInt, Int.SInt.from_diff(Nat.add(bm, cm), am), Int.SInt.from_diff(Nat.add(cm, bm), am), Int.SInt.add(Int.SInt.from_diff(bm, am), Int.SInt{True{}, cm}),
          Equal.cong(Nat, Int.SInt, x => Int.SInt.from_diff(x, am), Nat.add(bm, cm), Nat.add(cm, bm), nat_add_comm(bm, cm)),
          Equal.trans(Int.SInt, Int.SInt.from_diff(Nat.add(cm, bm), am), Int.SInt.add(Int.SInt{True{}, cm}, Int.SInt.from_diff(bm, am)), Int.SInt.add(Int.SInt.from_diff(bm, am), Int.SInt{True{}, cm}),
            Equal.sym(Int.SInt, Int.SInt.add(Int.SInt{True{}, cm}, Int.SInt.from_diff(bm, am)), Int.SInt.from_diff(Nat.add(cm, bm), am), add_true_from_diff(cm, bm, am)),
            sint_add_comm(Int.SInt{True{}, cm}, Int.SInt.from_diff(bm, am)))))
    case Int.SInt{False{}, am} Int.SInt{True{}, bm} Int.SInt{False{}, cm}:
      Equal.trans(Int.SInt, Int.SInt.add(Int.SInt{False{}, am}, Int.SInt.from_diff(bm, cm)), Int.SInt.from_diff(bm, Nat.add(am, cm)), Int.SInt.add(Int.SInt.from_diff(bm, am), Int.SInt{False{}, cm}),
        add_false_from_diff(am, bm, cm),
        Equal.trans(Int.SInt, Int.SInt.from_diff(bm, Nat.add(am, cm)), Int.SInt.from_diff(bm, Nat.add(cm, am)), Int.SInt.add(Int.SInt.from_diff(bm, am), Int.SInt{False{}, cm}),
          Equal.cong(Nat, Int.SInt, x => Int.SInt.from_diff(bm, x), Nat.add(am, cm), Nat.add(cm, am), nat_add_comm(am, cm)),
          Equal.trans(Int.SInt, Int.SInt.from_diff(bm, Nat.add(cm, am)), Int.SInt.add(Int.SInt{False{}, cm}, Int.SInt.from_diff(bm, am)), Int.SInt.add(Int.SInt.from_diff(bm, am), Int.SInt{False{}, cm}),
            Equal.sym(Int.SInt, Int.SInt.add(Int.SInt{False{}, cm}, Int.SInt.from_diff(bm, am)), Int.SInt.from_diff(bm, Nat.add(cm, am)), add_false_from_diff(cm, bm, am)),
            sint_add_comm(Int.SInt{False{}, cm}, Int.SInt.from_diff(bm, am)))))
