# Scratch/exploratory proof of flip_changes_magnetization_by_two, built up
# incrementally against the real compiler before being merged into
# bend/ising/PROOF.bend (the real, in-use copy). Kept as a standalone,
# independently checkable record -- also documents the "forward reference
# breaks a Type-valued def" gotcha found while building this (see
# row_pair_rel.true_cons's position relative to lift_up below). Run with
# `bend bend/tests/ising_mag.bend`.

import Base
import ../ising/lattice.bend as Ising
import ../int.bend as Int

# Relation between an (ups,downs) Count before/after a single flip inside a
# row/lattice: either unchanged, or there's a shared "core" Count such that
# before = bump_up(core), after = bump_down(core) (one spin went up->down),
# or the symmetric case. Phrased via equality-to-a-reconstructed-Count
# (never destructuring p1/p2 themselves) because updown.row(t) for an
# abstract list t never reduces to a literal Count -- any destructure of it
# (match or let-pair) gets stuck.
def count_rel(p1: Ising.Count, p2: Ising.Count) -> Type:
  Or(
    {p1 == p2 : Ising.Count},
    Or(
      Exists(Ising.Count, core => ({p1 == Ising.updown.bump_up(core) : Ising.Count} & {p2 == Ising.updown.bump_down(core) : Ising.Count})),
      Exists(Ising.Count, core => ({p1 == Ising.updown.bump_down(core) : Ising.Count} & {p2 == Ising.updown.bump_up(core) : Ising.Count}))
    )
  )

def bump_commute(+core: Ising.Count) -> {Ising.updown.bump_up(Ising.updown.bump_down(core)) == Ising.updown.bump_down(Ising.updown.bump_up(core)) : Ising.Count}:
  match core:
    case Ising.Count{u, d}:
      {==}

def lift_up(+P: Ising.Count, +Q: Ising.Count, rec: count_rel(P, Q)) -> count_rel(Ising.updown.bump_up(P), Ising.updown.bump_up(Q)):
  match rec:
    case Inl{e}:
      Inl{Equal.cong(Ising.Count, Ising.Count, Ising.updown.bump_up, P, Q, e)}
    case Inr{Inl{w}}:
      (+core, ew) = w
      (e1, e2) = ew
      Inr{Inl{(Ising.updown.bump_up(core), (
        Equal.cong(Ising.Count, Ising.Count, Ising.updown.bump_up, P, Ising.updown.bump_up(core), e1),
        Equal.trans(Ising.Count, Ising.updown.bump_up(Q), Ising.updown.bump_up(Ising.updown.bump_down(core)), Ising.updown.bump_down(Ising.updown.bump_up(core)),
          Equal.cong(Ising.Count, Ising.Count, Ising.updown.bump_up, Q, Ising.updown.bump_down(core), e2),
          bump_commute(core))
      ))}}
    case Inr{Inr{w}}:
      (+core, ew) = w
      (e1, e2) = ew
      Inr{Inr{(Ising.updown.bump_up(core), (
        Equal.trans(Ising.Count, Ising.updown.bump_up(P), Ising.updown.bump_up(Ising.updown.bump_down(core)), Ising.updown.bump_down(Ising.updown.bump_up(core)),
          Equal.cong(Ising.Count, Ising.Count, Ising.updown.bump_up, P, Ising.updown.bump_down(core), e1),
          bump_commute(core)),
        Equal.cong(Ising.Count, Ising.Count, Ising.updown.bump_up, Q, Ising.updown.bump_up(core), e2)
      ))}}

def lift_down(+P: Ising.Count, +Q: Ising.Count, rec: count_rel(P, Q)) -> count_rel(Ising.updown.bump_down(P), Ising.updown.bump_down(Q)):
  match rec:
    case Inl{e}:
      Inl{Equal.cong(Ising.Count, Ising.Count, Ising.updown.bump_down, P, Q, e)}
    case Inr{Inl{w}}:
      (+core, ew) = w
      (e1, e2) = ew
      Inr{Inl{(Ising.updown.bump_down(core), (
        Equal.trans(Ising.Count, Ising.updown.bump_down(P), Ising.updown.bump_down(Ising.updown.bump_up(core)), Ising.updown.bump_up(Ising.updown.bump_down(core)),
          Equal.cong(Ising.Count, Ising.Count, Ising.updown.bump_down, P, Ising.updown.bump_up(core), e1),
          Equal.sym(Ising.Count, Ising.updown.bump_up(Ising.updown.bump_down(core)), Ising.updown.bump_down(Ising.updown.bump_up(core)), bump_commute(core))),
        Equal.cong(Ising.Count, Ising.Count, Ising.updown.bump_down, Q, Ising.updown.bump_down(core), e2)
      ))}}
    case Inr{Inr{w}}:
      (+core, ew) = w
      (e1, e2) = ew
      Inr{Inr{(Ising.updown.bump_down(core), (
        Equal.cong(Ising.Count, Ising.Count, Ising.updown.bump_down, P, Ising.updown.bump_down(core), e1),
        Equal.trans(Ising.Count, Ising.updown.bump_down(Q), Ising.updown.bump_down(Ising.updown.bump_up(core)), Ising.updown.bump_up(Ising.updown.bump_down(core)),
          Equal.cong(Ising.Count, Ising.Count, Ising.updown.bump_down, Q, Ising.updown.bump_up(core), e2),
          Equal.sym(Ising.Count, Ising.updown.bump_up(Ising.updown.bump_down(core)), Ising.updown.bump_down(Ising.updown.bump_up(core)), bump_commute(core)))
      ))}}

def row_pair_rel.true_cons(+t: +List<Ising.Spin>, +p: Nat, rec: count_rel(Ising.updown.row(t), Ising.updown.row(Ising.flip.row(t, p))))
  -> count_rel(Ising.updown.bump_up(Ising.updown.row(t)), Ising.updown.bump_up(Ising.updown.row(Ising.flip.row(t, p)))):
  lift_up(Ising.updown.row(t), Ising.updown.row(Ising.flip.row(t, p)), rec)

def row_pair_rel.false_cons(+t: +List<Ising.Spin>, +p: Nat, rec: count_rel(Ising.updown.row(t), Ising.updown.row(Ising.flip.row(t, p))))
  -> count_rel(Ising.updown.bump_down(Ising.updown.row(t)), Ising.updown.bump_down(Ising.updown.row(Ising.flip.row(t, p)))):
  lift_down(Ising.updown.row(t), Ising.updown.row(Ising.flip.row(t, p)), rec)

def row_pair_rel(+row: +List<Ising.Spin>, +j: Nat) -> count_rel(Ising.updown.row(row), Ising.updown.row(Ising.flip.row(row, j))):
  match row j:
    case Nil{} _:
      Inl{{==}}
    case Ising.Spin{True{}} <> t 0n:
      Inr{Inl{(Ising.updown.row(t), ({==}, {==}))}}
    case Ising.Spin{False{}} <> t 0n:
      Inr{Inr{(Ising.updown.row(t), ({==}, {==}))}}
    case Ising.Spin{True{}} <> t 1n+p:
      row_pair_rel.true_cons(t, p, row_pair_rel(t, p))
    case Ising.Spin{False{}} <> t 1n+p:
      row_pair_rel.false_cons(t, p, row_pair_rel(t, p))

def main() -> Nat:
  0n

def combine_bump_up_left(+core: Ising.Count, +R: Ising.Count) -> {Ising.updown.combine(Ising.updown.bump_up(core), R) == Ising.updown.bump_up(Ising.updown.combine(core, R)) : Ising.Count}:
  match core R:
    case Ising.Count{cu, cd} Ising.Count{ru, rd}:
      {==}

def combine_bump_down_left(+core: Ising.Count, +R: Ising.Count) -> {Ising.updown.combine(Ising.updown.bump_down(core), R) == Ising.updown.bump_down(Ising.updown.combine(core, R)) : Ising.Count}:
  match core R:
    case Ising.Count{cu, cd} Ising.Count{ru, rd}:
      {==}

def combine_cong_left(+R: Ising.Count, +P: Ising.Count, +Q: Ising.Count, rec: count_rel(P, Q))
  -> count_rel(Ising.updown.combine(P, R), Ising.updown.combine(Q, R)):
  match rec:
    case Inl{e}:
      Inl{Equal.cong(Ising.Count, Ising.Count, p => Ising.updown.combine(p, R), P, Q, e)}
    case Inr{Inl{w}}:
      (+core, ew) = w
      (e1, e2) = ew
      Inr{Inl{(Ising.updown.combine(core, R), (
        Equal.trans(Ising.Count, Ising.updown.combine(P, R), Ising.updown.combine(Ising.updown.bump_up(core), R), Ising.updown.bump_up(Ising.updown.combine(core, R)),
          Equal.cong(Ising.Count, Ising.Count, p => Ising.updown.combine(p, R), P, Ising.updown.bump_up(core), e1),
          combine_bump_up_left(core, R)),
        Equal.trans(Ising.Count, Ising.updown.combine(Q, R), Ising.updown.combine(Ising.updown.bump_down(core), R), Ising.updown.bump_down(Ising.updown.combine(core, R)),
          Equal.cong(Ising.Count, Ising.Count, p => Ising.updown.combine(p, R), Q, Ising.updown.bump_down(core), e2),
          combine_bump_down_left(core, R))
      ))}}
    case Inr{Inr{w}}:
      (+core, ew) = w
      (e1, e2) = ew
      Inr{Inr{(Ising.updown.combine(core, R), (
        Equal.trans(Ising.Count, Ising.updown.combine(P, R), Ising.updown.combine(Ising.updown.bump_down(core), R), Ising.updown.bump_down(Ising.updown.combine(core, R)),
          Equal.cong(Ising.Count, Ising.Count, p => Ising.updown.combine(p, R), P, Ising.updown.bump_down(core), e1),
          combine_bump_down_left(core, R)),
        Equal.trans(Ising.Count, Ising.updown.combine(Q, R), Ising.updown.combine(Ising.updown.bump_up(core), R), Ising.updown.bump_up(Ising.updown.combine(core, R)),
          Equal.cong(Ising.Count, Ising.Count, p => Ising.updown.combine(p, R), Q, Ising.updown.bump_up(core), e2),
          combine_bump_up_left(core, R))
      ))}}

# Nat.add facts (already proven this way in ising/PROOF.bend; duplicated
# here for this standalone scratch file).
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

def combine_bump_up_right(+core: Ising.Count, +R: Ising.Count) -> {Ising.updown.combine(R, Ising.updown.bump_up(core)) == Ising.updown.bump_up(Ising.updown.combine(R, core)) : Ising.Count}:
  match core R:
    case Ising.Count{cu, cd} Ising.Count{ru, rd}:
      %nat_add_succ_r(ru, cu) : {Ising.Count{Nat.add(ru, 1n+cu), Nat.add(rd, cd)} == Ising.Count{_, Nat.add(rd, cd)} : Ising.Count}
      {==}

def combine_bump_down_right(+core: Ising.Count, +R: Ising.Count) -> {Ising.updown.combine(R, Ising.updown.bump_down(core)) == Ising.updown.bump_down(Ising.updown.combine(R, core)) : Ising.Count}:
  match core R:
    case Ising.Count{cu, cd} Ising.Count{ru, rd}:
      %nat_add_succ_r(rd, cd) : {Ising.Count{Nat.add(ru, cu), Nat.add(rd, 1n+cd)} == Ising.Count{Nat.add(ru, cu), _} : Ising.Count}
      {==}

def combine_cong_right(+R: Ising.Count, +P: Ising.Count, +Q: Ising.Count, rec: count_rel(P, Q))
  -> count_rel(Ising.updown.combine(R, P), Ising.updown.combine(R, Q)):
  match rec:
    case Inl{e}:
      Inl{Equal.cong(Ising.Count, Ising.Count, p => Ising.updown.combine(R, p), P, Q, e)}
    case Inr{Inl{w}}:
      (+core, ew) = w
      (e1, e2) = ew
      Inr{Inl{(Ising.updown.combine(R, core), (
        Equal.trans(Ising.Count, Ising.updown.combine(R, P), Ising.updown.combine(R, Ising.updown.bump_up(core)), Ising.updown.bump_up(Ising.updown.combine(R, core)),
          Equal.cong(Ising.Count, Ising.Count, p => Ising.updown.combine(R, p), P, Ising.updown.bump_up(core), e1),
          combine_bump_up_right(core, R)),
        Equal.trans(Ising.Count, Ising.updown.combine(R, Q), Ising.updown.combine(R, Ising.updown.bump_down(core)), Ising.updown.bump_down(Ising.updown.combine(R, core)),
          Equal.cong(Ising.Count, Ising.Count, p => Ising.updown.combine(R, p), Q, Ising.updown.bump_down(core), e2),
          combine_bump_down_right(core, R))
      ))}}
    case Inr{Inr{w}}:
      (+core, ew) = w
      (e1, e2) = ew
      Inr{Inr{(Ising.updown.combine(R, core), (
        Equal.trans(Ising.Count, Ising.updown.combine(R, P), Ising.updown.combine(R, Ising.updown.bump_down(core)), Ising.updown.bump_down(Ising.updown.combine(R, core)),
          Equal.cong(Ising.Count, Ising.Count, p => Ising.updown.combine(R, p), P, Ising.updown.bump_down(core), e1),
          combine_bump_down_right(core, R)),
        Equal.trans(Ising.Count, Ising.updown.combine(R, Q), Ising.updown.combine(R, Ising.updown.bump_up(core)), Ising.updown.bump_up(Ising.updown.combine(R, core)),
          Equal.cong(Ising.Count, Ising.Count, p => Ising.updown.combine(R, p), Q, Ising.updown.bump_up(core), e2),
          combine_bump_up_right(core, R))
      ))}}

def rows_pair_rel.zero(+row: +List<Ising.Spin>, +j: Nat, +t: +List<+List<Ising.Spin>>, rec: count_rel(Ising.updown.row(row), Ising.updown.row(Ising.flip.row(row, j))))
  -> count_rel(Ising.updown.rows(row <> t), Ising.updown.rows(Ising.flip.rows(row <> t, 0n, j))):
  combine_cong_left(Ising.updown.rows(t), Ising.updown.row(row), Ising.updown.row(Ising.flip.row(row, j)), rec)

def rows_pair_rel.succ(+row: +List<Ising.Spin>, +t: +List<+List<Ising.Spin>>, +p: Nat, +j: Nat, rec: count_rel(Ising.updown.rows(t), Ising.updown.rows(Ising.flip.rows(t, p, j))))
  -> count_rel(Ising.updown.rows(row <> t), Ising.updown.rows(Ising.flip.rows(row <> t, 1n+p, j))):
  combine_cong_right(Ising.updown.row(row), Ising.updown.rows(t), Ising.updown.rows(Ising.flip.rows(t, p, j)), rec)

def rows_pair_rel(+rows: +List<+List<Ising.Spin>>, +i: Nat, +j: Nat) -> count_rel(Ising.updown.rows(rows), Ising.updown.rows(Ising.flip.rows(rows, i, j))):
  match rows i:
    case Nil{} _:
      Inl{{==}}
    case row <> t 0n:
      rows_pair_rel.zero(row, j, t, row_pair_rel(row, j))
    case row <> t 1n+p:
      rows_pair_rel.succ(row, t, p, j, rows_pair_rel(t, p, j))

# SInt.from_diff facts (mirrors sint_laws.bend, duplicated here for this
# standalone scratch file -- see sint_laws.bend for the full derivation
# notes on shift_invariant/diff_inc/diff_dec).

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

def nat_add_one_r(+n: Nat) -> {Nat.add(n, 1n) == 1n+n : Nat}:
  %nat_add_comm(n, 1n) : {Nat.add(n, 1n) == _ : Nat}
  {==}

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

# Final conversion: count_rel at the Count level implies the 3-way SInt
# disjunction, via diff_inc/diff_dec applied once at the leaf.

def mag_unchanged(+C1: Ising.Count, +C2: Ising.Count, e: {C1 == C2 : Ising.Count})
  -> {Ising.magnetization.finish(C2) == Ising.magnetization.finish(C1) : Int.SInt}:
  Equal.cong(Ising.Count, Int.SInt, Ising.magnetization.finish, C2, C1, Equal.sym(Ising.Count, C1, C2, e))

def mag_inc_case(+cu: Nat, +cd: Nat, +C1: Ising.Count, +C2: Ising.Count,
  e1: {C1 == Ising.updown.bump_down(Ising.Count{cu, cd}) : Ising.Count}, e2: {C2 == Ising.updown.bump_up(Ising.Count{cu, cd}) : Ising.Count})
  -> {Ising.magnetization.finish(C2) == Int.SInt.add(Ising.magnetization.finish(C1), Int.SInt{True{}, 2n}) : Int.SInt}:
  Equal.trans(Int.SInt, Ising.magnetization.finish(C2), Ising.magnetization.finish(Ising.updown.bump_up(Ising.Count{cu, cd})), Int.SInt.add(Ising.magnetization.finish(C1), Int.SInt{True{}, 2n}),
    Equal.cong(Ising.Count, Int.SInt, Ising.magnetization.finish, C2, Ising.updown.bump_up(Ising.Count{cu, cd}), e2),
    Equal.trans(Int.SInt, Int.SInt.from_diff(1n+cu, cd), Int.SInt.add(Int.SInt.from_diff(cu, 1n+cd), Int.SInt{True{}, 2n}), Int.SInt.add(Ising.magnetization.finish(C1), Int.SInt{True{}, 2n}),
      diff_inc(cu, cd),
      Equal.cong(Ising.Count, Int.SInt, c => Int.SInt.add(Ising.magnetization.finish(c), Int.SInt{True{}, 2n}), Ising.updown.bump_down(Ising.Count{cu, cd}), C1, Equal.sym(Ising.Count, C1, Ising.updown.bump_down(Ising.Count{cu, cd}), e1))))

def mag_dec_case(+cu: Nat, +cd: Nat, +C1: Ising.Count, +C2: Ising.Count,
  e1: {C1 == Ising.updown.bump_up(Ising.Count{cu, cd}) : Ising.Count}, e2: {C2 == Ising.updown.bump_down(Ising.Count{cu, cd}) : Ising.Count})
  -> {Ising.magnetization.finish(C2) == Int.SInt.add(Ising.magnetization.finish(C1), Int.SInt{False{}, 2n}) : Int.SInt}:
  Equal.trans(Int.SInt, Ising.magnetization.finish(C2), Ising.magnetization.finish(Ising.updown.bump_down(Ising.Count{cu, cd})), Int.SInt.add(Ising.magnetization.finish(C1), Int.SInt{False{}, 2n}),
    Equal.cong(Ising.Count, Int.SInt, Ising.magnetization.finish, C2, Ising.updown.bump_down(Ising.Count{cu, cd}), e2),
    Equal.trans(Int.SInt, Int.SInt.from_diff(cu, 1n+cd), Int.SInt.add(Int.SInt.from_diff(1n+cu, cd), Int.SInt{False{}, 2n}), Int.SInt.add(Ising.magnetization.finish(C1), Int.SInt{False{}, 2n}),
      diff_dec(cu, cd),
      Equal.cong(Ising.Count, Int.SInt, c => Int.SInt.add(Ising.magnetization.finish(c), Int.SInt{False{}, 2n}), Ising.updown.bump_up(Ising.Count{cu, cd}), C1, Equal.sym(Ising.Count, C1, Ising.updown.bump_up(Ising.Count{cu, cd}), e1))))

def mag_inc_case_core(+core: Ising.Count, +C1: Ising.Count, +C2: Ising.Count,
  e1: {C1 == Ising.updown.bump_down(core) : Ising.Count}, e2: {C2 == Ising.updown.bump_up(core) : Ising.Count})
  -> {Ising.magnetization.finish(C2) == Int.SInt.add(Ising.magnetization.finish(C1), Int.SInt{True{}, 2n}) : Int.SInt}:
  match core:
    case Ising.Count{cu, cd}:
      mag_inc_case(cu, cd, C1, C2, e1, e2)

def mag_dec_case_core(+core: Ising.Count, +C1: Ising.Count, +C2: Ising.Count,
  e1: {C1 == Ising.updown.bump_up(core) : Ising.Count}, e2: {C2 == Ising.updown.bump_down(core) : Ising.Count})
  -> {Ising.magnetization.finish(C2) == Int.SInt.add(Ising.magnetization.finish(C1), Int.SInt{False{}, 2n}) : Int.SInt}:
  match core:
    case Ising.Count{cu, cd}:
      mag_dec_case(cu, cd, C1, C2, e1, e2)

def mag_law.finish(+C1: Ising.Count, +C2: Ising.Count, rec: count_rel(C1, C2)) ->
  Or(
    {Ising.magnetization.finish(C2) == Ising.magnetization.finish(C1) : Int.SInt},
    Or(
      {Ising.magnetization.finish(C2) == Int.SInt.add(Ising.magnetization.finish(C1), Int.SInt{True{}, 2n}) : Int.SInt},
      {Ising.magnetization.finish(C2) == Int.SInt.add(Ising.magnetization.finish(C1), Int.SInt{False{}, 2n}) : Int.SInt}
    )
  ):
  match rec:
    case Inl{e}:
      Inl{mag_unchanged(C1, C2, e)}
    case Inr{Inl{w}}:
      (+core, ew) = w
      (e1, e2) = ew
      Inr{Inr{mag_dec_case_core(core, C1, C2, e1, e2)}}
    case Inr{Inr{w}}:
      (+core, ew) = w
      (e1, e2) = ew
      Inr{Inl{mag_inc_case_core(core, C1, C2, e1, e2)}}

def mag_law(+lat: Ising.Lattice, +i: Nat, +j: Nat) ->
  Or(
    {Ising.magnetization(Ising.flip(lat, i, j)) == Ising.magnetization(lat) : Int.SInt},
    Or(
      {Ising.magnetization(Ising.flip(lat, i, j)) == Int.SInt.add(Ising.magnetization(lat), Int.SInt.of_nat(2n)) : Int.SInt},
      {Ising.magnetization(Ising.flip(lat, i, j)) == Int.SInt.add(Ising.magnetization(lat), Int.SInt.neg(Int.SInt.of_nat(2n))) : Int.SInt}
    )
  ):
  match lat:
    case Ising.Lattice{rows}:
      mag_law.finish(Ising.updown.rows(rows), Ising.updown.rows(Ising.flip.rows(rows, i, j)), rows_pair_rel(rows, i, j))
