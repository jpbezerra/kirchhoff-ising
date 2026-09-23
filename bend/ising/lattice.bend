import Base
import ../int.bend as Int

# A spin is +1 (up) or -1 (down), encoded as a Bool.
type Spin is Data:
  Spin{up: Bool}

# A 2D grid of spins, stored row-major.
type Lattice is Data:
  Lattice{rows: +List<+List<Spin>>}

def flip.row(row: +List<Spin>, j: Nat) -> +List<Spin>:
  match row j:
    case Nil{} _:
      Nil{}
    case Spin{u} <> t 0n:
      Spin{Bool.not(u)} <> t
    case h <> t 1n+p:
      h <> flip.row(t, p)

def flip.rows(rows: +List<+List<Spin>>, i: Nat, j: Nat) -> +List<+List<Spin>>:
  match rows i:
    case Nil{} _:
      Nil{}
    case row <> t 0n:
      flip.row(row, j) <> t
    case row <> t 1n+p:
      row <> flip.rows(t, p, j)

# Inverts the spin at (i, j). Out-of-bounds indices leave the lattice unchanged.
def flip(lat: Lattice, i: Nat, j: Nat) -> Lattice:
  match lat:
    case Lattice{rows}:
      Lattice{flip.rows(rows, i, j)}

# A proper Data record (not the generic `&` pair, which is never
# Data-kinded regardless of its components) so equalities about Counts
# type-check in PROOF.bend.
type Count is Data:
  Count{up: Nat, down: Nat}

# Direct structural recursion (not a fold) -- keeps the count-changed-by-one
# reasoning in PROOF.bend a plain induction, no accumulator/associativity
# lemmas needed. bump_up/bump_down/combine take an already-bound Count
# (never a fresh call) since match/let-destructure can't scrutinize a
# computed value directly.
def updown.bump_up(c: Count) -> Count:
  match c:
    case Count{up, down}:
      Count{1n+up, down}

def updown.bump_down(c: Count) -> Count:
  match c:
    case Count{up, down}:
      Count{up, 1n+down}

def updown.row(row: +List<Spin>) -> Count:
  match row:
    case Nil{}:
      Count{0n, 0n}
    case Spin{True{}} <> t:
      updown.bump_up(updown.row(t))
    case Spin{False{}} <> t:
      updown.bump_down(updown.row(t))

def updown.combine(c1: Count, c2: Count) -> Count:
  match c1 c2:
    case Count{up1, down1} Count{up2, down2}:
      Count{Nat.add(up1, up2), Nat.add(down1, down2)}

def updown.rows(rows: +List<+List<Spin>>) -> Count:
  match rows:
    case Nil{}:
      Count{0n, 0n}
    case row <> t:
      updown.combine(updown.row(row), updown.rows(t))

def magnetization.finish(c: Count) -> Int.SInt:
  match c:
    case Count{up, down}:
      Int.SInt.from_diff(up, down)

# Sum of all spins (+1 per up, -1 per down).
def magnetization(lat: Lattice) -> Int.SInt:
  match lat:
    case Lattice{rows}:
      magnetization.finish(updown.rows(rows))

# Row count, for the preserves_lattice_shape law.
def Lattice.row_count(lat: Lattice) -> Nat:
  match lat:
    case Lattice{rows}:
      List.length(&2, +List<Spin>, rows)
