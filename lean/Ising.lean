namespace Ising

/-- A spin is +1 (up) or -1 (down), encoded as a `Bool`. -/
structure Spin where
  up : Bool
deriving Repr, DecidableEq, Inhabited

/-- A 2D grid of spins, stored row-major. -/
structure Lattice where
  rows : List (List Spin)
deriving Repr

def flipRow : List Spin → Nat → List Spin
  | [], _ => []
  | s :: t, 0 => { s with up := !s.up } :: t
  | s :: t, n + 1 => s :: flipRow t n

def flipRows : List (List Spin) → Nat → Nat → List (List Spin)
  | [], _, _ => []
  | r :: t, 0, j => flipRow r j :: t
  | r :: t, i + 1, j => r :: flipRows t i j

/-- Inverts the spin at (i, j). Out-of-bounds indices leave the lattice unchanged. -/
def Lattice.flip (lat : Lattice) (i j : Nat) : Lattice :=
  { lat with rows := flipRows lat.rows i j }

def spinValue (s : Spin) : Int :=
  if s.up then 1 else -1

/-- Sum of all spins (+1 per up, -1 per down). -/
def Lattice.magnetization (lat : Lattice) : Int :=
  (lat.rows.map (fun row => (row.map spinValue).sum)).sum

end Ising
