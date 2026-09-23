# Ising -- the laws (Module B: the Ising spin lattice).

import Base
import ./lattice.bend as Ising
import ../int.bend as Int

# LAW: flipping the same cell twice returns the original lattice.
law flip_twice_identity:
  for +lat: Ising.Lattice
  for +i: Nat
  for +j: Nat
  {Ising.flip(Ising.flip(lat, i, j), i, j) == lat : Ising.Lattice}

# LAW: flip never changes the lattice's row count.
law preserves_lattice_shape:
  for +lat: Ising.Lattice
  for +i: Nat
  for +j: Nat
  {Ising.Lattice.row_count(Ising.flip(lat, i, j)) == Ising.Lattice.row_count(lat) : Nat}

# LAW: a single flip changes the magnetization by exactly 0 (out-of-bounds
# i/j, a no-op) or +/-2 (an in-bounds flip).
law flip_changes_magnetization_by_two:
  for +lat: Ising.Lattice
  for +i: Nat
  for +j: Nat
  Or(
    {Ising.magnetization(Ising.flip(lat, i, j)) == Ising.magnetization(lat) : Int.SInt},
    Or(
      {Ising.magnetization(Ising.flip(lat, i, j)) == Int.SInt.add(Ising.magnetization(lat), Int.SInt.of_nat(2n)) : Int.SInt},
      {Ising.magnetization(Ising.flip(lat, i, j)) == Int.SInt.add(Ising.magnetization(lat), Int.SInt.neg(Int.SInt.of_nat(2n))) : Int.SInt}
    )
  )
