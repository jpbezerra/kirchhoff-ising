import Ising

open Ising

private def demoLattice : Lattice :=
  { rows := [
      [⟨true⟩, ⟨false⟩, ⟨true⟩],
      [⟨true⟩, ⟨true⟩, ⟨false⟩]
    ] }

#eval demoLattice.magnetization                        -- 2
#eval (demoLattice.flip 0 0).magnetization              -- 0
#eval (demoLattice.flip 0 0).rows.head!.head!.up        -- false
