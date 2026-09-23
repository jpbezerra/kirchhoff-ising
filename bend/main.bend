import Base
import ./ising/lattice.bend as Ising
import ./circuit/circuit.bend as Circuit
import ./int.bend as Int

def demo_lattice() -> Ising.Lattice:
  Ising.Lattice{[
    [Ising.Spin{True{}}, Ising.Spin{False{}}, Ising.Spin{True{}}],
    [Ising.Spin{True{}}, Ising.Spin{True{}}, Ising.Spin{False{}}],
  ]}

def demo_circuit() -> Circuit.Circuit:
  Circuit.Circuit{[
    Circuit.Edge{0n, 1n, Int.SInt.of_nat(3n)},
    Circuit.Edge{1n, 2n, Int.SInt.of_nat(3n)},
    Circuit.Edge{2n, 0n, Int.SInt.of_nat(3n)},
  ]}

def main() -> IO(Unit):
  do IO<Unit>:
    +lat : Ising.Lattice = demo_lattice()
    IO.print("Ising module")
    IO.print("magnetization before flip: " ++ Int.SInt.show(Ising.magnetization(lat)))
    flipped : Ising.Lattice = Ising.flip(lat, 0n, 0n)
    IO.print("magnetization after flip(0,0): " ++ Int.SInt.show(Ising.magnetization(flipped)))
    +c : Circuit.Circuit = demo_circuit()
    IO.print("Circuit module")
    IO.print("balance(0) before mesh current: " ++ Int.SInt.show(Circuit.node_balance(0n, c)))
    loop : Circuit.Loop = Circuit.Loop{[0n, 1n, 2n]}
    c2 : Circuit.Circuit = Circuit.add_loop_current(c, loop, Int.SInt.of_nat(5n))
    IO.print("balance(0) after mesh current: " ++ Int.SInt.show(Circuit.node_balance(0n, c2)))
