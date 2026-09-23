import Base
import ../circuit/circuit.bend as C
import ../int.bend as Int

def demo() -> C.Circuit:
  C.Circuit{[
    C.Edge{0n, 1n, Int.SInt.of_nat(3n)},
    C.Edge{1n, 2n, Int.SInt.of_nat(3n)},
    C.Edge{2n, 0n, Int.SInt.of_nat(3n)},
  ]}

def main() -> IO(Unit):
  do IO<Unit>:
    +c : C.Circuit = demo()
    IO.print("balance(0) before: " ++ Int.SInt.show(C.node_balance(0n, c)))
    loop : C.Loop = C.Loop{[0n, 1n, 2n]}
    c2 : C.Circuit = C.add_loop_current(c, loop, Int.SInt.of_nat(5n))
    IO.print("balance(0) after: " ++ Int.SInt.show(C.node_balance(0n, c2)))
