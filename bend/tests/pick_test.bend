import Base

def count_down(+n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      Bool.pick(Nat, Nat.is_eq(p, 0n), 99n, count_down(p))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Nat.show(count_down(5n)))
