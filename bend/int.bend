import Base

# A signed integer as sign + magnitude (Bend's Base has no built-in Int, only
# Nat and U32). Zero is always SInt{True{}, 0n}.
type SInt is Data:
  SInt{nonneg: Bool, mag: Nat}

def SInt.zero() -> SInt:
  SInt{True{}, 0n}

def SInt.of_nat(n: Nat) -> SInt:
  SInt{True{}, n}

def SInt.neg(a: SInt) -> SInt:
  match a:
    case SInt{True{}, 0n}:
      SInt{True{}, 0n}
    case SInt{True{}, m}:
      SInt{False{}, m}
    case SInt{False{}, m}:
      SInt{True{}, m}

def SInt.show(n: SInt) -> String:
  match n:
    case SInt{True{}, m}:
      Nat.show(m)
    case SInt{False{}, m}:
      "-" ++ Nat.show(m)

# ups - downs, as a signed int.
def SInt.from_diff.cmp(c: Cmp, ups: Nat, downs: Nat) -> SInt:
  match c:
    case LT{}:
      SInt{False{}, Nat.sub(downs, ups)}
    case EQ{}:
      SInt{True{}, 0n}
    case GT{}:
      SInt{True{}, Nat.sub(ups, downs)}

def SInt.from_diff(+ups: Nat, +downs: Nat) -> SInt:
  SInt.from_diff.cmp(Nat.cmp(ups, downs), ups, downs)

def SInt.add(a: SInt, b: SInt) -> SInt:
  match a b:
    case SInt{True{}, am} SInt{True{}, bm}:
      SInt{True{}, Nat.add(am, bm)}
    case SInt{False{}, am} SInt{False{}, bm}:
      SInt{False{}, Nat.add(am, bm)}
    case SInt{True{}, am} SInt{False{}, bm}:
      SInt.from_diff(am, bm)
    case SInt{False{}, am} SInt{True{}, bm}:
      SInt.from_diff(bm, am)
