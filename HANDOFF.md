# Handoff — Fase 2/3 mostly done, one deep gap left, fully diagnosed

Written 2026-09-22, end of session (second pass on the same day). This
supersedes the previous handoff. Captures exact state, what's proven, what's
not, and every non-obvious Bend/Lean gotcha discovered so far.

## Where things stand

**Fase 0/1 (toolchain, core types): done.**

**Fase 2 (all laws, both modules, both languages): 8 of 10 leis done.**

| Law | Module | Lean | Bend |
| --- | --- | --- | --- |
| `flip_twice_identity` | B (Ising) | done | done |
| `preserves_lattice_shape` | B | done | done |
| `flip_changes_magnetization_by_two` | B | done | **done** (closed this session) |
| `preserves_node_balance` | A (Circuit) | done | **open** (`?TODO`, deeply diagnosed) |
| `loop_current_conserves_total` | A | done | **open** (`?TODO`, deeply diagnosed) |

`lake build` passes clean for the whole Lean project. `bend
bend/ising/PROOF.bend` reports **"All terms check."** — zero `?TODO`s, all 3
Ising laws fully proven. `bend bend/circuit/PROOF.bend` reports "2 TODOs
found" (the two Circuit laws, both blocked on the same missing lemma). `bend
bend/main.bend` runs both modules correctly.

**Fase 3 (benchmark table, PRD §8): done.** `bench/run.sh` is a versioned,
reproducible benchmark script; PRD.md §8 is filled with real numbers from
running it (see `bench/last_run.log` for the raw output of this session's
run). Read PRD.md §8's "Leitura dos números" for the honest interpretation
(Lean ~3x fewer proof LOC, 100% tactic-closed; Bend ~3x more non-proof LOC
mostly from reimplementing a signed-int type Lean gets from core/Mathlib).

## The big story of this session: the Ising magnetization proof got solved

The previous handoff left `flip_changes_magnetization_by_two` open in Bend,
believing it needed general `SInt.add` associativity (same as Circuit). That
belief was **wrong**, and finding out why is the main technical content of
this session:

1. **The real blocker for `diff_inc`/`diff_dec` (single ±2 step lemmas) was
   findable and fixable.** The previous session's "peel invariance" shortcut
   (`from_diff(1n+x,1n+y) == from_diff(x,y)` "for free") was correctly
   identified as false by direct computation — but it turns out to be
   **true**, provable by routing through a helper parameterized by the
   *already-computed* `Nat.cmp` value:
   ```
   def from_diff_cmp_shift(c: Cmp, +x: Nat, +y: Nat)
     -> {SInt.from_diff.cmp(c, 1n+x, 1n+y) == SInt.from_diff.cmp(c, x, y) : SInt}:
     match c: case LT{}: {==}; case EQ{}: {==}; case GT{}: {==}

   def shift_invariant(+x: Nat, +y: Nat) -> {SInt.from_diff(1n+x, 1n+y) == SInt.from_diff(x, y) : SInt}:
     from_diff_cmp_shift(Nat.cmp(x, y), x, y)
   ```
   `match` can't scrutinize the *computed expression* `Nat.cmp(x, y)`
   directly (the long-known gotcha), but it *can* bind a `Cmp` **parameter**
   and case on that — and once bound, all three cases close by pure
   computation (`Nat.sub` also peels a matching `1n+`/`1n+` pair for free).
   This is a genuinely reusable technique: whenever a proof is stuck because
   a `match` can't see through a computed value, check whether routing that
   computed value through an already-evaluated parameter of the relevant
   *result type* (here, `Cmp`) unblocks it.

2. **With `diff_inc`/`diff_dec` in hand, `flip_changes_magnetization_by_two`
   turned out not to need general `SInt.add` associativity at all**, because
   `bend/ising/lattice.bend`'s `magnetization` was *already* restructured
   (last session) to compute via direct `(ups, downs)` recursion
   (`updown.row`/`updown.rows`, now returning a proper `Count` record, not
   `Nat & Nat`) and only calls `SInt.add`/`SInt.from_diff` **once**, at the
   very end. That meant the whole induction over rows/lattice could stay at
   the `Count` level (pure `Nat` successor congruence, zero `SInt`
   reasoning), with `diff_inc`/`diff_dec` applied exactly once at the top to
   convert the final `Count`-level 3-way relation into the `SInt`-level one
   the law needs. See `bend/ising/PROOF.bend`'s `count_rel`/`lift_up`/
   `lift_down`/`row_pair_rel`/`combine_cong_left`/`combine_cong_right`/
   `rows_pair_rel`/`mag_law` for the full chain — built and validated
   incrementally in `bend/tests/ising_mag.bend` before merging in.

3. **Circuit does NOT have this luxury** — `add_loop_current` can touch
   *multiple* edges (not a single flip), each contributing an *arbitrary*
   `delta:SInt` (not a fixed ±2), accumulated via repeated `SInt.add` as the
   edge list is traversed. There's no single final conversion point to defer
   to; the induction genuinely needs to reassociate a growing "delta so far"
   term at every step. This **does** need general `SInt.add` associativity.
   Confirmed this structural difference is real, not a proof-technique gap.

## SInt.add associativity: real progress, still open

Attacked it via: every `SInt.add` reduces to `SInt.from_diff` of the summed
`Nat` components (`from_diff_add`, aka "LEMMA A" in `bend/tests/sint_laws.bend`),
so associativity follows from that lemma plus `Nat.add`'s own associativity
(trivial, `nat_add_assoc` is done). **Proven and reusable, sitting in
`bend/tests/sint_laws.bend`:**

- `nat_add_assoc`, `sint_add_comm` (full `SInt.add` commutativity — done,
  turned out easier than associativity)
- `add_zero_left` (`SInt.add(SInt.zero(), from_diff(u,d)) == from_diff(u,d)`
  for all `u,d`)
- `add_false_from_diff` (`SInt.add(SInt{False,dm}, from_diff(u2,d2)) ==
  from_diff(u2, dm+d2)` for all `dm,u2,d2`)

**Still open:** `add_true_from_diff` (the mirror of `add_false_from_diff`
for the `True` side) and `from_diff_add` itself. The blocker, found and
documented in `sint_laws.bend`'s comment on `add_true_from_diff`: `Nat.cmp(X,
0n)` only reduces for free when `X` is a *manifest* `0n`/`1n+_` (a visible
outer constructor) — for an opaque expression like `Nat.add(um, 0n)` where
`um` is a bare, un-cased function parameter, it's stuck regardless of the
other argument being a literal `0n`. `add_false_from_diff`'s base cases
happened to avoid this (their stuck argument was always already wrapped in a
literal `1n+_`); `add_true_from_diff`'s don't. Fix: an *additional*
case-split on `um` itself, crossed with the existing case split on `u2,d2` —
8 leaf cases instead of 4, each closeable with the same
`shift_invariant`/`nat_add_succ_r`/`nat_add_zero_r` toolkit already proven to
work. This is bounded, mechanical remaining work, not a new unsolved
problem — budget a few more focused hours.

**When this gets picked up**: finish `add_true_from_diff`, then
`from_diff_add`, then `SInt.add` associativity falls out directly (canonicalize
each operand as `from_diff(am,0n)`/`from_diff(0n,dm)` — need `SInt{True,m} ==
from_diff(m,0n)` for all `m`, which should be free by the same `1n+_` visible-
constructor trick, check first), then redo Circuit's `node_balance`/
`node_balance_delta` to use direct recursion (head + rest via `SInt.add`, not
an accumulator fold — mirroring the Ising fix) so the induction has a clean
shape to apply associativity to, then the two Circuit laws.

## Repo layout right now

```
bench/
  run.sh              # versioned benchmark script (PRD §8) -- bash bench/run.sh
  last_run.log        # raw output of this session's run

bend/
  int.bend            # shared signed-int type: SInt{nonneg:Bool, mag:Nat}
  main.bend           # demo for BOTH modules, run with: bend bend/main.bend
  circuit/
    circuit.bend       # + node_balance_delta/node_balance_map (for the laws)
    LAWS.bend           # preserves_node_balance, loop_current_conserves_total
                        #   -- NOT namespaced "Circuit.X" (see gotcha below)
    PROOF.bend          # both laws OPEN (?TODO), root cause fully diagnosed
                        #   in-file and above
  ising/
    lattice.bend        # Spin/Lattice/flip/magnetization + Count record type
                         #   (not Nat & Nat -- equalities need Data-kinded
                         #   types, see gotcha below) + updown.row/rows
    LAWS.bend            # all 3 Module B laws
    PROOF.bend           # ALL 3 LAWS PROVEN. ~470 lines: diff_inc/diff_dec,
                          #   count_rel + lift_up/lift_down + row_pair_rel +
                          #   combine_cong_left/right + rows_pair_rel +
                          #   mag_law, plus the shared Nat.add lemma kit
  tests/
    circuit_check.bend   # scratch/demo, kept per user request
    pick_test.bend       # scratch/demo, kept per user request
    sint_laws.bend        # scratch/exploratory: shift_invariant, diff_inc,
                          #   diff_dec, sint_add_comm, nat_add_assoc,
                          #   add_zero_left, add_false_from_diff (all DONE);
                          #   from_diff_add, add_true_from_diff (OPEN) --
                          #   independently runnable record of the
                          #   associativity investigation
    ising_mag.bend        # scratch/exploratory: the full
                          #   flip_changes_magnetization_by_two derivation,
                          #   built incrementally before merging into
                          #   ising/PROOF.bend -- kept as an independently
                          #   runnable record

lean/
  Circuit.lean        # DONE, compiles
  Ising.lean          # DONE, compiles -- wrapped in `namespace Ising` (was
                       #   bare top-level `Lattice`, collided with Mathlib's
                       #   `Order.Lattice` class)
  Laws.lean            # ALL 5 laws written AND PROVEN, `lake build` passes.
                        #   nodeBalanceDelta (single running Int accumulator,
                        #   not double List.filter) is the tractable
                        #   reformulation that got Circuit's Lean side to
                        #   close -- see the fix history below if extending it
  Tests.lean            # 3 #eval sanity checks, passing
  lakefile.lean, lean-toolchain, lake-manifest.json
```

## Bend gotchas found THIS session (read before writing more Bend proofs)

All of these were root-caused via minimal reproductions against the real
compiler, not guessed — trust them.

1. **A def prefixed with the same name as one of the file's own import
   aliases breaks as soon as that file is imported by another file.**
   `import ./circuit.bend as Circuit` + `def Circuit.foo(...): ...` in the
   *same* file works when run directly, but fails with `expected: a defined
   name, observed: Circuit.foo` (pointing at `foo`'s own
   self-recursive/sibling-calling reference) as soon as a second file does
   `import ./that_file.bend as X`. **Fix: never name your own defs with a
   prefix matching an import alias in the same file.** This is why
   `bend/circuit/LAWS.bend`'s `is_circulation`/`all_circulations` aren't
   prefixed `Circuit.`.

2. **Forward references break, even for non-self-recursive helpers.** A
   helper function defined *textually before* another function it calls
   fails with the same confusing `expected: a defined name, observed: <the
   later fn>` error — even when neither function is self-recursive and
   there's no import involved at all. `lift_up`/`lift_down` must be defined
   *before* `row_pair_rel.true_cons`/`.false_cons`, which call them. This
   cost real time in `bend/tests/ising_mag.bend` (see its own scratch
   history) before being isolated with a minimal same-file repro — always
   check def ordering first when this exact error appears, before suspecting
   anything about imports or self-recursion.

3. **`Nat & Nat` (bare `&` pair sugar) cannot be used as the type argument
   of an equality `{a == b : T}`.** Pairs via `&` are *always* `Kind(&1)`
   (`Type`), never `Data`, regardless of their components' kind (this was
   already known from an earlier session re: `+List`) — but equalities
   specifically need a `Data`-kinded `T`. Fails with `expected: Data,
   observed: Type`. **Fix: define a proper `type Foo is Data: Foo{a:A,
   b:B}` record** wherever you need to state equalities about a pair-like
   value — this is why `Ising.Count` exists now (`updown.row`/`.rows`
   return it, not `Nat & Nat`).

4. **`Nat.cmp`/`Nat.sub` peel a matching `1n+`/`1n+` pair on *both*
   arguments for free (even for fully symbolic values) — but a *single*
   `1n+_`-wrapped argument against an opaque unwrapped one does NOT let
   `Nat.cmp` resolve**, even when the wrapped side would obviously decide
   the comparison on its own (e.g. `Nat.cmp(1n+X, Y)` for `Y` some opaque
   unwrapped expression is stuck, full stop, regardless of what `X` is).
   Concretely: `SInt.from_diff(X, 0n)` only reduces to `SInt{True, X}` for
   free when `X` is *manifestly* `0n` or `1n+something` — not for an opaque
   expression like `Nat.add(um, 0n)` where `um` is a bare, un-cased
   parameter, even though the *second* argument is the literal `0n`. This
   is the exact blocker `add_true_from_diff` hit (see above) — the fix is
   always an *additional* case-split on whatever variable is hiding inside
   the opaque expression.

5. **The `match`-can't-scrutinize-a-computed-expression restriction has a
   systematic workaround: route the computed value through a fresh
   parameter of a helper function, case on the parameter there.** This was
   known already for simple cases (factor `Nat.cmp(a,b)` into its own
   `.go` helper taking the `Cmp` as a parameter). This session confirmed
   it generalizes cleanly to *proof* obligations too (`from_diff_cmp_shift`
   above) — the technique isn't just for computing values, it unblocks
   otherwise-stuck equational reasoning the same way.

6. **Existentials (`Exists(A, x => B(x))` from Base) work fine as ordinary
   `Type`-valued expressions outside `law` blocks**, not just via the `exs`
   sugar the GUIDE shows inside laws — used throughout `count_rel` in
   `ising/PROOF.bend`. Construct a witness with `(value, proof)`, same as a
   plain pair.

## Bend gotchas from prior sessions (still true)

- `match`/let-destructure can't scrutinize a computed expression or an
  already-consumed/reused binder (`(a, b) = some_call(...)` fails the same
  way as `match some_call(...):`) — factor through a helper taking the
  value as an already-bound parameter.
- Mutual recursion is completely disallowed.
- `+List<T>` requires `T` to be `Data`-kinded.
- Any local variable of a `Data`-kinded type (includes `Nat`, `Bool`, `SInt`,
  not just lists/records) used more than once needs `+`.
- Boolean/constructor literals inside a nested pattern need explicit `{}`.
- Imports need `as Alias`; everything from an imported module must be
  qualified.
- `bend`'s IO-effect imports resolve relative to CWD — always invoke via the
  `bend`/`bend.ps1` shims.
- `%e : P` rewrites *backward*: for `e : {a == b : T}`, `P` is the current
  goal with `_` marking the (sub)term equal to `b`; the new goal is `P` with
  that `_` filled by `a`. Get this backward and you get a confusing
  "expected/observed" mismatch — it happened repeatedly again this session,
  always fixable by swapping which side gets the `_` (or wrapping the lemma
  in `Equal.sym` first if the "wrong" side is the one that's occurring).
- `%rewrite` needs its target's type already concrete — doesn't work inline
  on a *live self-recursive call*. Use the `.cons`/`.succ`/`.zero`-suffixed
  helper-taking-`rec`-as-a-parameter pattern from `proof_insertion_sort`.

## Environment / tooling notes (unchanged)

- `bend2-src` at `C:\Users\jplim\Documents\Programação\bend2-src`.
- `bend`/`bend.ps1` shims and `elan`/`lake`/`lean` on PATH persistently.
- A `lake build Laws` incremental run (Mathlib already built) took
  182s/70s/15s across 3 runs this session (see `bench/last_run.log`) — the
  first pays some Lake cache-recompilation cost, the third is the
  representative "check one file's change" number.
- Windows short path for `Programação`: `C:\Users\jplim\DOCUME~1\PROGRA~1`.

## What's left, in order

1. **Finish `add_true_from_diff`** in `bend/tests/sint_laws.bend` (8 leaf
   cases, case-split on `um` crossed with `u2/d2` — see its own comment for
   the exact plan). Then `from_diff_add`. Then general `SInt.add`
   associativity falls out (see "When this gets picked up" above).
2. **Restructure `Circuit`'s `node_balance`/`node_balance_delta`** from
   accumulator-fold to direct head+rest recursion (mirroring the Ising fix),
   then close `preserves_node_balance`/`loop_current_conserves_total` using
   the new associativity lemma.
3. Optional/Fase 4 (PRD §9): CPU parallelism speedup measurement for a
   `sweep` operation (not implemented at all this session — would be new
   scope, not a completion of existing work). No GPU available (PRD §10).
4. Once the above is resolved (or explicitly deferred further), a git
   commit is warranted — nothing has been committed yet this project.
   Confirm with the user before committing/pushing.

## User's standing preferences (from memory, already saved)

- **Never stop to ask clarifying questions during implementation** — pick a
  reasonable default, note the deviation in prose, keep going.
- **Keep Bend scratch/test files in `bend/tests/`** rather than deleting
  them — the user asked for this explicitly, twice now (once for
  `circuit_check.bend`/`pick_test.bend`, reaffirmed implicitly by never
  objecting to `sint_laws.bend`/`ising_mag.bend` being added there this
  session). Default going forward: any exploratory `.bend` proof work stays
  in `bend/tests/`, not deleted after merging into the real `PROOF.bend`.
