import Circuit
import Ising
import Mathlib.Tactic

open Ising

/-!
Laws for both the Circuit and Ising modules. Human-authored claims; proofs live below
(this repo doesn't split LAWS/PROOF the way the Bend side does, since Lean has no
equivalent convention -- theorem statement and proof sit together).
-/

/-! ### Module A: Circuit -/

/-- Edges of `c` that belong to `loop`. -/
def Circuit.loopEdges (c : Circuit) (loop : Loop) : List Edge :=
  c.edges.filter (isLoopEdge loop)

/-- How much a mesh current of +1 around `loop` would shift `n`'s node balance, summed
    edge by edge: +1 per loop edge entering `n`, -1 per loop edge leaving it. A single
    running `Int` accumulator (instead of two separate `List.filter/.length` counts)
    keeps the induction below a plain `split_ifs`/`ring` argument, with no simp lemmas
    about `filter` needed. -/
def nodeBalanceDelta (es : List Edge) (loop : Loop) (n : Nat) : Int :=
  match es with
  | [] => 0
  | e :: es =>
      (if isLoopEdge loop e then
        (if e.to_ = n then 1 else 0) - (if e.from_ = n then 1 else 0)
      else 0) + nodeBalanceDelta es loop n

/-- `loop` is a genuine closed walk in `c`, at node `n`: a +1 mesh current around it
    would shift `n`'s balance by exactly 0. This is the standard graph-theory
    "circulation" condition -- the precise sense in which a mesh/loop current can be
    added to a circuit without breaking Kirchhoff's Current Law. A loop that isn't
    actually closed within the circuit (e.g. names a node pair with no matching edge)
    is not required to preserve balance, which is physically correct: you cannot run a
    mesh current around a path that doesn't exist. -/
def Circuit.IsCirculation (c : Circuit) (loop : Loop) (n : Nat) : Prop :=
  nodeBalanceDelta c.edges loop n = 0

/-- One unfolding step of `nodeBalanceDelta`, as a targeted rewrite: `rw` with this only
    fires where the list is a literal `e :: es`, unlike `unfold`/`simp [nodeBalanceDelta]`,
    which also re-expand the *already-reduced* `nodeBalanceDelta es loop n` left behind by
    the induction hypothesis -- that re-expansion is what produced the unreadable nested
    `match` goals in earlier attempts here. -/
private theorem nodeBalanceDelta_nil (loop : Loop) (n : Nat) : nodeBalanceDelta [] loop n = 0 := rfl

private theorem nodeBalanceDelta_cons (e : Edge) (es : List Edge) (loop : Loop) (n : Nat) :
    nodeBalanceDelta (e :: es) loop n
      = (if isLoopEdge loop e then (if e.to_ = n then 1 else 0) - (if e.from_ = n then 1 else 0) else 0)
        + nodeBalanceDelta es loop n := rfl

private theorem nodeBalance_map_update (es : List Edge) (loop : Loop) (delta : Int) (n : Nat) :
    (((es.map (fun e => if isLoopEdge loop e then { e with current := e.current + delta } else e)).map (edgeContribution n)).sum : Int)
    = (es.map (edgeContribution n)).sum + delta * nodeBalanceDelta es loop n := by
  induction es with
  | nil => simp [nodeBalanceDelta_nil]
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, nodeBalanceDelta_cons, edgeContribution]
    rw [ih]
    split_ifs <;> simp_all <;> ring

theorem preserves_node_balance (c : Circuit) (loop : Loop) (delta : Int) (n : Nat)
    (h : c.IsCirculation loop n) :
    (c.addLoopCurrent loop delta).nodeBalance n = c.nodeBalance n := by
  unfold Circuit.addLoopCurrent Circuit.nodeBalance
  rw [nodeBalance_map_update]
  unfold Circuit.IsCirculation at h
  rw [h]
  ring

/-- Summing `nodeBalance` over any fixed list of nodes is likewise unaffected, as long
    as the loop is a circulation at each of them -- an easy corollary of
    `preserves_node_balance`, not a new global-sum law (Module A's laws are about a
    *local* invariant, per §1; this is just that local invariant summed pointwise). -/
theorem loop_current_conserves_total (c : Circuit) (loop : Loop) (delta : Int) (ns : List Nat)
    (h : ∀ n ∈ ns, c.IsCirculation loop n) :
    (ns.map (c.addLoopCurrent loop delta).nodeBalance).sum
      = (ns.map c.nodeBalance).sum := by
  have hmap : ns.map (c.addLoopCurrent loop delta).nodeBalance = ns.map c.nodeBalance := by
    apply List.map_congr_left
    intro n hn
    exact preserves_node_balance c loop delta n (h n hn)
  rw [hmap]

/-! ### Module B: Ising -/

theorem flip_twice_identity (lat : Lattice) (i j : Nat) :
    (lat.flip i j).flip i j = lat := by
  obtain ⟨rows⟩ := lat
  simp only [Lattice.flip]
  congr 1
  induction rows generalizing i with
  | nil => cases i <;> rfl
  | cons row rows ih =>
    cases i with
    | zero =>
      simp only [flipRows]
      congr 1
      clear ih
      induction row generalizing j with
      | nil => cases j <;> rfl
      | cons s row ih' =>
        cases j with
        | zero => simp [flipRow]
        | succ p => simp [flipRow, ih']
    | succ p =>
      simp only [flipRows]
      congr 1
      exact ih p

theorem preserves_lattice_shape (lat : Lattice) (i j : Nat) :
    (lat.flip i j).rows.length = lat.rows.length := by
  obtain ⟨rows⟩ := lat
  simp only [Lattice.flip]
  induction rows generalizing i with
  | nil => cases i <;> rfl
  | cons row rows ih =>
    cases i with
    | zero => simp [flipRows]
    | succ p => simp [flipRows, ih p]

theorem flip_changes_magnetization_by_two (lat : Lattice) (i j : Nat) :
    (lat.flip i j).magnetization - lat.magnetization = 0
      ∨ (lat.flip i j).magnetization - lat.magnetization = 2
      ∨ (lat.flip i j).magnetization - lat.magnetization = -2 := by
  obtain ⟨rows⟩ := lat
  simp only [Lattice.flip, Lattice.magnetization]
  induction rows generalizing i with
  | nil => cases i <;> simp [flipRows]
  | cons row rows ih =>
    cases i with
    | zero =>
      simp only [flipRows, List.map_cons, List.sum_cons]
      clear ih
      induction row generalizing j with
      | nil => cases j <;> simp [flipRow]
      | cons s row ih' =>
        cases j with
        | zero =>
          rcases s with ⟨u⟩
          cases u <;> simp [flipRow, spinValue]
        | succ p =>
          simp only [flipRow, List.map_cons, List.sum_cons]
          have := ih' p
          rcases this with h | h | h <;> omega
    | succ p =>
      simp only [flipRows, List.map_cons, List.sum_cons]
      have := ih p
      rcases this with h | h | h <;> omega
