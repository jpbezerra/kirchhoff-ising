# Kirchhoff / Ising — Bend2 vs Lean 4

Comparação entre Bend2 e Lean 4 implementando e provando propriedades formais
sobre dois modelos físicos discretos: um circuito elétrico resistivo (Lei das
Correntes de Kirchhoff) e uma rede de spins tipo Ising. Ver [PRD.md](PRD.md)
para o escopo completo, o modelo de domínio (§5) e a metodologia de
comparação (§8).

## Estrutura

```
bend/
  circuit/
    circuit.bend    # Node, Edge, Circuit, Loop + node_balance, add_loop_current
    LAWS.bend
    PROOF.bend
  ising/
    lattice.bend     # Spin, Lattice, Coupling + flip, magnetization, local_energy
    LAWS.bend
    PROOF.bend
  main.bend          # roda os dois módulos e imprime o estado final
  tests/

lean/
  Circuit.lean       # Node, Edge, Circuit, Loop + node_balance, add_loop_current
  Ising.lean         # Spin, Lattice, Coupling + flip, magnetization, local_energy
  Laws.lean          # os mesmos enunciados do PRD §5, como `theorem`
  lakefile.lean      # build com Lake, dependência de Mathlib
  Tests.lean         # #eval de casos conhecidos
```

Ainda sem implementação — apenas o esqueleto de arquivos descrito no PRD (§6 e §7).
