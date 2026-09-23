# Kirchhoff / Ising — Bend2 vs Lean 4

Comparação entre Bend2 e Lean 4 implementando e **provando formalmente**
propriedades de dois modelos físicos discretos: um circuito elétrico
resistivo (Lei das Correntes de Kirchhoff) e uma rede de spins tipo Ising.

**Status: 10/10 leis fechadas (5 leis × 2 linguagens), zero `?TODO`, zero
`sorry`.**

| | Lean 4 | Bend2 |
| --- | --- | --- |
| `flip_twice_identity` | ✓ | ✓ |
| `preserves_lattice_shape` | ✓ | ✓ |
| `flip_changes_magnetization_by_two` | ✓ | ✓ |
| `preserves_node_balance` | ✓ | ✓ |
| `loop_current_conserves_total` | ✓ | ✓ |

Para o relato completo — a matemática de cada prova, o que travou e como
foi destravado, os números do benchmark e o que eles significam — ver
**[REPORT.md](REPORT.md)**, ou a versão interativa em
**https://jpbezerra.github.io/kirchhoff-ising/** (`docs/index.html`, servido
via GitHub Pages).

## Estrutura

```
bend/
  int.bend             # SInt: inteiro sinal+magnitude feito à mão
  circuit/
    circuit.bend        # Edge, Circuit, Loop, node_balance, add_loop_current
    LAWS.bend            # as 2 leis do Circuit
    PROOF.bend            # prova (cola, importa proofs/circuit_assoc.bend)
    proofs/
      circuit_assoc.bend   # a prova de fato das 2 leis do Circuit (~30 lemas)
  ising/
    lattice.bend         # Spin, Lattice, Coupling, flip, magnetization
    LAWS.bend             # as 3 leis do Ising
    PROOF.bend             # prova, autocontida
  tests/
    sint_laws.bend        # associatividade/comutatividade geral de SInt.add
  main.bend             # roda os dois módulos, imprime o estado final

lean/
  Circuit.lean, Ising.lean   # os mesmos tipos, versão Lean
  Laws.lean                    # as 5 leis, enunciado + prova
  Tests.lean                    # #eval de casos conhecidos

bench/
  run.sh               # script de benchmark versionado e reproduzível

docs/
  index.html           # relatório interativo, servido via GitHub Pages
```

## Rodando

```bash
# Bend -- checa as provas e roda a demo
bend bend/circuit/PROOF.bend
bend bend/ising/PROOF.bend
bend bend/main.bend

# Lean -- checa as provas (requer toolchain via elan/lake já instalado)
cd lean && lake build Laws

# Benchmark completo (tempo de checagem/execução + LOC dos dois lados)
bash bench/run.sh
```

## O que este projeto mede

Não "qual linguagem é melhor" — qual é o **custo real, medido, de provar as
mesmas cinco leis matemáticas** em Bend2 (sem táticas, com paralelismo
nativo) e Lean 4 (com Mathlib e táticas de decisão), no mesmo hardware, na
mesma sessão, pelo mesmo autor. Ver [REPORT.md §6](REPORT.md#6-benchmark)
para a tabela completa e uma leitura honesta dos números — a diferença de
esforço de prova (~9× mais LOC do lado Bend) tem uma causa específica e
compreensível, não é um veredito genérico sobre a linguagem.
