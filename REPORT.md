# Relatório técnico — Kirchhoff/Ising: Bend2 vs Lean 4

**Status: 10/10 leis fechadas (5 leis × 2 linguagens), zero `?TODO`, zero `sorry`.**
Última atualização: 2026-09-23. Ver [README.md](README.md) para uma síntese.

Este documento é o relato completo — matemático e de engenharia — de como
cada uma das dez provas foi construída, o que travou, como foi destravado, e
o que os números do benchmark realmente significam (e não significam). Ele
existe porque a peça mais interessante deste projeto não é o resultado final
("compila"), é o caminho: um compilador sem táticas expõe, passo a passo,
exatamente que álgebra uma prova "óbvia" precisa de verdade.

## Sumário

1. [Contexto e objetivo](#1-contexto-e-objetivo)
2. [Arquitetura e modelo de domínio](#2-arquitetura-e-modelo-de-domínio)
3. [Módulo Ising — narrativa completa](#3-módulo-ising--narrativa-completa)
4. [Módulo Circuit — narrativa completa](#4-módulo-circuit--narrativa-completa)
5. [Lado Lean — os dois ajustes que importaram](#5-lado-lean--os-dois-ajustes-que-importaram)
6. [Benchmark](#6-benchmark)
7. [Gotchas do compilador Bend](#7-gotchas-do-compilador-bend)
8. [Conclusões — o que essa comparação realmente mostra](#8-conclusões--o-que-essa-comparação-realmente-mostra)
9. [Próximos passos](#9-próximos-passos)
10. [Apêndice: mapa de arquivos](#10-apêndice-mapa-de-arquivos)

---

## 1. Contexto e objetivo

O projeto compara Bend2 (linguagem funcional com paralelismo nativo via
interaction nets, sem sistema de táticas) e Lean 4 (assistente de provas com
Mathlib e um arsenal grande de táticas) implementando e **provando
formalmente** propriedades de dois modelos físicos discretos:

- **Módulo A — Circuito elétrico resistivo**: um grafo de arestas com
  corrente sinalizada; a lei de Kirchhoff das correntes como invariante.
- **Módulo B — Ising**: uma grade 2D de spins (±1); conservação/variação de
  magnetização sob a operação de flip.

A pergunta de fundo não é "qual linguagem é melhor" — é **qual é o custo
real, em cada linguagem, de provar as mesmas cinco leis matemáticas**,
medido honestamente. A comparação segue quatro princípios fixos:

- **Mesmo hardware, mesma máquina, mesma sessão** para todas as medições de
  tempo.
- **Mesmo autor** implementando os dois lados, para reduzir viés de
  familiaridade prévia com uma linguagem.
- **Reportar honestamente as assimetrias estruturais** (Lean tem Mathlib e
  táticas; Bend2 tem paralelismo nativo) em vez de tentar neutralizá-las
  artificialmente — o objetivo é mostrar o trade-off real, não empatar os
  números.
- **Toda medição é reprodutível**: script de benchmark versionado no
  repositório (`bench/run.sh`), nunca números soltos no relatório.

## 2. Arquitetura e modelo de domínio

```
bend/
  int.bend             # SInt: inteiro sinal+magnitude feito à mão (Bend não tem Int nativo)
  circuit/
    circuit.bend        # Edge, Circuit, Loop, node_balance, add_loop_current, node_balance_delta(_scaled)
    LAWS.bend            # as 2 leis do módulo A, como `law` (assinatura + hipóteses)
    PROOF.bend            # as provas -- hoje só a "cola" que aplica as lemas de tests/circuit_assoc.bend
  ising/
    lattice.bend         # Spin, Lattice, Coupling, flip, magnetization, local_energy
    LAWS.bend             # as 3 leis do módulo B
    PROOF.bend             # as provas, ~470 linhas, autocontidas
  tests/
    sint_laws.bend        # associatividade/comutatividade geral de SInt.add -- biblioteca reutilizável
    circuit_assoc.bend     # ~30 lemas: a prova de fato das 2 leis do Circuit (ver §4)
    circuit_check.bend, ising_mag.bend, pick_test.bend  # demos/scratch menores
  main.bend             # roda os dois módulos, imprime o estado final

lean/
  Circuit.lean, Ising.lean   # os mesmos tipos, versão Lean
  Laws.lean                    # as 5 leis, enunciado+prova juntos (sem separação LAWS/PROOF)
  Tests.lean                    # #eval de casos conhecidos
```

As cinco leis:

| Lei | Módulo | Enunciado |
| --- | --- | --- |
| `preserves_node_balance` | A | Somar `delta` à corrente de todo arco de um laço não muda o balanço líquido de nenhum nó, desde que o laço seja uma circulação genuína naquele nó |
| `loop_current_conserves_total` | A | O mesmo, somado sobre uma lista fixa de nós — corolário direto |
| `flip_twice_identity` | B | Aplicar `flip` duas vezes na mesma posição retorna a grade original |
| `preserves_lattice_shape` | B | `flip` não muda as dimensões da grade |
| `flip_changes_magnetization_by_two` | B | Um `flip` muda a magnetização em exatamente 0, +2 ou −2 |

O Módulo A prova uma invariante local por indução sobre uma **lista de
arestas de tamanho variável** (não uma árvore binária balanceada); o Módulo
B prova um **limite de variação** (uma diferença igual a 2) sobre a
atualização de uma única célula numa grade. São duas técnicas de indução
genuinamente distintas — o objetivo deliberado era não repetir o mesmo
molde de prova duas vezes com nomes diferentes.

## 3. Módulo Ising — narrativa completa

Três leis, seis provas (3 × 2 linguagens), todas fechadas. As duas
primeiras (`flip_twice_identity`, `preserves_lattice_shape`) são diretas —
casamento estrutural e indução simples sobre a lista de linhas. A terceira,
`flip_changes_magnetization_by_two`, foi o ponto difícil de uma sessão
anterior e vale a pena entender por quê, porque a técnica que a resolveu
reaparece (generalizada) no Circuit.

### O bloqueio: `from_diff` não descasca sozinho

`magnetization` é calculada acumulando `(ups, downs): Nat & Nat` por
recursão direta sobre a grade — nunca uma soma parcial de `SInt`, só no
final uma única chamada a `SInt.from_diff(ups, downs)`. Isso já era uma
escolha de design deliberada de uma sessão anterior: evita precisar de
associatividade geral de `SInt.add`, porque nunca há mais de uma soma de
`SInt` acontecendo.

A prova de que mover um spin de baixo pra cima aumenta `ups` em 1 e reduz
`downs` em 1 — e portanto muda a magnetização em exatamente +2 — precisa de
um fato de "invariância por deslocamento":

```
{SInt.from_diff(1n+x, 1n+y) == SInt.from_diff(x, y) : SInt}
```

Isso *parece* que devia sair de graça por computação pura — mas não sai.
`SInt.from_diff(u, d)` é definido como `from_diff.cmp(Nat.cmp(u, d), u, d)`,
e `from_diff.cmp` usa os valores `u`/`d` **não descascados** nos seus ramos
de magnitude (`Nat.sub(d, u)` etc.). Só o argumento de comparação
(`Nat.cmp(u,d)`) descasca sozinho para `Nat.cmp(x,y)` quando `u=1+x`,
`d=1+y` — o resto da expressão não.

### A técnica: rotear por um parâmetro já avaliado

A saída foi fatorar a comparação por um `Cmp` recebido como **parâmetro**
(portanto casável) em vez de computado inline:

```bend
# c chega como parâmetro já calculado, não como Nat.cmp(x,y) inline
def from_diff_cmp_shift(c: Cmp, +x: Nat, +y: Nat)
  -> {SInt.from_diff.cmp(c, 1n+x, 1n+y) == SInt.from_diff.cmp(c, x, y) : SInt}:
  match c:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

def shift_invariant(+x: Nat, +y: Nat)
  -> {SInt.from_diff(1n+x, 1n+y) == SInt.from_diff(x, y) : SInt}:
  from_diff_cmp_shift(Nat.cmp(x, y), x, y)
```

Bend não consegue `match` numa expressão computada (`Nat.cmp(x,y)`) —
só num parâmetro ou campo. Mas nada impede *chamar* uma função com essa
expressão computada como argumento; dentro da função, o parâmetro é
casável normalmente. Essa é a saída sistemática, e generaliza: qualquer vez
que um `match` trava numa expressão computada, o conserto é fatorar essa
expressão por um parâmetro de uma função auxiliar.

Com `shift_invariant` genuinamente provado, os lemas de passo único
(`diff_inc`/`diff_dec`: mover um spin de baixo pra cima/cima pra baixo muda
a magnetização em exatamente ±2) saem por indução direta sobre `(a, b)`, e
como a magnetização inteira só chama `SInt.add`/`from_diff` **uma vez**, no
final, toda a indução sobre linhas/grade fica inteiramente no nível de
`Nat` (congruência de sucessor) — os dois lemas de passo se aplicam uma
única vez, no topo. É a peça central de `bend/ising/PROOF.bend`
(~470 linhas): `count_rel`, `lift_up`/`lift_down`, `row_pair_rel`,
`combine_cong_left`/`right`, `rows_pair_rel`, `mag_law`.

## 4. Módulo Circuit — narrativa completa

Esta é a parte mais rica do projeto: as duas leis do Circuit ficaram
**abertas por duas sessões inteiras** antes de fechar nesta. Não por falta
de ideia — porque cada tentativa de fechar revelava uma camada nova de
álgebra que precisava ser provada primeiro.

### 4.1 Por que o truque do Ising não se aplica aqui

`add_loop_current` pode tocar **várias** arestas ao mesmo tempo (não um
único flip), e cada aresta tocada contribui um `delta: SInt` **arbitrário**
(não um +2 fixo), acumulado via `SInt.add` repetido conforme a lista de
arestas é percorrida. Não existe um único ponto de conversão final para
adiar — a indução precisa reassociar um termo "soma parcial até agora" a
cada passo. Isso exige, de verdade:

```
{SInt.add(x, SInt.add(y, z)) == SInt.add(SInt.add(x, y), z) : SInt}
```

— associatividade geral de um inteiro sinal+magnitude feito à mão. Lean
fecha o equivalente com uma chamada de `ring`/`omega`. Bend não tem
táticas: isso é construção de termo, caso a caso.

### 4.2 Associatividade geral: os 8 casos

A primeira tentativa (sessão anterior) tentou canonicalizar todo operando
de `SInt.add` como `from_diff` de algum par — o que exigiria o fato
`{SInt{False,m} == from_diff(0n,m)}`, que é **falso em `m=0n`**:
`from_diff` nunca produz o valor não-canônico `SInt{False,0n}` (a "magnitude
zero negativa"), mas ele existe como termo `Data` válido e distinto de
`SInt{True,0n}`. Essa rota foi abandonada.

A rota que fechou: casar os três operandos por sinal (2³ = 8 casos) e, em
cada um, usar diretamente qualquer lema já provado que bater com o formato
*real* que `SInt.add` produz naquele caso — nunca inventando uma forma
canônica que não existe:

```bend
def sint_add_assoc(+a: SInt, +b: SInt, +c: SInt)
  -> {SInt.add(a, SInt.add(b, c)) == SInt.add(SInt.add(a, b), c) : SInt}:
  match a b c:
    case SInt{True{}, am} SInt{True{}, bm} SInt{True{}, cm}:
      %nat_add_assoc(am, bm, cm) : {SInt{True{}, _} == SInt{True{}, Nat.add(Nat.add(am, bm), cm)} : SInt}
      {==}
    # ... mais 7 casos, cada um via add_true_from_diff / add_false_from_diff /
    # sint_add_comm / nat_add_comm, conforme a combinação de sinais
```

Os dois casos mesmo-sinal (`True,True,True` e `False,False,False`) saem
direto de `Nat.add` ser associativo. Os seis casos de sinal misto usam dois
lemas de conversão (`add_true_from_diff`, `add_false_from_diff` — "somar um
`SInt` de sinal conhecido a um `from_diff` dá outro `from_diff`") mais
comutatividade quando a ordem dos operandos precisa trocar. Isso fechou o
bloqueio histórico do projeto — `bend/tests/sint_laws.bend`, 308 linhas,
zero `?TODO`.

### 4.3 A lei estrutural principal: `node_balance_map_update`

Com associatividade geral em mãos, o próximo passo é a peça que realmente
sustenta `preserves_node_balance`:

> Atualizar a corrente de toda aresta de um laço por `delta` desloca o
> balanço de um nó `n` em exatamente `node_balance_delta_scaled` — a soma,
> sobre as arestas do laço que tocam `n`, de `+delta` (se entra) ou
> `-delta` (se sai).

Formalmente:

```
node_balance.go(add_loop_current.go(edges, loop, delta), n)
  == add(node_balance.go(edges, n), node_balance_delta_scaled.go(edges, loop, n, delta))
```

Provado por indução sobre `edges`. O passo indutivo, para uma aresta que
*é* do laço, precisa combinar "a contribuição da aresta mudou" com "o resto
da soma já mudou pela hipótese de indução" — exatamente a identidade
"trocar quatro termos" (`four_term_swap`):

```
add(add(a,b), add(c,d)) == add(add(a,c), add(b,d))
```

que sai em 5 passos de `Equal.trans` usando só `sint_add_assoc`/
`sint_add_comm`. Uma dificuldade de engenharia à parte: se uma aresta *não*
é do laço, saber disso exige computar `is_loop_edge(loop, e)` — uma
expressão computada, não um parâmetro, então **não pode ser casada
diretamente** (mesma restrição do §3). A saída, generalizando o truque do
Ising: escrever um lema auxiliar (`node_balance_map_update.edge_step`)
parametrizado por um `Bool` genérico `is_loop` (casável porque é *seu
próprio* parâmetro), e aplicá-lo com `is_loop_edge(loop,e)` como argumento
no chamador — Bend aceita porque tipo-checagem funciona por normalização,
não por "essa expressão já virou um literal".

### 4.4 A armadilha do zero não-canônico

Esta foi a descoberta mais sutil da sessão. `SInt{nonneg: Bool, mag: Nat}`
tem, por construção, **dois termos distintos que representam zero**:
`SInt{True,0n}` (o zero canônico, o único que `SInt.zero()`/`from_diff`
produzem) e `SInt{False,0n}` (uma "magnitude-zero negativa" — nunca
produzida por operações "limpas", mas um termo `Data` perfeitamente válido,
alcançável por um `delta` escolhido pelo usuário ou uma corrente de aresta
crua).

Isso quebra a identidade mais óbvia do mundo:

```
{SInt.add(x, SInt.zero()) == x : SInt}   -- FALSA em x = SInt{False, 0n}
```

Checagem: `SInt.add(SInt{False,0n}, SInt{True,0n})` cai no ramo
sinal-misto de `SInt.add`, que sempre passa por `from_diff` — e
`from_diff.cmp(EQ{}, 0n, 0n) = SInt{True,0n}`. O resultado é o zero
**canônico**, diferente do `x = SInt{False,0n}` original. A soma "cura" a
não-canonicidade, mas não preserva a identidade do operando.

Essa armadilha apareceu **repetidamente** ao longo da prova, sempre que uma
soma parcial precisava ser combinada com um "termo zero" de bookkeeping:

- `node_balance_delta_scaled` foi definido para **pular** arestas que não
  são do laço (recursão por filtro), em vez de somar um `zero()` explícito
  — evita precisar da identidade falsa logo na definição.
- `repeat_add(k, x)` (`x` somado a si mesmo `k` vezes) foi definido com a
  recursão **uniforme** `repeat_add(0,x)=zero(); repeat_add(1+k,x) =
  add(x, repeat_add(k,x))` — sem um caso especial para `k=1` — porque isso
  torna o "passo sucessor" **verdadeiro por definição** para todo `k`
  (inclusive `k=0`), nunca precisando isolar `add(x, zero())` como um fato
  à parte.
- Onde um "zero à esquerda" era mesmo inevitável (`add_zero_r_nb`,
  `add_zero_l_repeat`/`add_zero_l_sum`), a identidade foi provada **só**
  para valores concretamente seguros (o caso base `Nil` de uma lista, ou um
  `SInt` de sinal manifesto e magnitude não-nula) — nunca para um `SInt`
  opaco arbitrário. Uma observação de bônus que simplificou vários desses
  casos: `repeat_add(k, x)` nunca produz o valor patológico, para nenhum
  `k` ou `x` — a soma sempre "cura" para uma forma canônica ou preserva
  magnitude positiva — então bastou provar a identidade para o *primeiro*
  termo de uma soma e deixar a associatividade geral carregar o resto.

### 4.5 A ponte: de "delta unitário" para "delta arbitrário"

A hipótese de circulação do enunciado (`is_circulation`) é sobre
`node_balance_delta` — a versão com `delta = of_nat(1n)` **fixo**. A lei
precisa valer para um `delta` **arbitrário**. A ponte entre as duas não sai
por álgebra local: a soma bruta de `SInt` não se decompõe estruturalmente
sob indução — somas parciais podem ser não-nulas mesmo quando o total é
zero. É preciso **contar**.

A solução, em `bend/tests/circuit_assoc.bend` (a peça nova desta sessão):

1. **`touch_to.go`/`touch_from.go`**: dois contadores `Nat`, por indução
   sobre as arestas — quantas arestas do laço entram em `n` (`ct`) e
   quantas saem (`cf`).
2. **`char_correspondence`**: prova, por indução, que
   `node_balance_delta_scaled` é exatamente
   `repeat_add(ct, delta) + repeat_add(cf, -delta)` — a soma se decompõe
   nos dois contadores, para *qualquer* `delta`.
3. **`char_unit`**: instancia o item 2 em `delta = of_nat(1n)`, usando dois
   fechos-de-forma (`repeat_add(k, of_nat(1n)) == of_nat(k)`, e o análogo
   negado) para reduzir a soma unitária a `from_diff(ct, cf)`.
4. **`from_diff_zero_implies_eq`**: se `from_diff(u,d) == zero()`, então
   `u == d`. Provado por indução estrutural direta em `(u,d)` — nos dois
   casos-base impossíveis (`from_diff(0,1+d)` ou `from_diff(1+u,0)` sendo
   igual a zero, o que nunca acontece de verdade), uma projeção `mag_of`
   aplicada à hipótese (via `Equal.cong`) produz diretamente a igualdade de
   `Nat` necessária — **eliminação por absurdo sem precisar de um tipo
   `Void`/`Empty` explícito** (ver gotcha #7 abaixo).
5. Combinando 3+4: a hipótese de circulação força `ct == cf`.
6. **`repeat_add_cancel`**: uma vez `ct == cf`, `repeat_add(ct,delta) +
   repeat_add(ct,-delta) == zero()` para **qualquer** `delta` — via
   `four_term_swap` mais o fato geral (esse sim, sempre verdadeiro, mesmo
   no zero patológico) `add(x, neg(x)) == zero()`.

O resultado (`circulation_implies_scaled_zero`) combinado com
`node_balance_map_update` (§4.3) e `add_zero_r_nb` fecha
`preserves_node_balance` em `bend/circuit/PROOF.bend`.
`loop_current_conserves_total` sai como corolário direto, por indução na
lista de nós, aplicando `preserves_node_balance` ponto a ponto.

### 4.6 Números finais do módulo

`bend/circuit/PROOF.bend` (73 linhas) hoje é só a "cola": destrutura
`Circuit`/`Loop`, aplica as lemas acima às duas leis. O trabalho de
verdade — a associatividade geral e a ponte de contagem — vive em
`bend/tests/sint_laws.bend` (308 linhas) e `bend/tests/circuit_assoc.bend`
(499 linhas, ~30 lemas), ambos arquivos independentemente checáveis
(`bend bend/tests/circuit_assoc.bend`). Total honesto do custo de prova do
Circuit: **880 linhas** (73 + 499 + 308).

## 5. Lado Lean — os dois ajustes que importaram

O lado Lean fechou as 5 leis sem nenhum termo manual — só táticas
(`induction`, `simp`, `omega`, `ring`, `split_ifs`). Dois problemas reais
apareceram e foram corrigidos:

**Colisão de nome com o Mathlib.** `Ising.lean` tinha uma `structure
Lattice` no nível superior, que colidia com a classe `Order.Lattice` do
próprio Mathlib (ambas geram `Lattice.noConfusion` no mesmo namespace). O
build falhava com `environment already contains 'Lattice.noConfusion'`.
Correção: envolver o arquivo inteiro em `namespace Ising ... end Ising`.
Lição geral: nunca deixe um tipo de domínio sem namespace quando o Mathlib
é dependência — colisões assim (`Lattice`, mas vigie também `Group`,
`Ring`, `Field`, `Order`, `Path`, `Set`) são fáceis de levar sem querer.

**Reformulação de `nodeBalanceDelta`.** A versão original usava duas
chamadas de `List.filter` encadeadas para contar arestas de laço tocando um
nó; sob `simp`/`by_cases`, o Lean fundia os dois filtros numa única
predicada composta de formas imprevisíveis, e casar essa forma à mão virou
fonte constante de erro. A correção foi trocar por um único acumulador
`Int` percorrido por recursão estrutural direta sobre a lista de arestas —
espelhando como `List.sum` do próprio Lean funciona — o que deixou
`split_ifs`/`simp_all`/`ring` fecharem de forma confiável.

Vale notar o paralelo: a "reformulação de acumulador para recursão direta"
que destravou o lado Lean é **a mesma ideia estrutural** que, do lado Bend,
tornou `node_balance.go`/`node_balance_delta_scaled.go` induzíveis (§4.3) —
convergência independente para a mesma solução, em duas linguagens
diferentes, porque o problema matemático subjacente é o mesmo.

## 6. Benchmark

Números medidos nesta máquina, nesta sessão, via `bash bench/run.sh`
(script versionado — ver `bench/run.sh`; saída bruta desta rodada em
`bench/last_run.log`, não versionado por ser regenerável).

### 6.1 Linhas de código de prova

| Arquivo | LOC | Papel |
| --- | ---: | --- |
| `bend/ising/PROOF.bend` | 474 | prova (3/3 leis) |
| `bend/circuit/PROOF.bend` | 73 | cola de prova (importa circuit_assoc.bend) |
| `bend/tests/circuit_assoc.bend` | 499 | biblioteca de lemas (associatividade+contagem) |
| `bend/tests/sint_laws.bend` | 308 | `SInt.add` associativo/comutativo (usado só pelo Circuit) |
| **Bend total (prova)** | **1354** | 474 + 73 + 499 + 308 |
| `lean/Laws.lean` | 151 | enunciado + prova das 5 leis, juntos |

### 6.2 Linhas de código não-prova (tipos e funções)

| Arquivo | LOC |
| --- | ---: |
| `bend/ising/lattice.bend` | 93 |
| `bend/circuit/circuit.bend` | 152 |
| `bend/int.bend` (compartilhado) | 52 |
| **Bend total** | **297** |
| `lean/Ising.lean` | 34 |
| `lean/Circuit.lean` | 41 |
| **Lean total** | **75** |

### 6.3 Automação vs. termo manual

| | Lean 4 | Bend2 |
| --- | --- | --- |
| Leis fechadas só com tática | 5/5 (100%) | N/A — sem táticas por design |
| Leis fechadas com termo explícito | 0/5 | 5/5 (100%) |

### 6.4 Tempo de checagem e execução

| Medição | Comando | Execução 1 | Execução 2 | Execução 3 |
| --- | --- | ---: | ---: | ---: |
| Checagem — Ising | `bend ising/PROOF.bend` | 4.55s | 2.26s | 2.44s |
| Checagem — Circuit (cola) | `bend circuit/PROOF.bend` | 3.28s | 1.61s | 2.29s |
| Checagem — Circuit (lemas) | `bend tests/circuit_assoc.bend` | 2.05s | 2.34s | 1.70s |
| Checagem — Laws (incremental) | `lake build Laws` | 413.40s | 30.90s | 20.88s |
| Execução — demo | `bend main.bend` | 2.79s | 2.07s | 1.58s |

Lean's 3 execuções caem porque o cache do Lake aquece entre rodadas —
20.88s (a terceira) é o número comparável a "checar uma alteração pontual"
num projeto já compilado antes. Execução do Lean não é medida
separadamente: `Tests.lean` só tem `#eval`, que roda como efeito colateral
do type-check — não há um binário compilado à parte para cronometrar.

### 6.5 Leitura honesta dos números (não um veredito)

- **Esforço de prova**: Bend precisou de **~9×** mais LOC de prova que Lean
  para o mesmo conjunto de cinco leis (1354 vs. 151) — e isso já é depois
  de tudo fechado, não uma subestimativa como no relatório anterior desta
  sessão. A maior parte do custo extra (880 das 1354 linhas) é exatamente
  o Circuit — reconstruir do zero associatividade de inteiros e um
  argumento de contagem que `omega`/`ring` do Lean resolvem em uma linha.
  Isso **não** é um problema de design de Bend; é o preço estrutural de
  não ter uma biblioteca de aritmética provada (Mathlib) nem táticas de
  decisão automatizada.
- **Automação**: Lean fecha 100% das
  leis só com táticas, Bend não tem essa opção por design (termo explícito
  em toda prova, até os lemas auxiliares de aritmética que Lean ganha de
  graça via `omega`/`ring`).
- **Tempo de checagem**: Bend é dramaticamente mais rápido por execução
  (1-5s vs. dezenas de segundos mesmo incremental) — mas essa comparação
  favorece Bend na direção errada: o binário do Bend não carrega uma
  biblioteca do tamanho do Mathlib. Não é uma medida de qual *checker* é
  mais eficiente; é uma medida de qual dependência cada checagem paga.
- **Linhas não-prova**: Bend precisou de ~4× mais LOC de tipos/funções
  (297 vs. 75), em grande parte porque `int.bend` (52 LOC) reimplementa do
  zero um tipo inteiro assinado que Lean ganha de graça do core/Mathlib,
  e porque Bend não tem `List.filter`/`List.sum` no nível de conveniência
  do Lean, exigindo mais funções auxiliares escritas à mão (`loop_pairs`,
  `node_balance.go`, `touch_to.go`/`touch_from.go`).
- **Paralelismo/GPU**: não medido nesta sessão — nenhuma
  das leis provadas aqui precisa de execução paralela; seria um eixo de
  comparação independente, sobre uma operação diferente (`sweep`).

## 7. Gotchas do compilador Bend

Catalogados por reprodução mínima contra o compilador real — não
suposições. Os seis primeiros vêm de sessões anteriores; o sétimo e oitavo
são novos desta sessão.

**1 — Nome de def igual a um alias de import quebra ao ser importado por
outro arquivo.** `import ./circuit.bend as Circuit` + `def
Circuit.foo(...): ...` no *mesmo* arquivo funciona rodado direto, mas falha
com `expected: a defined name, observed: Circuit.foo` assim que um segundo
arquivo importa esse arquivo. Correção: nunca nomear seus próprios defs com
um prefixo igual a um alias de import no mesmo arquivo.

**2 — Referência a frente quebra, mesmo sem recursão.** Uma função
auxiliar definida *textualmente antes* de outra que ela chama falha com o
mesmo erro confuso — mesmo sem nenhuma das duas ser recursiva e sem import
envolvido. Sempre checar a ordem textual dos `def`s primeiro quando esse
erro aparecer.

**3 — `Nat & Nat` não serve como tipo numa igualdade.** Pares via `&` são
sempre `Kind(&1)` (`Type`), nunca `Data` — mas `{a == b : T}` exige `T` com
kind `Data`. Falha com `expected: Data, observed: Type`. Correção: definir
um record próprio (`type Foo is Data: Foo{a:A, b:B}`) sempre que for
preciso enunciar igualdades sobre um valor tipo-par.

**4 — `Nat.cmp`/`Nat.sub` só descascam de graça com construtor visível dos
dois lados.** `Nat.cmp(1n+X, 1n+Y)` reduz de graça para `Nat.cmp(X, Y)`,
mesmo com `X`,`Y` totalmente simbólicos (mesmo vale para `Nat.sub`). Mas
`Nat.cmp(1n+X, Y)` contra um `Y` opaco (não visivelmente `0n`/`1n+_`)
trava, mesmo que `Y` "obviamente" decidiria a comparação sozinho.
Concretamente: `Nat.sub(a, 0n)` **não** reduz para `a` quando `a` é uma
variável opaca — só quando `a` já é manifestamente `0n` ou `1n+algo`.

**5 — A saída para "`match` não escrutina expressão computada" generaliza
para provas.** Já era conhecida para computar valores (fatorar
`Nat.cmp(a,b)` num helper `.go` que recebe o `Cmp` como parâmetro). Esta
sessão confirmou, repetidamente, que a mesma técnica destrava obrigações de
*prova* igualmente — inclusive booleanos derivados de comparações
estruturais arbitrárias (`is_loop_edge(loop,e)` no Circuit, não só
`Nat.cmp`). Não é truque de performance; é a saída sistemática sempre que
um `match` trava numa expressão computada, dentro ou fora de uma prova.

**6 — `Exists` funciona fora de blocos `law`.** `Exists(A, x => B(x))` do
`Base` funciona como expressão `Type` comum fora de `law`, não só via o
açúcar `exs` que o GUIDE mostra dentro de leis. Construa uma testemunha com
`(valor, prova)`, igual a um par comum.

**7 — Eliminação por absurdo sem `Void`/`Empty` explícito, via
`Equal.cong` + `Bool.pick`.** Bend não expõe um tipo `Empty`/`Void` com
eliminador embutido nesta base. Ainda assim, dado um absurdo `h: {True{} ==
False{} : Bool}` (por exemplo, `Nat.cmp` retornando dois construtores
incompatíveis), é possível produzir uma prova de **qualquer** igualdade-alvo
`{X == Y : T}`: basta `Equal.cong(Bool, T, b => Bool.pick(T, b, X, Y),
True{}, False{}, h)`. `Bool.pick` reduz livremente nos dois lados (`True{}`
e `False{}` são literais), então o resultado normaliza exatamente para
`{X == Y}` — confirmado contra o compilador real (`bend/tests/circuit_assoc.bend`,
`from_diff_zero_implies_eq`, casos-base). Generaliza para qualquer tipo de
absurdo com discriminador (`Cmp`, `SInt` via projeção de campo, etc.), sem
precisar inventar um tipo vazio à parte.

**8 — `Type` é o universo; `Set` já é outra coisa.** Tentar declarar um
parâmetro de tipo genérico como `T: Set` compila silenciosamente errado —
`Set` já existe no `Base` (provavelmente um tipo de coleção), então o
parâmetro assume esse tipo em vez de ser um universo. O erro só aparece
depois, tentando *usar* `T` como tipo (`expected: Type, observed: Data`
numa chamada de `Equal.cong` mais adiante). Use `T: Type` para
parametrizar sobre um tipo genérico — mas note que `Equal.cong`/`Equal.trans`
exigem que os argumentos de tipo concretos passados a eles sejam `Data`
(kind concreto), não a variável de universo `T` em si — então uma função
"genérica" que use `Equal.cong` internamente não pode ficar
polimórfica sobre `T: Type` até o fim; precisa ser instanciada em cada tipo
concreto (`Nat`, `Int.SInt`, etc.) separadamente.

## 8. Conclusões — o que essa comparação realmente mostra

Depois de fechar as 10 provas dos dois lados, os números confirmam com
dados reais a hipótese qualitativa de partida do projeto (§1):

- **Lean com Mathlib é estruturalmente mais barato para álgebra "chata"**
  (associatividade, aritmética de sinais, contagem). Não é sobre a
  linguagem Lean em si — é sobre ter, de graça, uma década de lemas de
  `Nat`/`Int` já provados e táticas de decisão (`omega`, `ring`) que os
  aplicam automaticamente. Em Bend, cada um desses lemas precisou ser
  redescoberto e escrito à mão — o trabalho de `bend/tests/sint_laws.bend`
  e `bend/tests/circuit_assoc.bend`, juntos, é essencialmente uma
  mini-biblioteca de aritmética de inteiros que o Lean traz pronta.
- **Isso não é grátis nem no Lean**: as duas correções do §5 (namespace
  colidindo com Mathlib; reformular um acumulador para recursão direta)
  mostram que "ter uma biblioteca gigante" tem seu próprio custo de
  fricção — colisões de nome, e a mesma armadilha estrutural
  (acumulador-fold vs. recursão direta) que também mordeu o lado Bend.
- **A armadilha do zero não-canônico é o achado mais transferível
  desta sessão** — não é específica de Bend. Qualquer representação de
  inteiro por sinal+magnitude (em qualquer linguagem, provada ou não) tem
  esse mesmo ponto cego: dois valores distintos representando "zero", só
  um deles produzido por construção "limpa". Um `Int` binário em
  complemento-de-dois (como o do Lean/Mathlib) não tem esse problema — é
  uma vantagem de representação, não de linguagem, e vale a pena carregar
  como lição para qualquer implementação futura de inteiros à mão.
- **Bend2 ganha limpo em tempo de checagem por execução**, mas essa vitória
  é sobre o tamanho da dependência carregada, não sobre a eficiência do
  verificador de tipos em si — as duas coisas não deveriam ser confundidas
  ao ler a tabela do §6.4.
- **Nenhuma das duas linguagens "perdeu"** — o objetivo nunca foi empatar
  os números. O trade-off é real: Lean troca "escrever seu próprio kit de
  aritmética" por "aprender a dirigir táticas que às vezes fecham
  sozinhas, às vezes não" (as reformulações do §5 vieram de tática que não
  fechava de primeira); Bend troca "nunca lutar contra uma tática opaca"
  por "construir cada fato de aritmética à mão, uma vez, para sempre
  reutilizável depois".

## 9. Próximos passos

- **Paralelismo de CPU** (fase avançada, opcional): medir speedup numa
  operação `sweep` sobre a grade Ising, usando a metodologia de
  bend2.dev/learn/measuring-speedup. Não implementado nesta sessão — seria
  escopo novo, não uma continuação das provas já fechadas.
- **GPU**: fora de escopo nesta máquina (sem GPU disponível).
- **Lei `resume`** (fase avançada, opcional): rodar a simulação em lotes é
  equivalente a rodar tudo de uma vez, testada nos dois módulos — não
  implementada.
- **Consolidar `bend/tests/circuit_assoc.bend` dentro de
  `bend/circuit/PROOF.bend`** (opcional, cosmético): hoje a prova real vive
  num arquivo de teste por escolha deliberada (mantém cada lema
  independentemente checável durante o desenvolvimento); poderia ser
  inlined ou reorganizado numa pasta `bend/circuit/proofs/` sem mudar
  nenhum conteúdo matemático.

## 10. Apêndice: mapa de arquivos

| Arquivo | Linhas | O que é |
| --- | ---: | --- |
| `bend/int.bend` | 52 | `SInt` (sinal+magnitude), `add`/`neg`/`from_diff` |
| `bend/circuit/circuit.bend` | 152 | tipos + `node_balance`, `add_loop_current`, `node_balance_delta(_scaled)` |
| `bend/circuit/LAWS.bend` | 57 | as 2 leis do Circuit, como `law` |
| `bend/circuit/PROOF.bend` | 73 | prova (cola, importa `circuit_assoc.bend`) |
| `bend/ising/lattice.bend` | 93 | tipos + `flip`, `magnetization`, `local_energy` |
| `bend/ising/LAWS.bend` | 33 | as 3 leis do Ising |
| `bend/ising/PROOF.bend` | 474 | prova completa, autocontida |
| `bend/tests/sint_laws.bend` | 308 | `SInt.add` associativo/comutativo geral |
| `bend/tests/circuit_assoc.bend` | 499 | ~30 lemas: a prova de fato do Circuit |
| `bend/tests/circuit_check.bend` | 18 | demo standalone do Circuit |
| `bend/tests/ising_mag.bend` | 370 | registro histórico da derivação de `diff_inc`/`diff_dec` |
| `bend/tests/pick_test.bend` | 12 | probe de `Bool.pick` |
| `bend/main.bend` | — | roda os dois módulos, imprime o estado final |
| `lean/Circuit.lean` | 41 | tipos do Circuit |
| `lean/Ising.lean` | 34 | tipos do Ising |
| `lean/Laws.lean` | 151 | as 5 leis, enunciado+prova |
| `lean/Tests.lean` | 13 | `#eval` de casos conhecidos |
| `bench/run.sh` | — | script de benchmark versionado e reproduzível |
