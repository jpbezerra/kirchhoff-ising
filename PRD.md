# PRD: Circuito Elétrico e Magnetismo (Ising) — Bend2 vs Lean 4

2026-09-21 · @Someone

## 1. Resumo executivo

Este projeto compara Bend2 e Lean 4 implementando e provando propriedades formais sobre dois modelos físicos discretos, escolhidos por exigirem técnicas de prova estruturalmente diferentes entre si:

1. **Circuito elétrico resistivo** (Lei das Correntes de Kirchhoff): o modelo é um **grafo**, não uma árvore, e a lei provada é uma invariante **local** (em cada nó) preservada por uma operação de análise de malhas (mesh current), não uma soma global como no exemplo de referência do Bend2.
2. **Rede de spins tipo Ising** (magnetismo): o modelo é uma **grade 2D**, e as leis provadas são sobre **variação controlada** (quanto uma atualização de spin pode mudar a magnetização/energia total), não conservação exata.

Os dois módulos são implementados e provados **em paralelo** nas duas linguagens, com o mesmo relatório comparativo objetivo do §8 aplicado a ambos. Essa escolha foi deliberada: o exemplo de colisão de galáxias do Bend2 (bend2.dev/learn/galaxy-encounter) usa árvore + conservação global — os dois módulos deste projeto evitam repetir esse padrão, testando o par de linguagens em terrenos de prova genuinamente diferentes.

## 2. Contexto e motivação

As duas linguagens compartilham tipos dependentes e a capacidade de checar provas de propriedades sobre um programa antes de executá-lo, mas divergem em quase tudo o mais:

- **Lean 4** é uma linguagem de prova madura, com Mathlib (biblioteca com milhares de lemas e táticas) e um kernel pequeno e bem auditado. É o padrão de facto para formalização matemática hoje.
- **Bend2** é jovem, exige provas por termos explícitos (sem táticas), mas embute paralelismo fork/join e execução em GPU (Metal/CUDA) diretamente na linguagem — algo que Lean não oferece nativamente.

A pergunta que motiva este projeto: **quando vale a pena trocar a maturidade e as bibliotecas de Lean pelo paralelismo nativo de Bend2, e qual o custo real disso em esforço de prova?** Comparações objetivas dessa natureza são raras porque a maioria dos benchmarks disponíveis (ex.: os publicados em bend2.dev) usam programas sintéticos pequenos, não um domínio de aplicação real com múltiplas leis interdependentes.

Os domínios escolhidos — circuito elétrico e rede de spins — partem do mesmo padrão "modelo físico + leis + provas" popularizado pelo exemplo de colisão de galáxias do Bend2 (bend2.dev/learn/galaxy-encounter), mas deliberadamente usam estruturas de dados (grafo, grade) e tipos de lei (invariante local, variação controlada) diferentes da árvore e da conservação global desse exemplo — justificativa completa no §4.

## 3. Objetivos e métricas de sucesso

### Objetivos

1. Implementar o mesmo modelo de domínio (§5) em Bend2 e em Lean 4, com o mesmo conjunto de leis provadas nas duas linguagens.
2. Produzir um relatório comparativo com dados concretos (não opiniões) nos eixos do §8.
3. Publicar o código de ambas as implementações e o relatório de forma que sejam reprodutíveis por terceiros.

### Critérios de sucesso (definição de "pronto")

| # | Critério | Como verificar |
| --- | --- | --- |
| 1 | Todas as leis do §5 compilam e checam (`bend x.bend` sem erro / `lake build` sem erro) nas duas linguagens | Log do compilador/checker anexado ao repositório |
| 2 | Cada lei tem uma prova completa (sem `?TODO`/`sorry`) | Inspeção do código-fonte |
| 3 | Testes numéricos confirmam que o modelo se comporta como esperado (não apenas "não quebra as leis", como discutido no §4) | Suíte de testes com casos conhecidos |
| 4 | Relatório comparativo preenchido com números reais (linhas de código de prova, tempo de checagem, tempo de execução) para os dois lados | Tabela do §8 populada |
| 5 | Repositório público com instruções de build para as duas linguagens | README testado do zero |

**Status em 2026-09-22**: critérios 1, 3 e 5 atendidos. Critério 4 atendido (§8 preenchido). Critério 2 **parcialmente** atendido: 8 das 10 leis (todas as 5 do lado Lean, 3 das 5 do lado Bend) têm prova completa sem `?TODO`/`sorry`; as 2 restantes (`preserves_node_balance` e `loop_current_conserves_total`, ambas em Bend) ficam como `?TODO` documentado em `bend/circuit/PROOF.bend`, com a causa raiz (associatividade geral de `SInt.add`) diagnosticada e parcialmente provada em `bend/tests/sint_laws.bend`. Ver HANDOFF.md para o estado exato e o próximo passo.

### Não-objetivos explícitos

- Não é objetivo publicar um paper ou reivindicar superioridade definitiva de uma linguagem sobre a outra — o objetivo é dados comparáveis, não um veredito.

## 4. Escopo e não-escopo

### Dentro do escopo

Dois módulos independentes, cada um com seu próprio conjunto de tipos, leis e provas, implementados nas duas linguagens:

**Módulo A — Circuito elétrico resistivo**

- Circuito representado como grafo: lista de nós e lista de arestas (resistores) com corrente associada
- Operação de análise de malhas (mesh current): adicionar uma corrente circulante a um laço fechado do circuito
- Lei de Kirchhoff das Correntes (KCL): a corrente líquida em cada nó não muda quando uma corrente de malha é aplicada
- Visualização opcional do grafo e das correntes (entregável de fase avançada, junto com o Módulo B)

**Módulo B — Rede de spins tipo Ising**

- Grade 2D de spins (+1/-1), representada com inteiros para evitar os problemas de precisão de ponto flutuante do projeto anterior
- Operação de flip de um spin (regra local, base do algoritmo de Metropolis)
- Magnetização total (soma dos spins) e energia local de interação entre vizinhos (constante de acoplamento inteira)
- Leis sobre variação controlada: um flip muda a magnetização em exatamente ±2; aplicar o mesmo flip duas vezes retorna ao estado original
- Visualização opcional da grade como mapa de calor (mesma fase avançada do Módulo A)

### Fora do escopo

| Item | Por que fica de fora |
| --- | --- |
| Circuitos com componentes reativos (capacitores, indutores) e corrente alternada | Exige números complexos (impedância) — Bend2 não tem esse tipo embutido |
| Solver completo de circuito (resolver todas as correntes/tensões do zero) | O objetivo é provar que uma operação de atualização preserva uma lei, não implementar um solver de circuitos de produção |
| Algoritmo de Metropolis completo, com temperatura e probabilidade de aceitação | Exigiria ponto flutuante e números aleatórios — o foco é a mecânica de atualização de spin e suas leis estruturais, não a simulação estatística completa |
| Ising 3D ou grades muito maiores que o necessário para os benchmarks | Sem necessidade para os objetivos de comparação do §8 |
| Validação contra circuitos ou experimentos de magnetismo reais | Os dois modelos são ilustrativos, escolhidos pela estrutura de prova que exercitam, não pela precisão física |

Ambos os módulos evitam deliberadamente ponto flutuante — `Nat`/`Int` bastam para todas as leis propostas, o que também contorna a limitação de `F64` do Bend2 discutida no projeto anterior.

## 5. Modelo de domínio

### Entidades

**Módulo A — Circuito**

| Tipo | Campos | Descrição |
| --- | --- | --- |
| `Node` | id (Nat) | Identificador de um nó do circuito |
| `Edge` | from (Nat), to (Nat), current (Int) | Aresta do grafo representando um resistor com corrente sinalizada |
| `Circuit` | edges (List\<Edge>) | O circuito completo, como lista de arestas |
| `Loop` | nodes (List\<Nat>) | Sequência cíclica de nós formando uma malha fechada |

**Módulo B — Ising**

| Tipo | Campos | Descrição |
| --- | --- | --- |
| `Spin` | value (+1 ou -1, via Bool) | Estado de um spin |
| `Lattice` | rows (List\<List\<Spin>>) | Grade 2D de spins |
| `Coupling` | j (Int) | Constante de acoplamento entre vizinhos |

### Operações a modelar

**Módulo A**

1. `node_balance(node, circuit) -> Int`: soma das correntes entrando menos saindo de um nó
2. `add_loop_current(circuit, loop, delta) -> Circuit`: soma `delta` à corrente de toda aresta pertencente ao laço `loop`
3. (fase avançada) `relax_step`: uma iteração de um método iterativo de solução (Gauss-Seidel) sobre o circuito completo

**Módulo B**

1. `flip(lattice, i, j) -> Lattice`: inverte o spin na posição (i,j)
2. `magnetization(lattice) -> Int`: soma de todos os spins
3. `local_energy(lattice, i, j, coupling) -> Int`: energia de interação do spin (i,j) com seus 4 vizinhos
4. (fase avançada) `sweep`: aplica flip em toda a grade — candidato natural a paralelismo fork/join do Bend2, já que cada linha (ou célula) pode ser atualizada de forma independente

### Leis a provar

| Lei | Módulo | Enunciado |
| --- | --- | --- |
| `preserves_node_balance` | A | A corrente líquida em qualquer nó não muda ao aplicar uma corrente de malha |
| `loop_current_conserves_total` | A | A soma de todas as correntes do circuito não muda ao aplicar uma corrente de malha |
| `flip_twice_identity` | B | Aplicar `flip` duas vezes na mesma posição retorna a grade original |
| `flip_changes_magnetization_by_two` | B | O valor absoluto da diferença de magnetização antes/depois de um `flip` é exatamente 2 |
| `preserves_lattice_shape` | B | `flip` não muda as dimensões da grade |
| `resume` (fase avançada) | A e B | Rodar a simulação em lotes é equivalente a rodar tudo de uma vez — mesma lei do exemplo da galáxia, agora testada em dois domínios diferentes |

Diferente do projeto anterior, as leis aqui não seguem um único molde: o Módulo A prova uma invariante local por indução sobre uma **lista de arestas de tamanho variável** (não uma árvore binária), e o Módulo B prova **limites de variação** (uma diferença igual a 2, não uma soma preservada) sobre a atualização de uma célula numa grade. Isso testa duas técnicas de prova genuinamente distintas nas duas linguagens, em ve� de repetir o padrão do exemplo da galáxia duas vezes com nomes diferentes.

## 6. Plano de implementação em Bend2

### Estrutura de arquivos

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
```

### Sequência de trabalho

1. Instalar o compilador Bend2 a partir do código-fonte (bend2.dev/notes/install-bend2-from-source).
2. Começar pelo **Módulo B (Ising)**: estruturalmente mais simples (grade de tamanho fixo, sem indução sobre lista de tamanho variável). Implementar `Lattice`/`flip`/`magnetization` e provar `flip_twice_identity` como aquecimento.
3. Provar `flip_changes_magnetization_by_two` — primeira lei "de limite" do projeto (uma diferença igual a uma constante, não uma igualdade sobre o estado inteiro).
4. Implementar `preserves_lattice_shape` e seguir para o **Módulo A (Circuito)**: representar `Circuit` como `List<Edge>` e implementar `node_balance`, decidindo como filtrar arestas que tocam um nó usando igualdade decidível de `Nat`.
5. Implementar `add_loop_current` e provar `preserves_node_balance` — a prova espera indução sobre a lista de arestas do circuito, tratando separadamente o caso em que a aresta pertence ao laço e o caso em que não pertence.
6. Provar `loop_current_conserves_total`.
7. (Fase avançada) Paralelizar `sweep` (Módulo B, por linha ou por célula) com `a b = f(x) g(y)` e medir speedup seguindo bend2.dev/learn/measuring-speedup.
8. (Fase avançada) Visualização: grafo do circuito e mapa de calor da grade, no mesmo espírito da demo da galáxia no navegador.

### Riscos específicos de Bend2

- Indução sobre `List<Edge>` para provar `preserves_node_balance` é mais delicada que indução em árvore binária: o número de arestas que tocam um nó é variável, então o caso indutivo precisa tratar "esta aresta pertence ao laço" e "esta aresta não pertence" separadamente — mais ramificação que os exemplos de árvore vistos até agora.
- Confirmar como a biblioteca `Base` expõe igualdade decidível de `Nat` (`Nat.eq` ou equivalente) antes de depender dela no meio de uma prova por indução.
- Mesmos riscos gerais do compilador em desenvolvimento ativo do projeto anterior (mensagens de erro pouco claras, ausência de táticas, divergências conhecidas entre o checker e sua formalização em Lean) — reservar tempo de buffer.

## 7. Plano de implementação em Lean 4

### Estrutura de arquivos

```
lean/
  Circuit.lean       # Node, Edge, Circuit, Loop + node_balance, add_loop_current
  Ising.lean         # Spin, Lattice, Coupling + flip, magnetization, local_energy
  Laws.lean          # os mesmos enunciados do §5, como `theorem`
  lakefile.lean      # build com Lake, dependência de Mathlib
  Tests.lean         # #eval de casos conhecidos
```

### Sequência de trabalho

1. Iniciar projeto com `lake new` e adicionar Mathlib como dependência.
2. Módulo B (Ising) primeiro, espelhando a ordem do lado Bend2: `Lattice`/`flip`/`magnetization`, depois `flip_twice_identity` e `flip_changes_magnetization_by_two`.
3. Módulo A (Circuito): `Circuit` como `List Edge`. Para `node_balance` e `preserves_node_balance`, testar primeiro se lemas prontos de `List.sum`/`Finset` do Mathlib resolvem a soma filtrada por nó antes de escrever indução manual — esse é o ponto do projeto onde a biblioteca de Lean deve ter maior vantagem sobre Bend2.
4. Enunciar e provar `loop_current_conserves_total`.
5. Para cada prova, registrar se ela foi fechada só com táticas automáticas (`simp`, `omega`, lemas de `Finset`) ou exigiu termos explícitos — esse dado alimenta a métrica de "automação vs. manual" do §8, e é especialmente relevante no Módulo A.
6. (Opcional) Explorar `Task`/threads do runtime de Lean para paralelizar `sweep` (Módulo B), como contraponto ao fork/join nativo de Bend2.

### Riscos específicos de Lean 4

- Risco oposto ao de Bend2: é tentador deixar Mathlib fazer todo o trabalho pesado de `Finset`/`List.sum` no Módulo A, o que tornaria a comparação injusta se não for documentado. Mitigação: registrar explicitamente quais lemas/táticas foram usados em cada prova.
- Nenhum paralelismo/GPU nativo comparável ao de Bend2 — a comparação de desempenho de execução paralela do Módulo B será necessariamente assimétrica (ver §8 e §10).
- Representar a grade do Módulo B como `List (List Spin)` (ou `Array`) tem as mesmas armadilhas de indexação e prova de limites que o lado Bend2 — não assumir que Mathlib torna isso automaticamente mais simples só porque ajuda mais no Módulo A.

## 8. Metodologia de comparação

Tabela preenchida em 2026-09-23, com as 5 leis fechadas dos dois lados
(0 `?TODO`, 0 `sorry`), números reais medidos via `bash bench/run.sh`
(script versionado, reproduzível — ver `bench/run.sh` e `bench/last_run.log`
para o output bruto desta rodada). Máquina/sessão únicas, conforme os
princípios abaixo. Ver [REPORT.md](REPORT.md) para a narrativa completa de
como cada prova foi construída (em especial §4, a ponte de contagem que
fechou o módulo Circuit).

| Eixo | Como medir | Bend2 | Lean 4 |
| --- | --- | --- | --- |
| Esforço de prova (LOC) | Linhas de arquivo de prova por módulo (Bend: `PROOF.bend` + as bibliotecas de lemas que importa; Lean: `Laws.lean`, que mistura enunciado+prova — ver nota) | Ising `PROOF.bend`: 474 LOC (3/3 leis). Circuit: `PROOF.bend` (73, cola) + `tests/circuit_assoc.bend` (499, lemas de associatividade/contagem) + `tests/sint_laws.bend` (308, associatividade geral de `SInt.add`) = 880 LOC (2/2 leis). Total: 1354 LOC | `Laws.lean`: 151 LOC para as 5 leis dos dois módulos, enunciado e prova juntos (sem separação LAWS/PROOF do lado Lean) |
| Automação vs. manual | % de provas fechadas só com tática automática (Lean) vs. termo explícito (ambos) | N/A (sem táticas) — 100% termo explícito em todas as provas, incluindo os lemas auxiliares de aritmética de `Nat`/`SInt` que Lean obteria de graça via `omega`/`ring` | 5/5 leis (100%) fechadas só com táticas (`induction`, `simp`, `omega`, `ring`, `split_ifs` etc.) — nenhuma prova precisou de termo explícito à mão. As duas mini-lemas auxiliares (`nodeBalanceDelta_nil/_cons`) fecham por `rfl` |
| Tempo de checagem | Tempo de `bend PROOF.bend` / `lake build` no mesmo hardware, 3 execuções | Ising: 4.55s / 2.26s / 2.44s. Circuit (cola): 3.28s / 1.61s / 2.29s. Circuit (lemas, `tests/circuit_assoc.bend`): 2.05s / 2.34s / 1.70s | `lake build Laws` (incremental, Mathlib já compilado): 413.40s / 30.90s / 20.88s — primeira execução paga recompilação de dependências no cache do Lake; a terceira (20.88s) é o número comparável a "checar uma mudança pontual" |
| Tempo de execução | `bend main.bend` (roda os dois módulos), 3 execuções | 2.79s / 2.07s / 1.58s | Não medido separadamente — o `Tests.lean` do projeto só tem `#eval`, que roda como efeito colateral do type-check/build (não há um binário compilado separado para cronometrar); ver `bench/run.sh` para a justificativa completa |
| Paralelismo CPU | Speedup medido com múltiplos núcleos (metodologia bend2.dev/learn/measuring-speedup) | Não implementado nesta sessão (fase avançada, PRD §9 Fase 4) | N/A ou via `Task`, se implementado |
| GPU | Speedup com `!`/Metal-CUDA vs. CPU | *N/A (sem GPU disponível, ver §10)* | N/A |
| Linhas de código (não-prova) | LOC dos tipos e funções puras | `ising/lattice.bend`: 93. `circuit/circuit.bend`: 152. `int.bend` (compartilhado): 52. Total: 297 | `Ising.lean`: 34. `Circuit.lean`: 41. Total: 75 |
| Curva de aprendizado | Tempo real gasto por quem implementa, em horas, por fase | Não cronometrado por fase (implementador único, sem baseline comparativo). Qualitativamente: a maior parte do tempo do lado Bend foi gasta reconstruindo, termo a termo, uma mini-biblioteca de aritmética de inteiros (associatividade, e um argumento de contagem para a ponte "circulação com +1 implica circulação com delta arbitrário") — não em entender a matemática das leis em si. Ver REPORT.md §4 e §7 (gotchas) | Não cronometrado por fase. Qualitativamente: o tempo do lado Lean foi dominado por iteração de táticas (`simp`/`omega` não fecham de primeira em boa parte das tentativas) e duas colisões de nome/design com o Mathlib (REPORT.md §5), não por design de tipos ou pela matemática |

### Leitura dos números (honesta, não um veredito)

- **Esforço de prova**: Bend precisou de ~9x mais LOC de prova que Lean para o mesmo conjunto de 5 leis, todas fechadas (1354 vs. 151) — e isso já é o custo final, não uma subestimativa. O número de Lean já inclui os enunciados das leis (que no lado Bend ficam em `LAWS.bend`, 33+57=90 LOC, fora dessa contagem), e mesmo assim Lean fica menor. A maior parte do custo extra do Bend (880 das 1354 linhas) é o módulo Circuit — reconstruir do zero associatividade de inteiros e um argumento de contagem que `omega`/`ring` do Lean resolvem em uma linha.
- **Automação**: confirma a hipótese do PRD §6/§10 — Lean fecha 100% das leis só com táticas, sem precisar de um termo manual em nenhum caso, enquanto Bend não tem essa opção por design. Esse é o eixo onde a assimetria estrutural (Mathlib/tactics vs. ownership/paralelismo) mais aparece nos números.
- **Tempo de checagem**: Bend é dramaticamente mais rápido por execução (~2-5s vs. dezenas de segundos mesmo incremental), mas essa comparação é injusta na direção oposta — o binário do Bend não carrega uma biblioteca do tamanho do Mathlib. Não é uma medida de "qual checker é mais eficiente", é uma medida de "qual dependência cada checagem paga".
- **Linhas não-prova**: bend precisou de ~4x mais LOC de tipos/funções (297 vs. 75), em grande parte porque `int.bend` (52 LOC) reimplementa um tipo inteiro assinado que Lean ganha de graça do core/Mathlib, e porque Bend não tem `List.filter`/`List.sum` no nível de conveniência de Lean, exigindo mais funções auxiliares escritas à mão (`node_balance.go`, `loop_pairs`, `touch_to.go`/`touch_from.go`, etc.).

### Princípios da comparação

- **Mesmo hardware, mesma máquina, mesma sessão** para todas as medições de tempo — cumprido (ver `bench/last_run.log`).
- **Mesmo autor** implementando os dois lados, para reduzir viés de familiaridade prévia com uma linguagem — cumprido.
- **Reportar honestamente as assimetrias estruturais** (Lean tem Mathlib e táticas; Bend2 tem paralelismo nativo) em vez de tentar neutralizá-las artificialmente — o objetivo é mostrar o trade-off real, não empatar os números. Ver "Leitura dos números" acima.
- Todas as medições devem ser reprodutíveis: script de benchmark versionado no repositório (`bench/run.sh`), não números soltos no relatório.

## 9. Roadmap e fases

| Fase | Entregável | Escopo |
| --- | --- | --- |
| 0 — Setup | Ambientes instalados e funcionando | Compilador Bend2 (fonte) + toolchain Lean 4/Lake/Mathlib; repositório criado |
| 1 — Núcleo mínimo | `flip_twice_identity` (Módulo B) provado nas duas linguagens | Tipos `Lattice`/`Spin`, `flip`, `magnetization`; 1 lei |
| 2 — Modelo completo | Todas as leis do §5 (Módulos A e B) provadas nas duas linguagens | `flip_changes_magnetization_by_two`, `preserves_lattice_shape`, `node_balance`/`preserves_node_balance`, `loop_current_conserves_total` |
| 3 — Comparação de dados | Tabela do §8 totalmente preenchida | Benchmarks de tempo de checagem/execução, contagem de LOC |
| 4 — Extensões opcionais | Paralelismo CPU no `sweep` do Módulo B medido (sem GPU, ver §10); visualização de ambos os módulos; lei `resume` para os dois módulos, se o tempo permitir | Só se as fases 1-3 confirmarem viabilidade dentro do prazo |
| 5 — Relatório final | Documento comparativo publicável (pode reaproveitar este PRD como base) | Síntese dos dados do §8 + conclusões qualitativas |

Cada fase só começa quando a anterior tem as leis daquela fase provadas nas **duas** linguagens — isso evita que uma implementação avance muito à frente da outra e distorça a comparação.

## 10. Riscos, limitações e perguntas em aberto

### Limitações técnicas conhecidas (herdadas das fontes)

- O checker de Bend2 tem divergências documentadas em relação à sua própria formalização em Lean — um bug do compilador pode invalidar uma prova fonte correta sem que isso apareça como erro óbvio.
- Ambos os módulos evitam ponto flutuante de propósito (ver §4), então a ausência de `F64` no Bend2 não afeta as leis propostas aqui — ela só limitaria uma extensão futura para corrente alternada (números complexos) ou Metropolis com temperatura real.
- As leis de invariante/limite, como no exemplo da galáxia, **não garantem que a simulação resolve o circuito corretamente ou reproduz a física do modelo de Ising real** — só que a operação de atualização (corrente de malha, flip de spin) respeita a invariante enunciada. O projeto precisa de testes numéricos separados (§3, critério 3) para não repetir esse mal-entendido.
- Comparar tempo de checagem/execução entre linguagens com runtimes tão diferentes (BendRT compilado para C vs. Lean com reference counting) é inerentemente ruidoso; tratar os números como indicativos, não definitivos.

### Perguntas em aberto (decidir antes da fase 1)

1. Resolvido: sem GPU dedicada disponível (notebook comum, sem Metal/CUDA). A fase 4 mede só paralelismo CPU; benchmarks de GPU ficam fora de alcance por ora.
2. O projeto será público desde o início (repositório aberto) ou só ao final?
3. Resolvido: uma única pessoa (eu, Claude) implementa os dois lados — reduz o risco de viés por familiaridade prévia citado no §6/§7, mas também significa que a métrica de "curva de aprendizado" do §8 não tem dois implementadores independentes para comparar.
4. Sem prazo-alvo fixo definido; fica a critério de quem implementa (eu) conforme o projeto avança, junto com a decisão de quando tornar o repositório público (pergunta 2).
5. Qual o tamanho da grade Ising (NxN) e do circuito (quantos nós/malhas) usar nos benchmarks de desempenho do §8, para que sejam grandes o bastante para mostrar diferença de paralelismo mas ainda checáveis em tempo razoável?

### Riscos de projeto

- **Maior risco**: subestimar o tempo de prova em Bend2 para `preserves_node_balance` (Módulo A) — indução sobre uma lista de arestas de tamanho variável, filtrando por nó, é estruturalmente mais complexa que os exemplos de árvore binária vistos até agora, e não há táticas para ajudar. Mitigação: a fase 1 usa só o Módulo B (grade fixa, sem indução sobre coleções de tamanho variável) para validar o pipeline antes de partir para o Módulo A.
- **Risco de viés**: se uma pessoa souber Lean bem e Bend2 mal (ou vice-versa), o "esforço de prova" medido reflete familiaridade, não a linguagem. Mitigação: registrar explicitamente o nível de experiência prévio de quem implementa cada lado.

## 11. Referências

- [What is Bend2?](https://bend2.dev/notes/what-is-bend2/) — visão geral da linguagem, tipos dependentes, ownership, paralelismo
- [How does Bend simulate a galaxy encounter?](https://bend2.dev/learn/galaxy-encounter/) — exemplo-fonte de inspiração deste PRD (7 leis, kick-drift-kick, paralelismo fork/join)
- [Bend2 vs Lean](https://bend2.dev/notes/bend2-vs-lean/) — comparação usada como base do §8
- [Bend2 syntax primer](https://bend2.dev/notes/bend2-syntax-primer/)
- [BendRT explained](https://bend2.dev/notes/bendrt-explained/)
- [Bend2 examples](https://bend2.dev/learn/examples.json) — inclui `inventory-conservation`, usado como modelo para as leis de conservação do §5
- [Bend official repository](https://github.com/bendlang/bend)
- [Lean 4 reference](https://lean-lang.org/doc/reference/latest/Introduction/)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)
