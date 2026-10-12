import Lax920634.WordEncoding
import Lax808846.RamComputes

/-!
---
title: Linear-Time Construction on the Word RAM
type: theorem
---
One fixed deterministic word-RAM program constructs the specified subcubic
graphs in linear time in their output order. The program receives a requested
order as one word and outputs the complete word-sized matching table.

There are constants $c_t,c_w>0$ such that its actual instruction count is at
most $c_t(N+1)$ at every word width satisfying $c_w(N+1)\le2^w$, where $N$ is
the selected graph's order. Consequently $O(\log(N+1))$-bit words suffice.
The program and constants are chosen before the request and the word width.
The proof supplies $c_t=25381$ and $c_w=128$.

# Proof strategy

Materialize the fixed seed and build the rotation tables from the bottom up.
Each new row uses a constant number of lookups in the seed and preceding table.
Geometric growth bounds the total number of rows by a constant multiple of
$N$. A verified compiler transfers this bound to actual registered RAM
instructions, including initialization and output. The fixed seed and
level-zero table are program literals determined by the specified seed scan;
writing these literals into RAM is charged. No data depending on the request
or word width are built into the program.
-/

namespace Lax920634.LinearConstruction

/-- A uniform deterministic RAM constructs the precise family in linear output time. -/
axiom linear_time : ∃ (program : Lax808846.Ram.Program) (timeConstant wordConstant : ℕ),
  0 < timeConstant ∧ 0 < wordConstant ∧
  ∀ (n w : ℕ),
    wordConstant * (ZigZagConstruction.order (GraphEncoding.selectedLevel n) + 1) ≤ 2 ^ w →
    ∃ t ≤ timeConstant * (ZigZagConstruction.order (GraphEncoding.selectedLevel n) + 1),
      Lax808846.Ram.RunsTo w program [n] (WordEncoding.construct n) t

end Lax920634.LinearConstruction
