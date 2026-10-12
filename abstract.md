We give a deterministic polynomial-time construction of arbitrarily large
finite simple subcubic expanders and prove that the same graphs have linear
treewidth. A fixed permutation seed, found by finite numerical enumeration,
is made lazy and powered, then used in an explicit numbered zig-zag tower.
Replacing each regular vertex by a path reduces the maximum degree to three.

With $D=120^{5760000}$ and $d=D^2$, the resulting graphs $H_k$ have
$N_k=d(D^4)^{k+1}$ vertices, edge expansion at least $1/(8d)$, and satisfy
$N_k\le(24d+1)(\operatorname{tw}(H_k)+1)$.
Consequently there are arbitrarily large subcubic graphs with treewidth at
least their order divided by $48d+2$.

The specified constructor accepts a unary order request $n$, outputs a
complete encoding of a graph of order between $n$ and $2dD^4(n+1)$, and is
computed by one deterministic Turing machine in polynomial time. The fixed
seed search has an enormous constant cost. The proofs include seed-search
correctness, spectral expansion, path replacement, the treewidth bound, and
polynomial-time computation of the actual graph encoding.
