We give a deterministic linear-time word-RAM construction of arbitrarily large
finite simple subcubic expanders and prove that the same graphs have linear
treewidth. A fixed permutation seed, found by finite numerical enumeration,
is made lazy and powered, then used in an explicit numbered zig-zag tower.
Replacing each regular vertex by a path reduces the maximum degree to three.

With $D=120^{5760000}$ and $d=D^2$, the resulting graphs $H_k$ have
$N_k=d(D^4)^{k+1}$ vertices, edge expansion at least $1/(8d)$, and satisfy
$N_k\le(24d+1)(\operatorname{tw}(H_k)+1)$.
Consequently there are arbitrarily large subcubic graphs with treewidth at
least their order divided by $48d+2$.

The size selector chooses an order between $n$ and $2dD^4(n+1)$.
One fixed program in the registered Lax word-RAM model, on the one-word
input $[n]$, outputs a header and one matching endpoint per vertex.
Decoding this table gives exactly $H_k$ at the selected level. The program
executes at most $25381(N+1)$ instructions whenever $128(N+1)\le2^w$.
It builds successive rotation tables from the bottom up; geometric growth
bounds the total work and storage linearly in the final order $N$.

The fixed seed is chosen by a specified deterministic finite scan. Its data
are literals in the fixed program; their initialization is included in the
instruction bound. The construction has enormous fixed constants and is
theoretical. A separate binary encoding retains the deterministic
polynomial-time Turing-machine guarantee.
