# Staircase rank forces adjacent cluster invariance

Assume sdim(Ψ(u;v))≤d for all finitely supported inputs whose coordinates are in {0,1,-1}. If τ' exchanges two adjacent positions in the cluster order permutation τ, then χ(τ)=χ(τ').

## Proof

Choose m=d+2. Fix all clusters outside the two adjacent ranks and place A₁<B₁<A₂<B₂<⋯<A_m<B_m between them. Let the two corresponding input families be all A_i and all B_j; other families are singleton. The resulting input vectors still have entries in {0,1,-1}, so ω=Ψ(u;v) has support dimension≤d. Vary the two output coordinates along A_i(0),B_j(0). Cancellation identifies the resulting m×m matrix with χ(τ) on and above the diagonal and χ(τ') below it. It is a submatrix of a flattening, so has rank≤d. If δ=χ(τ)-χ(τ')≠0, subtracting the rank-at-most-one constant matrix leaves δ times the upper-unitriangular matrix [i≤j], of full rank m. Rank subadditivity then forces rank M≥m-1=d+1, contradiction.
