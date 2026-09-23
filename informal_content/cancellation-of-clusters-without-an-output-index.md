# Cancellation of clusters without an output index

Let finite families C_j of clusters be disjoint as families and let all clusters occurring be pairwise disjoint. Set u_j=∑_{C∈C_j}s_C and v_j=∑_{C∈C_j}w_C. Choose C_j∈C_j and output c=(C₁(0),…,C_k(0)). Then Ω(Ψ(u;v))(c)=χ(C₁,…,C_k).

## Proof

Group the finite unit-vector expansion by the operator and vector cluster assigned to each slot j. If an occupied cluster Γ is not an output cluster, it belongs to exactly one family, so only a_j and/or y_j can lie there. Hold all other positions fixed. If only a_j lies in Γ the pattern is independent of its position and the group vanishes by ∑s_i=0. If only y_j lies there use ∑w_i=0. If both lie there, the pattern depends only on i<j, i=j or i>j; all three weighted partial sums vanish by the four-position identities. Thus all groups containing a free cluster cancel. In any remaining group the only available output cluster in family j is C_j, so both indices in slot j use C_j; this surviving group is χ(C₁,…,C_k).
