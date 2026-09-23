# Four-position cancellation weights

Let R be a commutative ring. On Fin 4, indexed here by 0,1,2,3, put s=(1,0,-1,0) and w=(1,-1,1,-1). Then

- sum_i s_i = sum_i w_i = 0;
- sum_i s_i*w_i = 0;
- sum_{i<j} s_i*w_j = sum_{i>j} s_i*w_j = 0;
- s_0*w_0 = 1.

These identities remain valid in characteristic 2, where -1=1. They are the cancellation weights for one operator position and one vector position within a four-element cluster.

## Proof

Expand all four-position sums. The individual sums are 1-1 and 1-1+1-1. The diagonal sum is 1-1. The strictly increasing sum is s_0(w_1+w_2+w_3)+s_2*w_3=(-1)+1=0. The strictly decreasing sum is s_2(w_0+w_1)=-(1-1)=0. Finally the distinguished product is 1*1=1. All equalities are ring identities over the integers, so no characteristic or finiteness assumption is used.
