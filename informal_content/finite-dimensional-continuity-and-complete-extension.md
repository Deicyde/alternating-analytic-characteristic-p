# Finite-dimensional continuity and complete extension

Over a complete nontrivially normed field, a finite-dimensional normed space is complete and every linear map from it to a normed space is continuous. A linear map defined on a dense normed subspace with bound ‖Tx‖≤C‖x‖ extends uniquely to a Banach target with the same bound. A k-linear map on products of dense subspaces with bound C∏‖x_i‖ extends uniquely to the completed spaces with the same bound.

## Proof

The finite-dimensional facts are available as `LinearMap.continuous_of_finiteDimensional` and `FiniteDimensional.complete`. For linear extension use `LinearMap.extendOfNorm` and its norm/uniqueness lemmas. For multilinear extension, approximate each argument in its dense subspace. On a ball of radius ρ, telescoping across the k coordinates gives ‖M(x)-M(y)‖≤Cρ^(k-1)∑ᵢ‖x_i-y_i‖. This makes the output Cauchy and independent of approximants. Addition, scalar multiplication, the norm estimate and uniqueness pass to limits. The k=0 case is constant.
