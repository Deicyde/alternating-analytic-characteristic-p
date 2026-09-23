# Vector-valued polynomial identity principle

Let L be an infinite field and Y an L-vector space. If a polynomial g(λ)=∑_α λ^α y_α with finitely many coefficients vanishes for every λ∈L^m, then y_α=0 for every α.

## Proof

The finitely many coefficients span a finite-dimensional subspace U of Y. Apply the basis coordinate functionals on U. Each scalar multivariate polynomial is zero as a function on an infinite field, hence is the zero polynomial; this is `MvPolynomial.funext`. Every coordinate of every y_α is zero, so all y_α vanish.
