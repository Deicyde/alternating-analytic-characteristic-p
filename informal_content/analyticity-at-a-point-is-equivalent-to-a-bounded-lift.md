# Analyticity at a point is equivalent to a bounded lift

For k≥1, Q has a bounded k-linear lift P with P(f,…,f)=Q(f) if and only if Q is analytic at some point, if and only if it is analytic at every point. A lift gives a finite power series with infinite radius at every point. For every analytic expansion at f₀, its degree-k coefficient is a lift. If no lift exists then ContDiffAt K ω Q f₀ fails at every f₀. No completeness or characteristic assumption is added.

## Proof

Given P, expand P(f₀+y,…,f₀+y) by subsets of slots; the degree-r coefficient is bounded by binom(k,r)‖P‖‖f₀‖^(k-r), and all higher coefficients vanish. Conversely embed alternating maps isometrically into continuous multilinear maps. Along f₀+th, the ambient precomposition is a polynomial in t of degree at most k, with top coefficient Q(h). Compare this polynomial to the analytic series along the same line. One-variable uniqueness applies without completeness: if a norm-bounded convergent series is zero near 0, choose its least nonzero coefficient, divide by the corresponding t-power, bound the tail geometrically and let nonzero t tend to 0. The degree-k diagonal of the original analytic coefficient is Q(h); h=0 follows from k≥1. Analyticity implied by ContDiffAt K ω gives the last assertion.
