# Infinite Ramsey theorem for fixed-size subsets

For n≥1, every map from the n-element subsets of ℕ to a finite color type has an infinite subset H on which all n-element subsets have the same color.

## Proof

Induct on n. For n=1 use the infinite finite-color pigeonhole principle. For the successor step recursively choose an increasing sequence a_i and nested infinite tails H_i above a_i so that for every n-subset s of the already chosen prefix, the color of s∪{x} is constant as x ranges over the current tail. Each stage has finitely many such s, so repeatedly replace the tail by an infinite monochromatic fiber. Define a coloring of the n-subsets of the chosen sequence using these stabilized extension colors. The induction hypothesis gives an infinite subset whose n-subsets have one stabilized color. For an (n+1)-subset, its largest element lies in the tail that stabilized its first n elements, so its original color is that common color. This also yields the finite-homogeneous-size version used by any finite implementation of the staircase test.
