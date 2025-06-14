import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.Algebra.InfiniteSum
import Mathlib.Topology.Algebra.Module.InfiniteSum

/-!
# Checking Available Euler Product Lemmas

Let's see what Mathlib provides for the Euler product.
-/

open Complex Real BigOperators

-- From the search results, these should exist:
#check riemannZeta_eulerProduct
#check zeta_eq_tsum_one_div_nat_cpow
#check Complex.summable_natPrime_rpow_neg

-- Let's also check for product convergence
#check Multipliable
#check tprod_eq_prod_indicator
#check Multipliable.prod_factor

-- For our specific needs
variable (s : ℂ) (hs : 1 < s.re)

-- The Euler product should give us something like:
-- riemannZeta s = ∏' p : Nat.Primes, (1 - p^(-s))⁻¹

-- We need the inverse:
-- (riemannZeta s)⁻¹ = ∏' p : Nat.Primes, (1 - p^(-s))
