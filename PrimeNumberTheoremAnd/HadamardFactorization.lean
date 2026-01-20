/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Architect
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Hadamard
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.RiemannZetaHadamard
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ZetaFiniteOrder

blueprint_comment /--

In this file, we expose Hadamard factorization API in the style of
Tao’s notes (246B, Theorem 22 in `PrimeNumberTheoremAnd/hadamard.md`).

Tao formulates “order at most `ρ`” using an \(ε\)-family of bounds of the shape
\(|f(z)| \le C_ε \exp(|z|^{ρ+ε})\).  In this repository we prove a matching `ε`-family version
(`Complex.Hadamard.hadamard_factorization_of_order`), stated with the standard harmless
normalization `(1 + ‖z‖)` in place of `|z|`, and proved by reducing to the core growth-based theorem
`Complex.Hadamard.hadamard_factorization_of_growth` (which assumes a single explicit bound on
`Real.log (1 + ‖f z‖)`).

-/

noncomputable section

open scoped Real

namespace PrimeNumberTheoremAnd

/-!
We provide blueprint-facing entry points for the intrinsic Hadamard factorization theorem.

The **general** theorem is `Complex.Hadamard.hadamard_factorization_of_order`, which factors an
entire function under Tao’s “finite order” hypothesis formulated as an `ε`-family of growth bounds
(246B, Theorem 22).

The **zeta** corollary is `Riemann.completedRiemannZeta₀_hadamard_factorization_intrinsic`,
obtained by combining the general theorem with the growth estimate proved in
`Mathlib/Analysis/Complex/ZetaFiniteOrder.lean`.
-/

@[blueprint
  "hadamard_factorization_of_order"
  (title := "Hadamard factorization (intrinsic, Tao-style finite order)")
  (statement := /--
    Let `f : ℂ → ℂ` be entire and not identically zero, and assume a global growth bound
    of Tao’s “order at most `ρ`” form: for every `ε > 0` there is `Cε > 0` such that
    `‖f z‖ ≤ exp (Cε * (1 + ‖z‖) ^ (ρ + ε))`.

    Then `f` admits a Hadamard factorization
    \( f(z) = \exp(P(z)) \, z^{m} \, \prod E_d(z/a)\),
    with `d = ⌊ρ⌋`, `deg P ≤ d`, and where the canonical product is indexed intrinsically by the
    divisor (zeros with multiplicity), rather than by choosing an external enumeration of zeros.
  --/)
  (latexEnv := "theorem")]
theorem hadamard_factorization_of_order {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder :
      ∀ ε : ℝ, 0 < ε →
        ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε))) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            Complex.Hadamard.divisorCanonicalProduct (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order (f := f) (ρ := ρ) hρ hentire hnot horder)

@[blueprint
  "completedRiemannZeta0_hadamard_factorization_intrinsic"
  (title := "Hadamard factorization for the completed Riemann zeta function")
  (statement := /--
    The entire completed Riemann zeta function `completedRiemannZeta₀` admits an intrinsic Hadamard
    factorization with genus `1` and an exponential factor of degree at most `1`.
  --/)
  (latexEnv := "theorem")]
theorem completedRiemannZeta₀_hadamard_factorization_intrinsic :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ 1 ∧
      ∀ z : ℂ,
        completedRiemannZeta₀ z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
            Complex.Hadamard.divisorCanonicalProduct 1 completedRiemannZeta₀ (Set.univ : Set ℂ) z := by
  simpa using Riemann.completedRiemannZeta₀_hadamard_factorization_intrinsic

end PrimeNumberTheoremAnd
