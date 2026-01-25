import PrimeNumberTheoremAnd.ArtinRepresentation
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
## Artin characters (algebraic layer)

Sharifi’s notes phrase Artin L-functions in terms of **characters** `χ` of representations.
This file defines the character of an Artin representation `ρ` as the matrix trace, and
records its invariance under conjugation, so it descends to a function on `ConjClasses G`.

No analytic input appears here.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

namespace ArtinLSeries

namespace ArtinRep

variable {G : Type*} [Group G]

variable (ρ : PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep G)

/-- The character of an Artin representation: `χ(g) = tr(ρ(g))`. -/
noncomputable def character (g : G) : ℂ :=
  Matrix.trace (ρ.mat g)

lemma character_eq_of_isConj {g h : G} (hg : IsConj g h) :
    ρ.character g = ρ.character h := by
  classical
  rcases hg with ⟨c, hc⟩
  -- Convert semiconjugation into the usual conjugation formula.
  have hconj : (↑c : G) * g * (↑c : G)⁻¹ = h := by
    have := congrArg (fun t : G => t * (↑(c⁻¹) : G)) hc
    simpa [mul_assoc] using this
  -- Let `u` be the unit matrix `ρ(c)`.
  let u : (Matrix ρ.n ρ.n ℂ)ˣ := (ρ.ρ (↑c : G))
  -- Rewrite `ρ(h)` as a conjugate of `ρ(g)` by `u`, then apply trace invariance.
  have hmat :
      ρ.mat h = (↑u : Matrix ρ.n ρ.n ℂ) * ρ.mat g * (↑u⁻¹ : Matrix ρ.n ρ.n ℂ) := by
    -- `ρ` is a group hom into units, so it respects multiplication and inverses.
    -- Unfold `mat` and use `hconj`.
    calc
      ρ.mat h = ρ.mat ((↑c : G) * g * (↑c : G)⁻¹) := by simp [hconj]
      _ = (↑u : Matrix ρ.n ρ.n ℂ) * ρ.mat g * (↑u⁻¹ : Matrix ρ.n ρ.n ℂ) := by
            -- `simp` knows how to coerce `u` and use `map_mul`/`map_inv`.
            simp [ArtinRep.mat, u, map_mul, mul_assoc]
  -- Now use `trace_units_conj`.
  simpa [ArtinRep.character, hmat] using (Matrix.trace_units_conj u (ρ.mat g)).symm

/--
The character as a class function on `ConjClasses G`.
-/
noncomputable def characterClass : ConjClasses G → ℂ :=
  Quotient.lift (fun g : G => ρ.character g) (by
    intro g h hg
    exact ρ.character_eq_of_isConj (g := g) (h := h) hg)

@[simp] lemma characterClass_mk (g : G) :
    ρ.characterClass (ConjClasses.mk g) = ρ.character g :=
  rfl

end ArtinRep

end ArtinLSeries

end PrimeNumberTheoremAnd

