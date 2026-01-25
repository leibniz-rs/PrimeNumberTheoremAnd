import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
## Chebotarev reduction: degree-one primes (inertia degree = 1)

Sharifi’s reduction step uses primes `𝔓` of an intermediate field `E/K` of **degree 1** over `K`.
In algebraic terms this is the condition that the residue field extension has degree `1`, i.e.
the inertia degree is `1`.

We package this condition in a reusable definition based on mathlib’s
`Ideal.inertiaDeg` API (`Mathlib.NumberTheory.RamificationInertia.Basic`).
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

namespace DegreeOne

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A prime ideal `P : Ideal S` has degree `1` over `p : Ideal R` if its inertia degree is `1`. -/
def IsDegreeOneOver (p : Ideal R) (P : Ideal S) : Prop :=
  p.inertiaDeg P = 1

@[simp] lemma isDegreeOneOver_iff (p : Ideal R) (P : Ideal S) :
    IsDegreeOneOver (p := p) P ↔ p.inertiaDeg P = 1 := Iff.rfl

lemma isDegreeOneOver_iff_finrank
    (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsMaximal] :
    IsDegreeOneOver (p := p) P ↔ Module.finrank (R ⧸ p) (S ⧸ P) = 1 := by
  -- Use the standard inertia-degree formula under the `LiesOver` hypothesis.
  simpa [IsDegreeOneOver] using congrArg (fun n : ℕ => n = 1) (_root_.Ideal.inertiaDeg_algebraMap (p := p) (P := P))

end DegreeOne

end Chebotarev

end PrimeNumberTheoremAnd

