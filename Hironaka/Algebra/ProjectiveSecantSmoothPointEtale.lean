import Hironaka.Algebra.ProjectiveSecantSeparablePoint
import Mathlib.RingTheory.Etale.Field
import Mathlib.Algebra.Algebra.Pi

/-!
# Actual algebra points of nonzero etale algebras over actual separably closed fields
-/

noncomputable section

namespace Hironaka.Algebra.ProjectiveSecant

universe u

/-- The actual native etale field-product equivalence internally produces an actual original algebra point from nonzeroness. -/
theorem exists_algHom_of_etale_sepClosed
    (K A : Type u) [Field K] [IsSepClosed K] [CommRing A] [Nontrivial A] [Algebra K A]
    [Algebra.Etale K A] : Nonempty (A →ₐ[K] K) := by
  let P : PrimeSpectrum A := Classical.choice inferInstance
  exact ⟨(Pi.evalAlgHom K (fun _ : PrimeSpectrum A => K) P).comp
    (Algebra.FormallyEtale.equivPiOfIsSepClosed K A).toAlgHom⟩

end Hironaka.Algebra.ProjectiveSecant
