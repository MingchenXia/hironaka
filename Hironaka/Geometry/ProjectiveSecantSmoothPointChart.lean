import Hironaka.Algebra.ProjectiveSecantSmoothPointEtale
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Smooth.Flat

/-!
# Actual original etale polynomial charts have rational points over their separably closed coefficient field
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace Hironaka.Geometry.ProjectiveSecant

open Algebra.ProjectiveSecant

universe u

/-- The native open image of the SAME original etale chart internally produces a rational polynomial point; its actual tensor fibre then produces a whole original algebra point. -/
theorem exists_algHom_of_etale_polynomial_sepClosed
    (K A : Type u) [Field K] [IsSepClosed K] [CommRing A] [Nontrivial A] [Algebra K A]
    (n : ℕ) [Algebra (MvPolynomial (Fin n) K) A]
    [IsScalarTower K (MvPolynomial (Fin n) K) A]
    [Algebra.Etale (MvPolynomial (Fin n) K) A] : Nonempty (A →ₐ[K] K) := by
  let R := MvPolynomial (Fin n) K
  let φ := algebraMap R A
  let Q : PrimeSpectrum A := Classical.choice inferInstance
  have hop : IsOpenMap (PrimeSpectrum.comap φ) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  have ho : IsOpen (Set.range (PrimeSpectrum.comap φ)) := hop.isOpen_range
  obtain ⟨_, ⟨F, rfl⟩, hQF, hF⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp
    ho (PrimeSpectrum.comap φ Q) (Set.mem_range_self Q)
  have hne : F ≠ 0 := by
    intro h
    exact hQF (h ▸ (PrimeSpectrum.comap φ Q).asIdeal.zero_mem)
  let : Infinite K := separablyClosed_infinite K
  obtain ⟨v, hv⟩ : ∃ v : Fin n → K, MvPolynomial.eval v F ≠ 0 := by
    by_contra! h
    apply hne
    exact MvPolynomial.funext fun v => by simpa only [map_zero] using h v
  let e : R →ₐ[K] K := MvPolynomial.aeval v
  have hpoint : PrimeSpectrum.comap e.toRingHom (⊥ : PrimeSpectrum K) ∈ PrimeSpectrum.basicOpen F := by
    change MvPolynomial.eval v F ∉ (⊥ : Ideal K)
    simpa only [Ideal.mem_bot] using hv
  obtain ⟨q, hq⟩ := hF hpoint
  let : Algebra R K := e.toRingHom.toAlgebra
  let : IsScalarTower K R K := IsScalarTower.of_algebraMap_eq fun c => (e.commutes c).symm
  let B := K ⊗[R] A
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R K A)
  obtain ⟨b, _, _⟩ := Scheme.exists_preimage_of_isPullback hpb
    (⊥ : PrimeSpectrum K) q hq.symm
  let : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨b⟩
  obtain ⟨χ⟩ := exists_algHom_of_etale_sepClosed K B
  exact ⟨χ.comp ((Algebra.TensorProduct.includeRight : A →ₐ[R] B).restrictScalars K)⟩

end Hironaka.Geometry.ProjectiveSecant
