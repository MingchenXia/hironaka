/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Extension.Generators
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# An actual polynomial-local presentation of a local essentially finite-type algebra
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.RegularSmoothConversePresentation

universe u

/-- Essential finite type and actual locality construct an actual finite-variable polynomial-local surjection. -/
theorem exists_polynomial_local_surjection (K S : Type u) [CommRing K] [CommRing S]
    [Algebra K S] [IsLocalRing S] [Algebra.EssFiniteType K S] :
    ∃ (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) K))
      (f : Localization.AtPrime p.asIdeal →ₐ[K] S), Function.Surjective f := by
  let A := Algebra.EssFiniteType.subalgebra K S
  let p : PrimeSpectrum A := ⟨(maximalIdeal S).comap (algebraMap A S), inferInstance⟩
  have hM : Algebra.EssFiniteType.submonoid K S = p.asIdeal.primeCompl := by
    ext a
    change IsUnit (algebraMap A S a) ↔ algebraMap A S a ∉ maximalIdeal S
    simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]
  have : IsLocalization.AtPrime S p.asIdeal := by
    change IsLocalization p.asIdeal.primeCompl S
    rw [← hM]
    infer_instance
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType K A)
  let q : PrimeSpectrum (MvPolynomial (Fin n) K) := ⟨p.asIdeal.comap φ.toRingHom, inferInstance⟩
  let ψ := Localization.localAlgHom q.asIdeal p.asIdeal φ rfl
  have hψ : Function.Surjective ψ := RingHom.surjective_localRingHom_of_surjective φ.toRingHom hφ p.asIdeal
  let e := IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) S
  exact ⟨n, q, (e.restrictScalars K).toAlgHom.comp ψ, e.surjective.comp hψ⟩

end DeJongAlterations.Algebra.RegularSmoothConversePresentation
