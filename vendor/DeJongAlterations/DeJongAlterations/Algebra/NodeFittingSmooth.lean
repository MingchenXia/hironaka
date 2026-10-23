import DeJongAlterations.Algebra.NodeFittingClosedRegular
import DeJongAlterations.Geometry.RegularSmooth
import Mathlib.RingTheory.Localization.Ideal

/-! # Every actual smooth prime of an affine curve avoids the full original Fitting locus -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingSmooth

open NodeFittingModule

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual localization prime-comap embedding bounds its native dimension. -/
theorem ringKrullDim_localization_le (A S : Type*) [CommRing A] [CommRing S]
    [Algebra A S] (M : Submonoid A) [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim A := by
  apply Order.krullDim_le_of_strictMono
    (fun p : PrimeSpectrum S ↦ (PrimeSpectrum.comap (algebraMap A S)) p)
  intro p q hpq
  exact (IsLocalization.orderEmbedding M S).strictMono hpq

variable (K A : Type*) [Field K] [PerfectField K] [CommRing A] [Algebra K A]
  [Algebra.FiniteType K A]

/-- On an actual smooth affine curve, the ENTIRE original differential Fitt₁ is the unit ideal. -/
theorem smooth_fitting_one_eq_top [Algebra.Smooth K A] (hdim : ringKrullDim A ≤ 1) :
    letI := NodeFittingClosedRegular.affineOmega_finitePresentation K A
    fittingIdeal (R := A) (M := KaehlerDifferential K A) 1 = ⊤ := by
  let := NodeFittingClosedRegular.affineOmega_finitePresentation K A
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let : IsRegularRing A := Geometry.RegularSmooth.isRegularRing_of_smooth K A
  by_contra h
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ h
  let : m.IsMaximal := hm
  let : IsRegularLocalRing (Localization.AtPrime m) :=
    (isRegularRing_iff.mp (inferInstance : IsRegularRing A)) m
  exact NodeFittingClosedRegular.affineOmega_fitting_not_le_maximal K A m hdim hJm

/-- An arbitrary actual native smooth prime, including a nonclosed one, avoids the full original ideal. -/
theorem fitting_not_le_of_isSmoothAt (p : Ideal A) [p.IsPrime] [Algebra.IsSmoothAt K p]
    (hdim : ringKrullDim A ≤ 1) :
    letI := NodeFittingClosedRegular.affineOmega_finitePresentation K A
    ¬ fittingIdeal (R := A) (M := KaehlerDifferential K A) 1 ≤ p := by
  let := NodeFittingClosedRegular.affineOmega_finitePresentation K A
  let : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨c, hc, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K p
  let S := Localization.Away c
  let : Algebra.IsStandardSmooth K S := hsm
  let := NodeFittingClosedRegular.affineOmega_finitePresentation K S
  have hdimS : ringKrullDim S ≤ 1 :=
    (ringKrullDim_localization_le A S (Submonoid.powers c)).trans hdim
  have hmap := NodeFittingOmega.fittingIdeal_localization K A S (Submonoid.powers c) 1
  rw [smooth_fitting_one_eq_top K S hdimS] at hmap
  have hdisj : Disjoint (Submonoid.powers c : Set A) (p : Set A) := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  have hpS : (p.map (algebraMap A S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers c) S p inferInstance hdisj
  intro hp
  have hle := Ideal.map_mono (f := algebraMap A S) hp
  rw [hmap] at hle
  exact hpS.ne_top (top_le_iff.mp hle)

end DeJongAlterations.Algebra.NodeFittingSmooth
