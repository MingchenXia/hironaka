import Hironaka.Resolution.HironakaG10HirFlatQuotient
import Hironaka.Resolution.HironakaG10FlatSimultaneousFlattener

/-!
# The canonical chart flattener is the flattener ideal of the chart map (lane G10H, run 0080)

A relative chart of a family over `(ℂ^d, 0)` is a germ ideal `I ⊆ 𝒪_{ℂ^{d+t},0}` (base coordinates
first); its structure map is `chartMap d t I : 𝒪_{ℂ^d,0} → 𝒪_{ℂ^{d+t},0} ⧸ I`.  The project's
canonical, presentation-independent flattener ideal `canonicalFlattenerIdeal d t I` (Hironaka's
Taylor-coefficient ideal `H` of Th. 1.14 at one point; H. Hironaka, *Flattening theorem in
complex-analytic geometry*, Amer. J. Math. 97 (1975), pp. 512–515) is exactly the flattener ideal
of this ring map in the sense of `HironakaG10HirFlatQuotient.IsFlattenerIdeal`: `chartMap` is flat
over the closed subgerm `V(a)` of the base iff `canonicalFlattenerIdeal d t I ≤ a`
(`isFlattenerIdeal_chartMap`).  After an analytic base change `φ : (ℂ^e,0) → (ℂ^d,0)` the
flattener of the base-changed chart is the pulled-back canonical ideal
(`isFlattenerIdeal_chartMap_baseChange`: Hironaka Th. 2.5, p. 529, at one point).

This is the ring-level bridge between the native germ flattener `IsGermFlattenerAt` (Hironaka
`HironakaG10HirGermFlattener`) and the chart-level flattener: combined with
`IsFlattenerIdeal.ringEquiv_comp`, `IsFlattenerIdeal.comp_ringEquiv` and
`IsFlattenerIdeal.quotient_base` it transports the canonical ideal to any native stalk map that is
identified with a chart map up to isomorphisms.
-/

set_option autoImplicit false

namespace Hironaka.HironakaG10HirChartFlattener

noncomputable section

open HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaActualAnalyticBaseChangeCoefficients HironakaChowOriginalFlattenerCoefficients
  HironakaChowPresentationIndependentFlattener HironakaG10FlatSimultaneousFlattener
  HironakaG10HirFlatQuotient

variable (d t : ℕ)

/-- The structure map `𝒪_{ℂ^d,0} → 𝒪_{ℂ^{d+t},0} ⧸ I` of a relative chart. -/
def chartMap (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    HolGerm (ComplexModel d) →+* HolGerm (ComplexModel (d+t)) ⧸ I :=
  (Ideal.Quotient.mk I).comp (tangentPullback d t).toRingHom

/-- **The canonical flattener ideal is the flattener ideal of the chart map.** -/
theorem isFlattenerIdeal_chartMap (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    IsFlattenerIdeal (chartMap d t I) (canonicalFlattenerIdeal d t I) := by
  intro a
  rw [chartMap, flat_quotMap_mk_comp_iff, ← flat_iff_canonicalFlattenerIdeal_le d t I a,
    ← RingHom.flat_algebraMap_iff]
  exact Iff.rfl

/-- Any flattener ideal of the chart map is the canonical one. -/
theorem eq_canonicalFlattenerIdeal (I : Ideal (HolGerm (ComplexModel (d+t))))
    {P : Ideal (HolGerm (ComplexModel d))} (hP : IsFlattenerIdeal (chartMap d t I) P) :
    P = canonicalFlattenerIdeal d t I :=
  hP.unique (isFlattenerIdeal_chartMap d t I)

/-- **Base change** (Hironaka Th. 2.5 at one point): after an analytic base change
`φ : (ℂ^e,0) → (ℂ^d,0)` the flattener of the base-changed chart is the pull-back of the canonical
flattener. -/
theorem isFlattenerIdeal_chartMap_baseChange (I : Ideal (HolGerm (ComplexModel (d+t))))
    (e : ℕ) (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in nhds (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0) :
    IsFlattenerIdeal (chartMap e t (Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I))
      (Ideal.map (compAlgHom φ hφ hφ0).toRingHom (canonicalFlattenerIdeal d t I)) := by
  intro a
  rw [chartMap, flat_quotMap_mk_comp_iff,
    ← flat_iff_map_canonicalFlattenerIdeal_le d t I e φ hφ hφ0 a, ← RingHom.flat_algebraMap_iff]
  exact Iff.rfl

end

end Hironaka.HironakaG10HirChartFlattener
