/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Support.RealDomainLocalCoherenceExact
import Hironaka.Resolution.HironakaRelativeNormalDeformationInitialRelations

/-! # Whole original initial relations in the actual real central family
Actual finite generation near zero supplies every origin dictionary.
The existing graph ideal/scaling/parameter-colon/central definitions
are retained. Original geometric/coherent input internally supplies
the real domains, selected index and entire initial-ideal inclusion.
Complete mathematics precedes this source; global model coherence is
neither a premise nor a conclusion of the original-input endpoint.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainInitialRelations
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  OkaCoherence HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainSaturation
 HironakaRelativeNormalCoherentSaturation
  HironakaRelativeNormalDeformationSaturation HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalMonomialBasis
  HironakaHolomorphicJetChartInvariance RelativePrincipalizationSpan InvertibleIdealQuotient



/-- The literal WHOLE origin ideal has the actual representative dictionary from local generation alone. -/
theorem mk_mem_originalOriginIdeal_iff_of_local {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (hI : IdealFGAt I.mem 0) {f : ComplexModel n → ℂ} (hf : HolAt f 0) :
    HolGerm.mk f hf ∈ originalCoherentOriginIdeal I ↔ I.mem 0 f := by
  classical
  obtain ⟨U, hU, h0U, μ, hμ, S, hS, hgen⟩ := hI
  let := hμ
  have hS0 : ∀ i, HolAt (S i) 0 := fun i => holAt_of_differentiableOn hU (hS i) h0U
  let K := Ideal.span (range fun i => HolGerm.mk (S i) (hS0 i))
  have hdict (g : ComplexModel n → ℂ) (hg : HolAt g 0) : I.mem 0 g ↔ HolGerm.mk g hg ∈ K :=
    (hgen 0 h0U g).trans (inSpanAt_zero_iff_mem_origin_span S hS0 hg)
  have hK : originalCoherentOriginIdeal I = K := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro g ⟨a, ha, hIa, rfl⟩
      exact (hdict a ha).mp hIa
    · apply Ideal.span_le.mpr
      rintro g ⟨i, rfl⟩
      apply Ideal.subset_span
      exact ⟨S i, hS0 i, (hgen 0 h0U _).mpr (inSpanAt_self hS0 i), rfl⟩
  rw [hK]
  exact (hdict f hf).symm

end
end Hironaka.HironakaSmoothCentreRealDomainInitialRelations
