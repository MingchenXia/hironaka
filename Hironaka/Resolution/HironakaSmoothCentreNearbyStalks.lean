/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreCoherentDomain

/-! # Actual fixed-flattening whole original stalks at every nearby point
Each nearby equivalence is built from the genuine translated nonlinear maps
on their real open domains. Original regularity and coherence internally
supply the SAME actual U and the whole original chart-stalk dictionary.
Complete mathematics precedes this source in the matching Mathematics.tex.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreNearbyStalks
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRelativeIdeal
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  InvertibleIdealQuotient OkaRelationSheaf
variable {n : ℕ}

/-- The actual translated nonlinear equivalence at each real target point. -/
def actualNearbyEquiv {p0 : ComplexModel n} (Φ : LocalHolomorphicEquivAt p0)
    (a : ComplexModel n) (ha : a ∈ Φ.target) : LocalHolomorphicEquivAt (0 : ComplexModel n) where
  source := (fun z => z + Φ.invFun a) ⁻¹' Φ.source
  target := (fun w => w + a) ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source.preimage (continuous_id.add continuous_const)
  isOpen_target := Φ.isOpen_target.preimage (continuous_id.add continuous_const)
  center_mem_source := by simpa only [mem_preimage, zero_add] using Φ.mapsTo_invFun ha
  toFun := fun z => Φ.toFun (z + Φ.invFun a) - a
  invFun := fun w => Φ.invFun (w + a) - Φ.invFun a
  toFun_holomorphic := by
    intro z hz
    exact (((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hz)).comp z
      (differentiableAt_id.add_const (Φ.invFun a))).sub_const a).differentiableWithinAt
  invFun_holomorphic := by
    intro w hw
    exact (((Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hw)).comp w
      (differentiableAt_id.add_const a)).sub_const (Φ.invFun a)).differentiableWithinAt
  mapsTo_toFun := by
    intro z hz
    change Φ.toFun (z + Φ.invFun a) - a + a ∈ Φ.target
    rw [sub_add_cancel]
    exact Φ.mapsTo_toFun hz
  mapsTo_invFun := by
    intro w hw
    change Φ.invFun (w + a) - Φ.invFun a + Φ.invFun a ∈ Φ.source
    rw [sub_add_cancel]
    exact Φ.mapsTo_invFun hw
  left_inv := by
    intro z hz
    rw [sub_add_cancel, Φ.left_inv _ hz, add_sub_cancel_right]
  right_inv := by
    intro w hw
    rw [sub_add_cancel, Φ.right_inv _ hw, add_sub_cancel_right]

theorem actualNearbyEquiv_zero {p0 : ComplexModel n} (Φ : LocalHolomorphicEquivAt p0)
    (a : ComplexModel n) (ha : a ∈ Φ.target) : (actualNearbyEquiv Φ a ha).toFun 0 = 0 := by
  change Φ.toFun (0 + Φ.invFun a) - a = 0
  rw [zero_add, Φ.right_inv a ha, sub_self]

/-- Entire actual ambient algebra equivalence from the real nearby recentered map. -/
def actualNearbyGermEquiv {p0 : ComplexModel n} (Φ : LocalHolomorphicEquivAt p0)
    (a : ComplexModel n) (ha : a ∈ Φ.target) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
  localGermAlgEquiv (actualNearbyEquiv Φ a ha) (actualNearbyEquiv_zero Φ a ha)

section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
theorem actualNearbyPoint_mem_chart_source (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (a : ComplexModel n) (ha : a ∈ Φ.target) :
    actualFlatteningInverseMap x Φ a ∈ (chartAt (ComplexModel n) x).source :=
  (chartAt (ComplexModel n) x).map_target (hsrc (Φ.mapsTo_invFun ha))

omit [IsComplexManifold n M] in
theorem actualNearbyPoint_chart_value (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (a : ComplexModel n) (ha : a ∈ Φ.target) :
    chartAt (ComplexModel n) x (actualFlatteningInverseMap x Φ a) = Φ.invFun a :=
  (chartAt (ComplexModel n) x).right_inv (hsrc (Φ.mapsTo_invFun ha))

/-- Every literal pulled and translated original generator becomes its original nearby chart germ. -/
theorem actualNearbyGermEquiv_original_function (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (a : ComplexModel n) (ha : a ∈ Φ.target) (G : M → ℂ)
    (hG : HolomorphicAt n G (actualFlatteningInverseMap x Φ a))
    (hH : HolAt ((G ∘ actualFlatteningInverseMap x Φ) ∘ actualAffineTranslation n a) 0) :
    actualNearbyGermEquiv Φ a ha
      (HolGerm.mk ((G ∘ actualFlatteningInverseMap x Φ) ∘ actualAffineTranslation n a) hH) =
      chartTranslatedGerm x (actualFlatteningInverseMap x Φ a)
        (actualNearbyPoint_mem_chart_source x Φ hsrc a ha) G hG := by
  unfold actualNearbyGermEquiv
  rw [localGermAlgEquiv_mk]
  simp only [chartTranslatedGerm, translatedGerm]
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards [(actualNearbyEquiv Φ a ha).isOpen_source.mem_nhds
    (actualNearbyEquiv Φ a ha).center_mem_source] with z hz
  change G ((chartAt (ComplexModel n) x).symm
      (Φ.invFun (a + (Φ.toFun (z + Φ.invFun a) - a)))) =
    G ((chartAt (ComplexModel n) x).symm
      (z + chartAt (ComplexModel n) x (actualFlatteningInverseMap x Φ a)))
  rw [add_comm a, sub_add_cancel, Φ.left_inv _ hz, actualNearbyPoint_chart_value x Φ hsrc a ha]

/-- Actual finite original membership at a real point identifies the whole fixed-chart stalk. -/
theorem wholeChartStalkIdeal_eq_span_of_original_generators {N : ℕ}
    (A : GermIdeal n M) (x y : M) (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (G : Fin N → M → ℂ) (hG : ∀ i, HolomorphicAt n (G i) y)
    (hgen : ∀ f, A.mem y f ↔ IsInSpanAt (n := n) (· ∈ range G) y f) :
    wholeChartStalkIdeal A x y hy =
      Ideal.span (range fun i => chartTranslatedGerm x y hy (G i) (hG i)) := by
  classical
  let H : Fin N → ComplexModel n → ℂ := fun i z => G i ((chartAt (ComplexModel n) x).symm z)
  have hH (i : Fin N) :
      ∀ᶠ z in 𝓝 ((chartAt (ComplexModel n) x) y), DifferentiableAt ℂ (H i) z :=
    CartanLocalReduction.holAt_comp_chart_symm hy (hG i)
  have hdict (f : M → ℂ) (hf : HolomorphicAt n f y) :
      A.mem y f ↔ chartTranslatedGerm x y hy f hf ∈
        Ideal.span (range fun i => chartTranslatedGerm x y hy (G i) (hG i)) :=
    (hgen f).trans
      ((ManifoldFiniteSpanChartTransport.isInSpanAt_comp_chartSymm_iff hy G f).trans
        (isInSpanAt_iff_translatedGerm_mem H _ hH
          (CartanLocalReduction.holAt_comp_chart_symm hy hf)))
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f, hf, hmem, rfl⟩
    exact (hdict f hf).mp hmem
  · apply Ideal.span_le.mpr
    rintro g ⟨i, rfl⟩
    apply Ideal.subset_span
    exact ⟨G i, hG i, (hgen (G i)).mpr
      (CoherentIdealColon.isInSpanAt_range_self hG i), rfl⟩

/-- Original geometry and coherence internally give EVERY nearby whole nonlinear map and comap. -/
theorem exists_original_regular_same_open_nearby_whole_stalk_dictionary {d : ℕ}
    (C : Set M) (x : M) (hreg : RegularAtDim (n := n) C x d)
    (A : GermIdeal n M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x),
      ∃ hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n d)) ∧
      ∃ U : Set (ComplexModel n), IsOpen U ∧ 0 ∈ U ∧
        ∃ hUT : U ⊆ Φ.target,
        ∀ (a : ComplexModel n) (ha : a ∈ U),
          let haT := hUT ha
          let y := actualFlatteningInverseMap x Φ a
          let hy := actualNearbyPoint_mem_chart_source x Φ hsrc a haT
          let E := actualNearbyGermEquiv Φ a haT
          let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) a)
          Ideal.map E.toRingEquiv.toRingHom Ia = wholeChartStalkIdeal A x y hy ∧
            Ia = Ideal.comap E.toRingEquiv.toRingHom (wholeChartStalkIdeal A x y hy) := by
  obtain ⟨Φ, hsrc, h0, hflat, O, hO, _hxO, N, G, hG, hgen,
    U, hU, h0U, hUT, hMap, _hH, _hF, hhol, hI, _htrans⟩ :=
    exists_original_regular_real_translated_ideal_dictionary C x hreg A hA
  refine ⟨Φ, hsrc, h0, hflat, U, hU, h0U, hUT, ?_⟩
  intro a ha
  let haT := hUT ha
  let y := actualFlatteningInverseMap x Φ a
  let hy := actualNearbyPoint_mem_chart_source x Φ hsrc a haT
  let E := actualNearbyGermEquiv Φ a haT
  let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) a)
  have hGy (i : Fin N) : HolomorphicAt n (G i) y :=
    holomorphicAt_of_mdifferentiableOn hO (hG i) (hMap ha)
  have hwhole := wholeChartStalkIdeal_eq_span_of_original_generators A x y hy G hGy (hgen y (hMap ha))
  have hmap : Ideal.map E.toRingEquiv.toRingHom Ia = wholeChartStalkIdeal A x y hy := by
    dsimp only [Ia]
    rw [hI a ha, Ideal.map_span, hwhole]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (actualNearbyGermEquiv_original_function x Φ hsrc a haT
        (G i) (hGy i) (hhol a ha i)).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, actualNearbyGermEquiv_original_function x Φ hsrc a haT
        (G i) (hGy i) (hhol a ha i)⟩
  refine ⟨hmap, ?_⟩
  rw [← hmap, Ideal.comap_map_of_bijective E.toRingEquiv.toRingHom E.bijective]

end Manifold
end
end Hironaka.HironakaSmoothCentreNearbyStalks
