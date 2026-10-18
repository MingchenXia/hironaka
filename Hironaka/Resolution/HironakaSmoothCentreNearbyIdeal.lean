/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreNearbyStalks

/-! # Whole original centre ideals at every real nearby centre point
The fixed normal ideal is identified only at actual target points lying
on the coordinate plane. Original regularity, coherence and ideal
containment internally supply one genuine open for both whole ideals
and every true centre power. Complete mathematics precedes this source.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreNearbyIdeal
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreRelativeIdeal HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  BlowupFlatCoordinates

section Manifold
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual target inverse lies in the real original flattening domain. -/
theorem actualNearbyPoint_mem_flatDomain (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (a : ComplexModel n) (ha : a ∈ Φ.target) :
    actualFlatteningInverseMap x Φ a ∈ flatDomain Φ :=
  (flatInverse_mem Φ ha hsrc).1

private theorem chartTranslatedGerm_congr (x y : M)
    (hy : y ∈ (chartAt (ComplexModel n) x).source) {f g : M → ℂ}
    (hf : HolomorphicAt n f y) (hg : HolomorphicAt n g y) (heq : f =ᶠ[𝓝 y] g) :
    chartTranslatedGerm x y hy f hf = chartTranslatedGerm x y hy g hg := by
  simp only [chartTranslatedGerm, translatedGerm]
  apply HolGerm.mk_eq_mk_iff.mpr
  let e := chartAt (ComplexModel n) x
  have ht : Tendsto (fun z : ComplexModel n => e.symm (z + e y)) (𝓝 0) (𝓝 y) := by
    have ha : Tendsto (fun z : ComplexModel n => z + e y) (𝓝 0) (𝓝 (e y)) := by
      simpa only [id_eq, zero_add] using (continuous_id.add_const (e y)).tendsto (0 : ComplexModel n)
    have hb := (e.continuousAt_symm (e.map_source hy)).tendsto
    simpa only [e.left_inv hy, Function.comp_def] using hb.comp ha
  exact ht.eventually heq

private theorem chartTranslatedGerm_sum_mul (x y : M)
    (hy : y ∈ (chartAt (ComplexModel n) x).source) {ι : Type*} [Fintype ι]
    (f g : ι → M → ℂ) (hf : ∀ i, HolomorphicAt n (f i) y)
    (hg : ∀ i, HolomorphicAt n (g i) y) :
    chartTranslatedGerm x y hy (fun z => ∑ i, f i z * g i z)
        (HolomorphicAt.sum Finset.univ fun i _ => (hf i).mul (hg i)) =
      ∑ i, chartTranslatedGerm x y hy (f i) (hf i) * chartTranslatedGerm x y hy (g i) (hg i) := by
  simp only [chartTranslatedGerm, translatedGerm]
  rw [HolGerm.mk_sum Finset.univ]
  · exact Finset.sum_congr rfl fun i _ => HolGerm.mk_mul _ _ _ _
  · intro i
    exact translated_holomorphic _ (CartanLocalReduction.holAt_comp_chart_symm hy
      ((hf i).mul (hg i)))

/-- Actual original containment retains every member of the whole fixed-chart stalk. -/
theorem wholeChartStalkIdeal_le_of_original_le (A D : GermIdeal n M)
    (hAD : A.Le D) (x y : M) (hy : y ∈ (chartAt (ComplexModel n) x).source) :
    wholeChartStalkIdeal A x y hy ≤ wholeChartStalkIdeal D x y hy := by
  apply Ideal.span_le.mpr
  rintro g ⟨f, hf, hmem, rfl⟩
  exact Ideal.subset_span ⟨f, hf, hAD y f hmem, rfl⟩

end Manifold

section Centre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- A true nearby centre-plane point removes ONLY its tangential coordinate constants. -/
theorem actualNearbyGermEquiv_normalCoordinate (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target)
    (a : ComplexModel (d+t)) (ha : a ∈ Φ.target)
    (hPlane : a ∈ complexCoordinatePlane (d+t) d) (i : Fin t) :
    actualNearbyGermEquiv Φ a ha (normalCoordinate d t i) =
      chartTranslatedGerm x (actualFlatteningInverseMap x Φ a)
        (actualNearbyPoint_mem_chart_source x Φ hsrc a ha) (flatCoord Φ (i.natAdd d))
        (holomorphicAt_flatCoord Φ _ (actualNearbyPoint_mem_flatDomain x Φ hsrc a ha)) := by
  unfold actualNearbyGermEquiv normalCoordinate coordinateGerm
  rw [localGermAlgEquiv_mk]
  simp only [chartTranslatedGerm, translatedGerm]
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards [(actualNearbyEquiv Φ a ha).isOpen_source.mem_nhds
    (actualNearbyEquiv Φ a ha).center_mem_source] with z hz
  change Φ.toFun (z + Φ.invFun a) (i.natAdd d) - a (i.natAdd d) =
    Φ.toFun (chartAt (ComplexModel (d+t)) x
      ((chartAt (ComplexModel (d+t)) x).symm
        (z + chartAt (ComplexModel (d+t)) x (actualFlatteningInverseMap x Φ a)))) (i.natAdd d)
  rw [hPlane (i.natAdd d) (by simp), sub_zero,
    actualNearbyPoint_chart_value x Φ hsrc a ha, (chartAt (ComplexModel (d+t)) x).right_inv (hsrc hz)]

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- At every REAL centre-plane target point, the ENTIRE original vanishing stalk is the actual image. -/
theorem whole_nearby_vanishing_stalk_eq_map_normalIdeal (x : M) (C : Set M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
      chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d))
    (a : ComplexModel (d+t)) (ha : a ∈ Φ.target)
    (hPlane : a ∈ complexCoordinatePlane (d+t) d) :
    wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x (actualFlatteningInverseMap x Φ a)
        (actualNearbyPoint_mem_chart_source x Φ hsrc a ha) =
      Ideal.map (actualNearbyGermEquiv Φ a ha).toRingEquiv.toRingHom (normalIdeal d t) := by
  let E := actualNearbyGermEquiv Φ a ha
  let J := Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t)
  let y := actualFlatteningInverseMap x Φ a
  let hy := actualNearbyPoint_mem_chart_source x Φ hsrc a ha
  have hdom := actualNearbyPoint_mem_flatDomain x Φ hsrc a ha
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f, hf, hmem, rfl⟩
    obtain ⟨b, hb0, hb, he⟩ := exists_eq_sum_flatCoord Φ hsrc hflat hdom hmem
    have hG : ∀ i, HolomorphicAt (d+t) (flatCoord Φ i) y :=
      fun i => holomorphicAt_flatCoord Φ i hdom
    rw [chartTranslatedGerm_congr x y hy hf (HolomorphicAt.sum Finset.univ fun i _ => (hb i).mul (hG i)) he,
      chartTranslatedGerm_sum_mul x y hy b (flatCoord Φ) hb hG, Fin.sum_univ_add]
    have hz : ∑ i : Fin d,
        chartTranslatedGerm x y hy (b (i.castAdd t)) (hb _) *
          chartTranslatedGerm x y hy (flatCoord Φ (i.castAdd t)) (hG _) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hbi := hb0 (i.castAdd t) i.isLt
      simp only [hbi]
      change HolGerm.mk (fun _ : ComplexModel (d+t) => (0 : ℂ)) eventually_differentiableAt_zero * _ = 0
      have he0 : HolGerm.mk (fun _ : ComplexModel (d+t) => (0 : ℂ)) eventually_differentiableAt_zero = 0 :=
        HolGerm.mk_zero
      rw [he0, zero_mul]
    rw [hz, zero_add]
    apply Ideal.sum_mem
    intro i _
    apply Ideal.mul_mem_left
    have hcoord : normalCoordinate d t i ∈ normalIdeal d t := Ideal.subset_span ⟨i, rfl⟩
    have hm := Ideal.mem_map_of_mem E.toRingEquiv.toRingHom hcoord
    change E (normalCoordinate d t i) ∈ J at hm
    dsimp only [E] at hm
    rw [actualNearbyGermEquiv_normalCoordinate x Φ hsrc a ha hPlane] at hm
    exact hm
  · change Ideal.map E.toRingEquiv.toRingHom (Ideal.span (range (normalCoordinate d t))) ≤ _
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro g ⟨v, ⟨i, rfl⟩, rfl⟩
    change E (normalCoordinate d t i) ∈ _
    dsimp only [E]
    rw [actualNearbyGermEquiv_normalCoordinate x Φ hsrc a ha hPlane]
    apply Ideal.subset_span
    exact ⟨flatCoord Φ (i.natAdd d), holomorphicAt_flatCoord Φ _ hdom,
      flatCoord_mem_vanishingIdeal Φ hflat (by simp) hdom, rfl⟩

/-- The WHOLE actual original centre powers, with genuine nearby point/plane restriction. -/
theorem whole_nearby_vanishing_stalk_pow_eq_map (x : M) (C : Set M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
      chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d))
    (a : ComplexModel (d+t)) (ha : a ∈ Φ.target)
    (hPlane : a ∈ complexCoordinatePlane (d+t) d) (q : ℕ) :
    wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x (actualFlatteningInverseMap x Φ a)
        (actualNearbyPoint_mem_chart_source x Φ hsrc a ha) ^ q =
      Ideal.map (actualNearbyGermEquiv Φ a ha).toRingEquiv.toRingHom (normalIdeal d t ^ q) := by
  rw [whole_nearby_vanishing_stalk_eq_map_normalIdeal x C Φ hsrc hflat a ha hPlane, Ideal.map_pow]

/-- Original geometry, coherence and containment supply BOTH whole nearby ideals and ALL centre powers. -/
theorem exists_original_regular_same_open_nearby_relative_ideal_bridge
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) (hAC : A.Le (vanishingIdeal (n := d+t) C)) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ U : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
        ∃ hUT : U ⊆ Φ.target,
        ∀ (a : ComplexModel (d+t)) (ha : a ∈ U), a ∈ complexCoordinatePlane (d+t) d →
          let haT := hUT ha
          let y := actualFlatteningInverseMap x Φ a
          let hy := actualNearbyPoint_mem_chart_source x Φ hsrc a haT
          let E := actualNearbyGermEquiv Φ a haT
          let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) a)
          let Ix := wholeChartStalkIdeal A x y hy
          let Kx := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x y hy
          y ∈ C ∧ Ix ≤ Kx ∧ Ix = Ideal.map E.toRingEquiv.toRingHom Ia ∧
            Kx = Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ∧
            ∀ q : ℕ, Kx ^ q = Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t ^ q) := by
  obtain ⟨Φ, hsrc, h0, hflat, U, hU, h0U, hUT, hI⟩ :=
    exists_original_regular_same_open_nearby_whole_stalk_dictionary C x hreg A hA
  refine ⟨Φ, hsrc, h0, hflat, U, hU, h0U, hUT, ?_⟩
  intro a ha hPlane
  have hdom := actualNearbyPoint_mem_flatDomain x Φ hsrc a (hUT ha)
  have hImg : Φ.toFun (chartAt (ComplexModel (d+t)) x (actualFlatteningInverseMap x Φ a)) = a := by
    rw [actualNearbyPoint_chart_value x Φ hsrc a (hUT ha), Φ.right_inv a (hUT ha)]
  have hyC : actualFlatteningInverseMap x Φ a ∈ C := by
    apply (hflat hdom.1 hdom.2).mpr
    rw [hImg]
    exact hPlane
  exact ⟨hyC, wholeChartStalkIdeal_le_of_original_le A _ hAC x _ hdom.1,
    (hI a ha).1.symm, whole_nearby_vanishing_stalk_eq_map_normalIdeal x C Φ hsrc hflat a (hUT ha) hPlane,
    fun q => whole_nearby_vanishing_stalk_pow_eq_map x C Φ hsrc hflat a (hUT ha) hPlane q⟩

end Centre
end
end Hironaka.HironakaSmoothCentreNearbyIdeal
