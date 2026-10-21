/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainSaturation

/-! # Actual original deformation and central family on genuine real domains
The existing projection-plus-graph-equations ideal is retained. Only
actual local coherent generators on the true projection target preimage
are used; Oka/Noetherian saturation supplies one index and real open.
The existing central ideal at that SAME index is coherent only on its
actual central-map preimage. Complete mathematics precedes this source.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainDeformation
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  OkaCoherence HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainSaturation
  HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalDeformationSaturation
  RelativePrincipalizationSpan InvertibleIdealQuotient HadamardBridge RestrictedIdealExtension

/-- Literal original pullback from a genuinely coherent real source domain. -/
theorem coherentOn_pullback_of_local {n m : ℕ} (I : GermIdeal n (ComplexModel n))
    (W : Set (ComplexModel n)) (hI : CoherentOn I W)
    (V : Set (ComplexModel m)) (hV : IsOpen V) (f : ComplexModel m → ComplexModel n)
    (hf : ∀ z ∈ V, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f z)
    (hMap : MapsTo f V W) : CoherentOn (GermIdeal.pullback (m := m) f I) V := by
  intro y hy
  obtain ⟨O, hO, hfyO, _hOW, N, G, hG, hgen⟩ := hI (f y) (hMap hy)
  have hpre : ∀ᶠ z in 𝓝 y, z ∈ V ∧ f z ∈ O := by
    filter_upwards [hV.mem_nhds hy,
      (hf y hy).continuousAt.tendsto.eventually (hO.mem_nhds hfyO)] with z hz hzO
    exact ⟨hz, hzO⟩
  obtain ⟨U, hUsub, hU, hyU⟩ := mem_nhds_iff.mp hpre
  have hfat {z : ComplexModel m} (hz : z ∈ U) :
      ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f w := by
    filter_upwards [hV.mem_nhds (hUsub hz).1] with w hw
    exact hf w hw
  have hshol (i : Fin N) (z : ComplexModel n) (hz : z ∈ O) : HolomorphicAt n (G i) z :=
    holomorphicAt_of_mdifferentiableOn hO (hG i) hz
  refine ⟨U, hU, hyU, (fun _ hz => (hUsub hz).1), N, fun i => G i ∘ f, ?_, ?_⟩
  · intro i z hz
    exact (holomorphicAt_comp_map (hfat hz) (hshol i (f z) (hUsub hz).2)).mdifferentiableAt.mdifferentiableWithinAt
  · intro z hz g
    constructor
    · intro hg
      refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
      rintro a ⟨a0, ham, rfl⟩
      refine IsInSpanAt.mono ?_ (isInSpanAt_comp_eventually_mdifferentiable
        (hfat hz) ((hgen (f z) (hUsub hz).2 a0).mp ham))
      rintro s' ⟨s0, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · intro hg
      refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hg)
      rintro s' ⟨i, rfl⟩
      exact ⟨G i, (hgen (f z) (hUsub hz).2 (G i)).mpr
        (isInSpanAt_self ⟨i, rfl⟩ (hshol i (f z) (hUsub hz).2)), rfl⟩

/-- The actual local condition restricts to a genuine smaller open. -/
theorem coherentOn_restrict {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (W : Set (ComplexModel n)) (hI : CoherentOn I W)
    (U : Set (ComplexModel n)) (hU : IsOpen U) (hUW : U ⊆ W) : CoherentOn I U := by
  intro y hy
  obtain ⟨V, hV, hyV, _hVW, N, G, hG, hgen⟩ := hI y (hUW hy)
  exact ⟨V ∩ U, hV.inter hU, ⟨hyV, hy⟩, inter_subset_right, N, G,
    fun i => (hG i).mono inter_subset_left, fun z hz => hgen z hz.1⟩

theorem coherentOn_of_isCoherent {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (hI : I.IsCoherent) (W : Set (ComplexModel n)) (hW : IsOpen W) : CoherentOn I W := by
  intro y hy
  obtain ⟨U, hU, hyU, N, G, hG, hgen⟩ := hI y
  exact ⟨U ∩ W, hU.inter hW, ⟨hyU, hy⟩, inter_subset_right, N, G,
    fun i => (hG i).mono inter_subset_left, fun z hz => hgen z hz.1⟩

/-- Both actual local families concatenate to present the EXISTING literal sum on the real domain. -/
theorem coherentOn_sum {n : ℕ} (I J : GermIdeal n (ComplexModel n))
    (W : Set (ComplexModel n)) (hI : CoherentOn I W) (hJ : CoherentOn J W) :
    CoherentOn (RestrictedIdealExtension.sumIdeal I J) W := by
  intro y hy
  obtain ⟨U, hU, hyU, hUW, N, G, hG, hgen⟩ := hI y hy
  obtain ⟨V, hV, hyV, _hVW, P, H, hH, hgenJ⟩ := hJ y hy
  refine ⟨U ∩ V, hU.inter hV, ⟨hyU, hyV⟩, (fun _ hz => hUW hz.1), N+P, sumFamily G H, ?_, ?_⟩
  · intro k
    refine Fin.addCases (fun j z hz => ?_) (fun j z hz => ?_) k
    · simpa [sumFamily] using (hG j z hz.1).mono inter_subset_left
    · simpa [sumFamily] using (hH j z hz.2).mono inter_subset_right
  · intro z hz g
    constructor
    · intro hg
      change IsInSpanAt (n := n) (fun s => I.mem z s ∨ J.mem z s) z g at hg
      refine IsInSpanAt.trans ?_ hg
      rintro s (hs | hs)
      · exact IsInSpanAt.mono (fun _ => range_left_subset_sumFamily) ((hgen z hz.1 s).mp hs)
      · exact IsInSpanAt.mono (fun _ => range_right_subset_sumFamily) ((hgenJ z hz.2 s).mp hs)
    · intro hg
      change IsInSpanAt (n := n) (fun s => I.mem z s ∨ J.mem z s) z g
      refine IsInSpanAt.mono ?_ hg
      intro s hs
      rcases mem_range_sumFamily hs with hs' | hs'
      · obtain ⟨j, rfl⟩ := hs'
        exact Or.inl (IdealWeightComparison.mem_of_isPresentation hU hz.1 hG hgen j)
      · obtain ⟨j, rfl⟩ := hs'
        exact Or.inr (IdealWeightComparison.mem_of_isPresentation hV hz.2 hH hgenJ j)

/-- A genuine local Oka presentation is coherence on one actual open, with no global extension. -/
theorem exists_open_coherentOn_of_idealFGAt {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (hI : IdealFGAt I.mem 0) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ 0 ∈ U ∧ CoherentOn I U := by
  classical
  obtain ⟨U, hU, h0U, μ, hμ, S, hS, hgen⟩ := hI
  let := hμ
  let e := Fintype.equivFin μ
  refine ⟨U, hU, h0U, ?_⟩
  intro y hy
  refine ⟨U, hU, hy, subset_refl U, Fintype.card μ, fun i => S (e.symm i),
    fun i => mdifferentiableOn_iff_differentiableOn.mpr (hS (e.symm i)), ?_⟩
  intro z hz g
  rw [hgen z hz g, CoherentIdealColon.isInSpanAt_range_iff]
  constructor
  · rintro ⟨hg, a, ha, he⟩
    refine ⟨hg.mono (fun _ h => h.mdifferentiableAt), fun i => a (e.symm i),
      fun i => (ha (e.symm i)).mono (fun _ h => h.mdifferentiableAt), ?_⟩
    filter_upwards [he] with w hw
    rw [hw]
    exact (e.symm.sum_comp (fun i => a i w * S i w)).symm
  · rintro ⟨hg, a, ha, he⟩
    refine ⟨hg.mono (fun _ h => h.differentiableAt), fun i => a (e i),
      fun i => (ha (e i)).mono (fun _ h => h.differentiableAt), ?_⟩
    filter_upwards [he] with w hw
    rw [hw]
    simpa only [Equiv.symm_apply_apply] using
      (e.sum_comp (fun i => a i w * S (e.symm i) w)).symm

section Original
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original input supplies local coherence of the EXISTING original equation model on its REAL domain. -/
theorem exists_original_regular_real_graph_deformation_domain
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let F := actualFlattenedOriginalSheaf A x Φ
      let V := (deformationProjection d t) ⁻¹' Φ.target
      IsOpen V ∧ 0 ∈ V ∧ CoherentOn (originalDeformationIdeal d t F) V := by
  obtain ⟨_, _, Φ, hsrc, h0, hflat⟩ := hreg
  let F := actualFlattenedOriginalSheaf A x Φ
  let V := (deformationProjection d t) ⁻¹' Φ.target
  have hV : IsOpen V := Φ.isOpen_target.preimage (deformationProjection d t).continuous
  have h0V : (0 : ComplexModel (deformationDimension d t)) ∈ V := by
    change deformationProjection d t 0 ∈ Φ.target
    simpa only [map_zero] using actualFlattening_target_zero_mem x Φ h0
  have hF := coherentOn_actualFlattenedOriginalSheaf A hA x Φ hsrc
  have hpull := coherentOn_pullback_of_local F Φ.target hF V hV (deformationProjection d t)
    (fun _ _ => (deformationProjection d t).differentiableAt.mdifferentiableAt) (fun _ hz => hz)
  have hEq := coherentOn_of_isCoherent (deformationEquationIdeal d t)
    (deformationEquationIdeal_isCoherent d t) V hV
  exact ⟨Φ, hsrc, h0, hflat, hV, h0V,
    coherentOn_sum _ _ V hpull hEq⟩

/-- Original data select SAME N and true real opens for ALL original parameter powers and central coherence. -/
theorem exists_original_regular_real_exact_deformation_central_model
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' Φ.target ∧
        let F := actualFlattenedOriginalSheaf A x Φ
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
          ((originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ q) ↔
            (originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ N))) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        let B := (deformationCentralInclusion d t) ⁻¹' U
        IsOpen B ∧ 0 ∈ B ∧ CoherentOn (originalDeformationCentralIdeal d t F N) B := by
  obtain ⟨Φ, hsrc, h0, hflat, hV, h0V, hD⟩ :=
    exists_original_regular_real_graph_deformation_domain C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
  let V := (deformationProjection d t) ⁻¹' Φ.target
  have hfg := idealFGAt_of_coherentOn (originalDeformationIdeal d t F) V hD h0V
  have hh : HolAt (deformationParameter d t) 0 :=
    Eventually.of_forall fun _ => (deformationParameter d t).differentiableAt
  let := isNoetherianRing_holGerm_euclidean (deformationDimension d t)
  obtain ⟨N, V0, hV0, h0V0, _hhV0, hstab, hpow, hsat⟩ :=
    exists_uniform_original_coherent_saturation_union (okaProperty_euclidean (deformationDimension d t)) hfg hh
  have hcolFG : IdealFGAt (originalDeformationColonIdeal d t F N).mem 0 :=
    actualColonChain_finitely_generated (okaProperty_euclidean (deformationDimension d t)) hfg hh N
  obtain ⟨O, hO, h0O, hcolO⟩ := exists_open_coherentOn_of_idealFGAt _ hcolFG
  let U := (V0 ∩ O) ∩ V
  have hU : IsOpen U := (hV0.inter hO).inter hV
  have h0U : (0 : ComplexModel (deformationDimension d t)) ∈ U := ⟨⟨h0V0, h0O⟩, h0V⟩
  have hcolU := coherentOn_restrict (originalDeformationColonIdeal d t F N) O hcolO U hU
    (fun _ hy => hy.1.2)
  let B := (deformationCentralInclusion d t) ⁻¹' U
  have hB : IsOpen B := hU.preimage (deformationCentralInclusion d t).continuous
  have h0B : (0 : ComplexModel (d+t)) ∈ B := by
    change deformationCentralInclusion d t 0 ∈ U
    simpa only [map_zero] using h0U
  have hcentral := coherentOn_pullback_of_local (originalDeformationColonIdeal d t F N) U hcolU B hB
    (deformationCentralInclusion d t)
    (fun _ _ => (deformationCentralInclusion d t).differentiableAt.mdifferentiableAt) (fun _ hy => hy)
  exact ⟨Φ, hsrc, h0, hflat, N, U, hU, h0U, (fun _ hy => hy.2), hcolU,
    (fun y hy => hstab y hy.1.1), (fun y hy => hpow y hy.1.1), (fun y hy => hsat y hy.1.1),
    hB, h0B, hcentral⟩

end Original
end
end Hironaka.HironakaSmoothCentreRealDomainDeformation
