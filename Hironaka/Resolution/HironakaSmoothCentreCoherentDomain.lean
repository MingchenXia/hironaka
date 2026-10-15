/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreCanonicalLayers
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.HadamardBridge

/-! # Actual original coherent families on a real nonlinear target domain
Only the REAL open domain is asserted coherent for the actual pullback.
No global extension, desired stalk/kernel/flatness certificate or arbitrary
origin-germ-to-nearby map is introduced. Complete mathematics written first in the matching blueprint chapter.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreCoherentDomain
noncomputable section
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  InvertibleIdealQuotient HadamardBridge
variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]

/-- The literal original finite-generator membership characterization on a REAL open domain. -/
def CoherentOn (I : GermIdeal m Y) (W : Set Y) : Prop :=
  ∀ y ∈ W, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ U ⊆ W ∧
    ∃ (N : ℕ) (H : Fin N → Y → ℂ),
      (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (H i) U) ∧
      ∀ z ∈ U, ∀ g, I.mem z g ↔ IsInSpanAt (n := m) (· ∈ range H) z g

/-- Compose an actual original finite relation using real LOCAL holomorphic map data. -/
theorem isInSpanAt_comp_eventually_mdifferentiable {f : Y → M} {y : Y}
    (hf : ∀ᶠ z in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f z)
    {S : (M → ℂ) → Prop} {c : M → ℂ} (hc : IsInSpanAt (n := n) S (f y) c) :
    IsInSpanAt (n := m) (fun s => ∃ a, S a ∧ s = a ∘ f) y (c ∘ f) := by
  obtain ⟨hchol, N, s, a, hs, ha, hsum⟩ := hc
  refine ⟨holomorphicAt_comp_map hf hchol, N, fun i => s i ∘ f, fun i => a i ∘ f,
    fun i => ⟨s i, hs i, rfl⟩, fun i => holomorphicAt_comp_map hf (ha i), ?_⟩
  exact hf.self_of_nhds.continuousAt.tendsto.eventually hsum

/-- Original generators internally produce actual pulled generators on a genuine smaller open. -/
theorem exists_local_original_pullback_generators {f : Y → M} (A : GermIdeal n M)
    (hA : A.IsCoherent) (W : Set Y) (hW : IsOpen W)
    (hf : ∀ z ∈ W, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f z)
    (y : Y) (hy : y ∈ W) :
    ∃ O : Set M, IsOpen O ∧ f y ∈ O ∧ ∃ (N : ℕ) (G : Fin N → M → ℂ),
      (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G i) O) ∧
      (∀ x ∈ O, ∀ g, A.mem x g ↔ IsInSpanAt (n := n) (· ∈ range G) x g) ∧
      ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ U ⊆ W ∧ MapsTo f U O ∧
        (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (G i ∘ f) U) ∧
        ∀ z ∈ U, ∀ g, (GermIdeal.pullback (m := m) f A).mem z g ↔
          IsInSpanAt (n := m) (· ∈ range fun i => G i ∘ f) z g := by
  obtain ⟨O, hO, hyO, N, G, hG, hgen⟩ := hA (f y)
  have hOevent : ∀ᶠ x in 𝓝 (f y), x ∈ O := hO.mem_nhds hyO
  have hpre : ∀ᶠ z in 𝓝 y, z ∈ W ∧ f z ∈ O := by
    filter_upwards [hW.mem_nhds hy, (hf y hy).continuousAt.tendsto.eventually hOevent] with z hz hzO
    exact ⟨hz, hzO⟩
  obtain ⟨U, hUsub, hU, hyU⟩ := mem_nhds_iff.mp hpre
  have hfat {z : Y} (hz : z ∈ U) :
      ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f w := by
    filter_upwards [hW.mem_nhds (hUsub hz).1] with w hw
    exact hf w hw
  have hshol (i : Fin N) (x : M) (hx : x ∈ O) : HolomorphicAt n (G i) x :=
    holomorphicAt_of_mdifferentiableOn hO (hG i) hx
  refine ⟨O, hO, hyO, N, G, hG, hgen, U, hU, hyU,
    (fun _ hz => (hUsub hz).1), (fun _ hz => (hUsub hz).2), ?_, ?_⟩
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

/-- The actual pullback is coherent on its REAL holomorphic domain, with no global extension. -/
theorem coherentOn_actual_pullback {f : Y → M} (A : GermIdeal n M) (hA : A.IsCoherent)
    (W : Set Y) (hW : IsOpen W)
    (hf : ∀ z ∈ W, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f z) :
    CoherentOn (GermIdeal.pullback (m := m) f A) W := by
  intro y hy
  obtain ⟨O, _hO, _hyO, N, G, _hG, _hgen, U, hU, hyU, hUW, _hMap, hH, hF⟩ :=
    exists_local_original_pullback_generators A hA W hW hf y hy
  exact ⟨U, hU, hyU, hUW, N, fun i => G i ∘ f, hH, hF⟩

open HolGerm HironakaSmoothCentreRelativeIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  FiniteGermIdealPullbackGenerators OkaRelationSheaf HironakaRelativeNormalCoherentSaturation

/-- A real-open holomorphic function has its actual translated holomorphic germ. -/
theorem translated_function_holAt {N : ℕ} {U : Set (ComplexModel N)}
    (hU : IsOpen U) {f : ComplexModel N → ℂ}
    (hf : MDifferentiableOn 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ℂ) f U)
    {a : ComplexModel N} (ha : a ∈ U) :
    HolAt (f ∘ actualAffineTranslation N a) 0 := by
  have hg := holomorphicAt_of_mdifferentiableOn hU hf ha
  have hzero : HolomorphicAt N f (actualAffineTranslation N a 0) := by
    simpa only [actualAffineTranslation_zero] using hg
  exact (hzero.comp_contMDiff (Eventually.of_forall fun _ =>
    (actualAffineTranslation_contMDiff N a).contMDiffAt)).mono fun _ h => h.differentiableAt

/-- Actual translation consumes the local original membership dictionary only. -/
theorem translated_sheaf_mem_iff_of_real_generators {k N : ℕ}
    (I : GermIdeal k (ComplexModel k)) (H : Fin N → ComplexModel k → ℂ)
    {U : Set (ComplexModel k)} (hU : IsOpen U)
    (hH : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ℂ) (H i) U)
    (hgen : ∀ z ∈ U, ∀ f, I.mem z f ↔ IsInSpanAt (n := k) (· ∈ range H) z f)
    {a : ComplexModel k} (ha : a ∈ U) (f : ComplexModel k → ℂ) :
    (actualTranslatedOriginalSheaf I a).mem 0 f ↔
      IsInSpanAt (n := k) (· ∈ range fun i => H i ∘ actualAffineTranslation k a) 0 f := by
  apply mem_pullback_iff_of_finite_generation
    (Eventually.of_forall fun _ => (actualAffineTranslation_contMDiff k a).contMDiffAt)
  · intro i
    simpa only [actualAffineTranslation_zero] using holomorphicAt_of_mdifferentiableOn hU (hH i) ha
  · simpa only [actualAffineTranslation_zero] using hgen a ha

/-- All original membership germs give precisely the whole actual translated generated ideal. -/
theorem translated_origin_ideal_eq_span_of_real_generators {k N : ℕ}
    (I : GermIdeal k (ComplexModel k)) (H : Fin N → ComplexModel k → ℂ)
    {U : Set (ComplexModel k)} (hU : IsOpen U)
    (hH : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ℂ) (H i) U)
    (hgen : ∀ z ∈ U, ∀ f, I.mem z f ↔ IsInSpanAt (n := k) (· ∈ range H) z f)
    {a : ComplexModel k} (ha : a ∈ U)
    (hhol : ∀ i, HolAt (H i ∘ actualAffineTranslation k a) 0) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I a) =
      Ideal.span (range fun i => HolGerm.mk (H i ∘ actualAffineTranslation k a) (hhol i)) := by
  classical
  have hdict : ∀ (f : ComplexModel k → ℂ) (hf : HolAt f 0),
      (actualTranslatedOriginalSheaf I a).mem 0 f ↔
        HolGerm.mk f hf ∈ Ideal.span (range fun i =>
          HolGerm.mk (H i ∘ actualAffineTranslation k a) (hhol i)) := by
    intro f hf
    rw [translated_sheaf_mem_iff_of_real_generators I H hU hH hgen ha f]
    constructor
    · intro h
      obtain ⟨_, c, hc, he⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp h
      exact (inSpanAt_zero_iff_mem_origin_span _ hhol hf).mp
        ⟨hf, c, fun i => (hc i).mono (fun _ hz => hz.differentiableAt), he⟩
    · intro h
      obtain ⟨hh, c, hc, he⟩ := (inSpanAt_zero_iff_mem_origin_span _ hhol hf).mpr h
      exact CoherentIdealColon.isInSpanAt_range_iff.mpr
        ⟨hh.mono (fun _ hz => hz.mdifferentiableAt), c,
          fun i => (hc i).mono (fun _ hz => hz.mdifferentiableAt), he⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f, hf, hIf, rfl⟩
    exact (hdict f hf).mp hIf
  · apply Ideal.span_le.mpr
    rintro g ⟨i, rfl⟩
    apply Ideal.subset_span
    refine ⟨H i ∘ actualAffineTranslation k a, hhol i, ?_, rfl⟩
    apply (translated_sheaf_mem_iff_of_real_generators I H hU hH hgen ha _).mpr
    exact CoherentIdealColon.isInSpanAt_range_self
      (fun j => (hhol j).mono (fun _ hz => hz.mdifferentiableAt)) i

/-- The REAL nonlinear inverse chart map, whose analytic assertions are restricted to the target. -/
def actualFlatteningInverseMap (x : M) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)) :
    ComplexModel n → M := fun z => (chartAt (ComplexModel n) x).symm (Φ.invFun z)

/-- The EXISTING literal germ-ideal pullback by that actual total function. -/
def actualFlattenedOriginalSheaf (A : GermIdeal n M) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)) : GermIdeal n (ComplexModel n) :=
  GermIdeal.pullback (m := n) (actualFlatteningInverseMap x Φ) A

/-- Actual inverse holomorphicity on EVERY real target point, with true chart image membership. -/
theorem actualFlatteningInverseMap_mdifferentiable (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) :
    ∀ z ∈ Φ.target, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (actualFlatteningInverseMap x Φ) z := by
  intro z hz
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.invFun z :=
    (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz)).mdifferentiableAt
  exact (mdifferentiableAt_atlas_symm (ChartedSpace.chart_mem_atlas x)
    (hsrc (Φ.mapsTo_invFun hz))).comp z h1

omit [IsComplexManifold n M] in
theorem actualFlattening_target_zero_mem (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) : (0 : ComplexModel n) ∈ Φ.target := by
  rw [← h0]
  exact Φ.mapsTo_toFun Φ.center_mem_source

omit [IsComplexManifold n M] in
theorem actualFlatteningInverseMap_zero (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) : actualFlatteningInverseMap x Φ 0 = x := by
  have hInv := Φ.left_inv _ Φ.center_mem_source
  rw [h0] at hInv
  change (chartAt (ComplexModel n) x).symm (Φ.invFun 0) = x
  rw [hInv, (chartAt (ComplexModel n) x).left_inv (mem_chart_source _ x)]

/-- Original coherence and actual flattening internally give coherence ONLY on the real open target. -/
theorem coherentOn_actualFlattenedOriginalSheaf (A : GermIdeal n M) (hA : A.IsCoherent) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) :
    CoherentOn (actualFlattenedOriginalSheaf A x Φ) Φ.target :=
  coherentOn_actual_pullback A hA Φ.target Φ.isOpen_target (actualFlatteningInverseMap_mdifferentiable x Φ hsrc)

/-- ONLY actual original regular geometry and original coherence supply the genuine real-open family. -/
theorem exists_original_regular_real_coherent_domain {d : ℕ} (C : Set M) (x : M)
    (hreg : RegularAtDim (n := n) C x d) (A : GermIdeal n M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n d)) ∧
      CoherentOn (actualFlattenedOriginalSheaf A x Φ) Φ.target ∧
      (0 : ComplexModel n) ∈ Φ.target ∧ actualFlatteningInverseMap x Φ 0 = x ∧
      ∃ U : Set (ComplexModel n), IsOpen U ∧ 0 ∈ U ∧ U ⊆ Φ.target ∧
        ∃ (N : ℕ) (H : Fin N → ComplexModel n → ℂ),
          (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (H i) U) ∧
          ∀ z ∈ U, ∀ g, (actualFlattenedOriginalSheaf A x Φ).mem z g ↔
            IsInSpanAt (n := n) (· ∈ range H) z g := by
  obtain ⟨_, _, Φ, hsrc, h0, hflat⟩ := hreg
  have hcoh := coherentOn_actualFlattenedOriginalSheaf A hA x Φ hsrc
  have h0T := actualFlattening_target_zero_mem x Φ h0
  obtain ⟨U, hU, h0U, hUT, N, H, hH, hgen⟩ := hcoh 0 h0T
  exact ⟨Φ, hsrc, h0, hflat, hcoh, h0T, actualFlatteningInverseMap_zero x Φ h0,
    U, hU, h0U, hUT, N, H, hH, hgen⟩

/-- Original regularity and coherence supply ALL nearby whole ideals from literal original composites. -/
theorem exists_original_regular_real_translated_ideal_dictionary {d : ℕ}
    (C : Set M) (x : M) (hreg : RegularAtDim (n := n) C x d)
    (A : GermIdeal n M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n d)) ∧
      ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∃ (N : ℕ) (G : Fin N → M → ℂ),
        (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G i) O) ∧
        (∀ y ∈ O, ∀ g, A.mem y g ↔ IsInSpanAt (n := n) (· ∈ range G) y g) ∧
        ∃ U : Set (ComplexModel n), IsOpen U ∧ 0 ∈ U ∧ U ⊆ Φ.target ∧
          MapsTo (actualFlatteningInverseMap x Φ) U O ∧
          let H : Fin N → ComplexModel n → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
          (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (H i) U) ∧
          (∀ z ∈ U, ∀ g, (actualFlattenedOriginalSheaf A x Φ).mem z g ↔
            IsInSpanAt (n := n) (· ∈ range H) z g) ∧
          ∃ hhol : ∀ a ∈ U, ∀ i, HolAt (H i ∘ actualAffineTranslation n a) 0,
            (∀ a (ha : a ∈ U),
              originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) a) =
                Ideal.span (range fun i => HolGerm.mk (H i ∘ actualAffineTranslation n a) (hhol a ha i))) ∧
            ∀ a ∈ U, ∀ g,
              (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) a).mem 0 g ↔
                IsInSpanAt (n := n) (· ∈ range fun i => H i ∘ actualAffineTranslation n a) 0 g := by
  obtain ⟨_, _, Φ, hsrc, h0, hflat⟩ := hreg
  have h0T := actualFlattening_target_zero_mem x Φ h0
  obtain ⟨O, hO, h0O, N, G, hG, hgen, U, hU, h0U, hUT, hMap, hH, hF⟩ :=
    exists_local_original_pullback_generators A hA Φ.target Φ.isOpen_target
      (actualFlatteningInverseMap_mdifferentiable x Φ hsrc) 0 h0T
  have hxO : x ∈ O := by
    simpa only [actualFlatteningInverseMap_zero x Φ h0] using h0O
  let H : Fin N → ComplexModel n → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  have hhol : ∀ a ∈ U, ∀ i, HolAt (H i ∘ actualAffineTranslation n a) 0 :=
    fun _ ha i => translated_function_holAt hU (hH i) ha
  refine ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen,
    U, hU, h0U, hUT, hMap, hH, hF, hhol, ?_, ?_⟩
  · intro a ha
    exact translated_origin_ideal_eq_span_of_real_generators
      (actualFlattenedOriginalSheaf A x Φ) H hU hH hF ha (hhol a ha)
  · intro a ha g
    exact translated_sheaf_mem_iff_of_real_generators
      (actualFlattenedOriginalSheaf A x Φ) H hU hH hF ha g

end
end Hironaka.HironakaSmoothCentreCoherentDomain
