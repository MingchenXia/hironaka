/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualWholeStalkHolomorphicPullback
import Hironaka.Support.GenuineAmbientJetAlgEquivExact
import Hironaka.Resolution.HironakaActualWholeAmbientHSSuperlevel

/-! Genuine original biholomorphisms preserve entire original stalks and the existing intrinsic HS function. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualBiholomorphicWholeStalkHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaActualWholeStalkHolomorphicPullback HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaActualWholeAmbientHSSuperlevel
section Maps
variable {n m k : ℕ} {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
  [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z]

omit [IsComplexManifold n X] in
/-- The literal genuine identity chart expression is the actual identity near zero. -/
theorem actualTranslatedMap_id_eventually (x : X) :
    actualTranslatedMap (n := n) (m := n) (id : X → X) x =ᶠ[𝓝 (0 : ComplexModel n)] id := by
  filter_upwards [(actualTranslatedMapDomain_isOpen (f := (id : X → X)) contMDiff_id x).mem_nhds
    (zero_mem_actualTranslatedMapDomain (n := n) (m := n) (id : X → X) x)] with z hz
  change (chartAt (ComplexModel n) x) ((chartAt (ComplexModel n) x).symm
    (z + (chartAt (ComplexModel n) x) x)) - (chartAt (ComplexModel n) x) x = z
  rw [(chartAt (ComplexModel n) x).right_inv hz.1,add_sub_cancel_right]

/-- The independently defined actual whole germ pullback preserves the genuine identity. -/
theorem actualHolomorphicGermPullback_id (x : X) :
    actualHolomorphicGermPullback (f := (id : X → X)) contMDiff_id x =
      AlgHom.id ℂ (HolGerm (ComplexModel n)) := by
  apply AlgHom.ext
  intro a
  induction a using HolGerm.induction_on with
  | h F hF =>
    change actualHolomorphicGermPullback (f := (id : X → X)) contMDiff_id x (HolGerm.mk F hF) =
      HolGerm.mk F hF
    unfold actualHolomorphicGermPullback
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact (actualTranslatedMap_id_eventually x).mono (fun z hz => congrArg F hz)

omit [IsComplexManifold n X] [IsComplexManifold m Y] [IsComplexManifold k Z] in
/-- True intermediate chart inverse identities give the actual translated composite near the original point. -/
theorem actualTranslatedMap_comp_eventually (f : Y → X) {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel m) ∞ g) (z : Z) :
    actualTranslatedMap (n := n) (m := k) (f ∘ g) z =ᶠ[𝓝 (0 : ComplexModel k)]
      actualTranslatedMap (n := n) (m := m) f (g z) ∘ actualTranslatedMap (n := m) (m := k) g z := by
  filter_upwards [(actualTranslatedMapDomain_isOpen hg z).mem_nhds
    (zero_mem_actualTranslatedMapDomain (n := m) (m := k) g z)] with w hw
  dsimp only [actualTranslatedMap,Function.comp_def]
  rw [sub_add_cancel,(chartAt (ComplexModel m) (g z)).left_inv hw.2]

/-- The genuine entire original complex-algebra pullback is contravariantly functorial. -/
theorem actualHolomorphicGermPullback_comp {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel m) ∞ g) (z : Z) :
    actualHolomorphicGermPullback (hf.comp hg) z =
      (actualHolomorphicGermPullback hg z).comp (actualHolomorphicGermPullback hf (g z)) := by
  apply AlgHom.ext
  intro a
  induction a using HolGerm.induction_on with
  | h F hF =>
    change actualHolomorphicGermPullback (hf.comp hg) z (HolGerm.mk F hF) =
      actualHolomorphicGermPullback hg z (actualHolomorphicGermPullback hf (g z) (HolGerm.mk F hF))
    unfold actualHolomorphicGermPullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact (actualTranslatedMap_comp_eventually f hg z).mono (fun w hw => congrArg F hw)

end Maps
section Equidimensional
variable {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- ONLY the actual original biholomorphism constructs the genuine whole complex germ algebra equivalence. -/
def actualBiholomorphicGermAlgEquiv
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (y : Y) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) := by
  apply AlgEquiv.ofAlgHom (actualHolomorphicGermPullback e.contMDiff y)
    (actualHolomorphicGermPullback e.symm.contMDiff (e y))
  · have h := actualHolomorphicGermPullback_comp e.symm.contMDiff e.contMDiff y
    simpa only [Function.comp_def,e.symm_apply_apply,actualHolomorphicGermPullback_id] using h.symm
  · have h := actualHolomorphicGermPullback_comp e.contMDiff e.symm.contMDiff (e y)
    simpa only [Function.comp_def,e.apply_symm_apply,e.symm_apply_apply,actualHolomorphicGermPullback_id] using h.symm

/-- The genuine equivalence keeps the SAME independently defined original pullback on EVERY whole germ. -/
theorem actualBiholomorphicGermAlgEquiv_apply
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (y : Y)
    (a : HolGerm (ComplexModel n)) :
    actualBiholomorphicGermAlgEquiv e y a = actualHolomorphicGermPullback e.contMDiff y a := rfl

/-- ONLY original coherence and actual biholomorphic geometry preserve the EXISTING intrinsic original ambient HS. -/
theorem hilbertSamuelAt_actual_biholomorphic_pullback
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (A : GermIdeal n X) (hA : A.IsCoherent) (y : Y) (ℓ : ℕ) :
    hilbertSamuelAt (GermIdeal.pullback (m := n) e A) y ℓ = hilbertSamuelAt A (e y) ℓ := by
  unfold hilbertSamuelAt
  rw [← map_wholeChartStalkIdeal_actual_pullback e.contMDiff A hA y]
  exact actualAmbientHS_eq_of_genuineAlgEquiv (actualBiholomorphicGermAlgEquiv e y) _ ℓ

/-- BOTH literal ALL-order original HS condition directions retain the same original threshold profile. -/
theorem actualWholeAmbientHSSuperlevel_actual_biholomorphic_pullback
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (A : GermIdeal n X) (hA : A.IsCoherent) (h : ℕ → ℕ) :
    actualWholeAmbientHSSuperlevel (GermIdeal.pullback (m := n) e A) h =
      e ⁻¹' actualWholeAmbientHSSuperlevel A h := by
  ext y
  change (∀ ℓ, h ℓ ≤ hilbertSamuelAt (GermIdeal.pullback (m := n) e A) y ℓ) ↔
    ∀ ℓ, h ℓ ≤ hilbertSamuelAt A (e y) ℓ
  simp only [hilbertSamuelAt_actual_biholomorphic_pullback e A hA]

end Equidimensional
end
end Hironaka.HironakaActualBiholomorphicWholeStalkHS
