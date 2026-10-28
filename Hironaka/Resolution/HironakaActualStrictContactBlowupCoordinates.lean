/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFixedFlatteningBlowupCoordinates
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Resolution.HironakaActualFixedFlatteningHSComparison
import Hironaka.Resolution.HironakaActualStrictRadicalPullback

/-! Actual strict-contact geometry forces the same genuine affine blowup
square's normal directions to vanish. The target flattening is retained;
no chart, pivot, zero-normal or strict-contact equation certificate is supplied.
Blueprint: hironaka-actual-strict-contact-blowup-coordinates-extension.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualStrictContactBlowupCoordinates
noncomputable section
open Hironaka.BlowupSequences NormalCrossings BlowupFlatCoordinates BlowupMonomialCharts
  BlowupLocalSurjectivity BlowupFibreDirection BlowupSNCTransform BlowupStrictSubmanifold
  HironakaActualAnalyticBlowupTaylor HironakaActualPointBlowupCoordinates
  HironakaActualSmoothCentreBlowupCoordinates
variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- SAME genuine joint source geometry and actual strict-contact membership
internally construct the whole affine square, a base pivot, all zero contact
normal directions and the WHOLE strict-contact plane in the same source chart. -/
theorem exists_actual_strict_contact_blowup_coordinates {C N : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (y : Y) (k d : ℕ)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π y) (π y))=0)
    (hflatC : ∀ {x : X},x∈(chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) x∈Φ.source →
      (x∈C ↔ Φ.toFun (chartAt (ComplexModel n) (π y) x)∈complexCoordinatePlane n k))
    (hflatN : ∀ {x : X},x∈(chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) x∈Φ.source →
      (x∈N ↔ Φ.toFun (chartAt (ComplexModel n) (π y) x)∈complexCoordinatePlane n d))
    (hyN : y∈geoStrictTransform π C N) :
    ∃ (e : Fin n) (b : Fin n → ℂ)
      (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y y)),
      Θ.source⊆(chartAt (ComplexModel n) y).target ∧
      Θ.toFun (chartAt (ComplexModel n) y y)=0 ∧
      k≤e.val ∧ e.val<d ∧
      (∀ i : Fin n,i.val<k → b i=0) ∧ (∀ i : Fin n,d ≤ i.val → b i=0) ∧ b e=0 ∧
      ∀ z : Y,z∈(chartAt (ComplexModel n) y).source →
        chartAt (ComplexModel n) y z∈Θ.source →
        π z∈flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel n) (π y) (π z))=
          actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} e b (Θ.toFun (chartAt (ComplexModel n) y z)) ∧
        (z∈geoStrictTransform π C N ↔
          Θ.toFun (chartAt (ComplexModel n) y z)∈complexCoordinatePlane n d) := by
  have hyflat : π y∈flatDomain Φ := mem_flatDomain_self Φ
  obtain ⟨e,he,O,hO,hyO,W,hWs,hWeq,hℓW,_⟩ :=
    exists_monomialLocalInverse hπ hΦsrc hflatC hyflat
  let T : Finset (Fin n) := Finset.univ.filter fun i => d ≤ i.val
  have hflatNT : ∀ {x : X},x∈(chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) x∈Φ.source →
      (x∈N ↔ Φ.toFun (chartAt (ComplexModel n) (π y) x)∈coordSubspace T) := by
    intro x hx hxΦ
    rw [coordSubspace_eq_complexCoordinatePlane]
    exact hflatN hx hxΦ
  have hNu : ∀ z∈O,z∈geoStrictTransform π C N ↔ e∉T ∧ W z∈coordSubspace T :=
    fun z hz => mem_geoStrictTransform_iff_of_chart hπ hΦsrc hflatC hflatNT he hO hWs hWeq hℓW hz
  obtain ⟨heT,hWy⟩ := (hNu y hyO).mp hyN
  have hed : e.val<d := by
    simpa only [T,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using heT
  have hWnormal : ∀ i : Fin n,d ≤ i.val → W y i=0 := by
    intro i hi
    exact hWy i (by simp only [T,Finset.mem_filter,Finset.mem_univ,true_and];exact hi)
  have hWmem : ∀ z∈O,W z∈monomialDomain Φ k e := by
    intro z hz
    change monomial k e (W z)∈Φ.target
    rw [(hWeq z hz).2]
    exact Φ.mapsTo_toFun (hWeq z hz).1.2
  obtain ⟨ℓ,⟨hℓs,hℓπ⟩,_⟩ := existsUnique_monomialLift hπ hΦsrc hflatC he
  have hFinj := fderiv_complex_monomial_inverse_injective hO hWs hWmem hℓs
    (hℓW ℓ hℓs hℓπ) hyO
  obtain ⟨Θ,hΘsrc,hΘ0,hΘeq⟩ := exists_recentred_coords hO hWs hyO hFinj
  have hWe : W y e=0 := by
    have h := congrArg (fun v : ComplexModel n => v e) (hWeq y hyO).2
    simpa [monomial_apply,hΦ0] using h
  have hWt : ∀ i : Fin n,i.val<k → W y i=0 := by
    intro i hi
    have h := congrArg (fun v : ComplexModel n => v i) (hWeq y hyO).2
    simpa [monomial_apply,not_le.mpr hi,hΦ0] using h
  refine ⟨e,(fun i => W y i),Θ,hΘsrc,hΘ0,he,hed,hWt,hWnormal,hWe,?_⟩
  intro z hz hzΘ
  obtain ⟨hzO,hcoord⟩ := hΘeq hz hzΘ
  change Θ.toFun (chartAt (ComplexModel n) y z)=W z-W y at hcoord
  refine ⟨(hWeq z hzO).1,?_,?_⟩
  · rw [hcoord,←actual_smooth_centre_monomial_recentre k e (W y) (W z) hWt hWe]
    exact (hWeq z hzO).2.symm
  · have hPlane : coordSubspace T=complexCoordinatePlane n d := coordSubspace_eq_complexCoordinatePlane d
    rw [hcoord,←hPlane,hNu z hzO,sub_mem_coordSubspace_iff hWy]
    exact and_iff_right heT

open Hironaka.HolomorphicIdealSheaves HironakaActualFixedFlatteningHSComparison
  HironakaRelativeNormalDeformationInitialRelations HironakaActualPointGeometricBennett
  HironakaActualPointExceptionalVanishing HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreCoherentDomain
  HironakaActualFlatCoordinateIntrinsicHS HironakaRelativeNormalCoherentTranslatedJets

/-- The WHOLE global geometric strict vanishing stalk, in this same square. -/
theorem strictFlattenedOriginIdeal_eq_model {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π) (z : Y) (k : ℕ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target)
    (j : Fin n) (b : Fin n → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) z).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) z z)=0)
    (hnormal : ∀ y : Y, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Θ.source →
      π y ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
        actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b (Θ.toFun (chartAt (ComplexModel n) z y)))
    (W : Set X) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) (strictTransform n π W)) z Θ) 0)=
      originalCoherentOriginIdeal (vanishingIdeal (n := n)
        (strictTransform n (actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b)
          (actualFixedFlatteningSet (π z) Φ W))) := by
  rw [originalFlattenedVanishingOriginIdeal_eq_model z Θ hΘsrc hΘ0]
  have heq := strictTransform_eq_fixedFlattening_preimage hπ z k Φ hΦsrc j b Θ hΘsrc hnormal W
  have htarget := actualFlattening_target_zero_mem z Θ hΘ0
  have hset : actualFixedFlatteningSet z Θ (strictTransform n π W) =ᶠ[𝓝 0]
      strictTransform n (actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b)
        (actualFixedFlatteningSet (π z) Φ W) := by
    apply eventuallyEq_set.mpr
    filter_upwards [Θ.isOpen_target.mem_nhds htarget] with q hq
    have h := congrArg (fun S => (⟨q,hq⟩ : (⟨Θ.target,Θ.isOpen_target⟩ : TopologicalSpace.Opens (ComplexModel n))) ∈ S) heq
    simpa only [actualFixedFlatteningSet,mem_inter_iff,mem_preimage,hq,true_and] using (iff_of_eq h)
  have hvan (S : Set (ComplexModel n)) :
      originalCoherentOriginIdeal (vanishingIdeal (n := n) S)=AnalyticGermDecomposition.vanishingIdeal S := by
    ext g
    obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
    rw [mk_mem_original_vanishing_origin_ideal_iff,AnalyticGermDecomposition.mem_vanishingIdeal_mk]
  rw [hvan,hvan]
  exact AnalyticGermDecomposition.vanishingIdeal_congr hset

theorem exists_actual_strict_contact_whole_stalk_chart {C N : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (y : Y) (k d : ℕ)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π y) (π y))=0)
    (hflatC : ∀ {x : X},x∈(chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) x∈Φ.source →
      (x∈C ↔ Φ.toFun (chartAt (ComplexModel n) (π y) x)∈complexCoordinatePlane n k))
    (hflatN : ∀ {x : X},x∈(chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) x∈Φ.source →
      (x∈N ↔ Φ.toFun (chartAt (ComplexModel n) (π y) x)∈complexCoordinatePlane n d))
    (hyN : y∈geoStrictTransform π C N) (W : Set X) :
    ∃ (e : Fin n) (b : Fin n → ℂ)
      (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y y)),
      Θ.source⊆(chartAt (ComplexModel n) y).target ∧
      Θ.toFun (chartAt (ComplexModel n) y y)=0 ∧
      k≤e.val ∧ e.val<d ∧
      (∀ i : Fin n,i.val<k → b i=0) ∧ (∀ i : Fin n,d ≤ i.val → b i=0) ∧ b e=0 ∧
      originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) (strictTransform n π W)) y Θ) 0)=
        originalCoherentOriginIdeal (vanishingIdeal (n := n)
          (strictTransform n (actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} e b)
            (actualFixedFlatteningSet (π y) Φ W))) ∧
      ∀ z : Y,z∈(chartAt (ComplexModel n) y).source →
        chartAt (ComplexModel n) y z∈Θ.source →
        π z∈flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel n) (π y) (π z))=
          actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} e b (Θ.toFun (chartAt (ComplexModel n) y z)) ∧
        (z∈geoStrictTransform π C N ↔
          Θ.toFun (chartAt (ComplexModel n) y z)∈complexCoordinatePlane n d) := by
  obtain ⟨e,b,Θ,hΘsrc,hΘ0,he,hed,hbt,hbn,hbe,hchart⟩ :=
    exists_actual_strict_contact_blowup_coordinates hπ y k d Φ hΦsrc hΦ0 hflatC hflatN hyN
  have hnormal : ∀ z : Y,z∈(chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z∈Θ.source →
      π z∈flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π y) (π z))=
        actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} e b (Θ.toFun (chartAt (ComplexModel n) y z)) :=
    fun z hz hzΘ => ⟨(hchart z hz hzΘ).1,(hchart z hz hzΘ).2.1⟩
  exact ⟨e,b,Θ,hΘsrc,hΘ0,he,hed,hbt,hbn,hbe,
    strictFlattenedOriginIdeal_eq_model hπ.contMDiff y k Φ hΦsrc e b Θ hΘsrc hΘ0 hnormal W,hchart⟩

end
end Hironaka.HironakaActualStrictContactBlowupCoordinates
