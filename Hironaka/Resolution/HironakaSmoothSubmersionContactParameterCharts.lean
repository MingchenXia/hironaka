/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionContactCoordinates
import Hironaka.Analytic.RegularLocusDense
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionContactParameterCharts
open Hironaka.RegularLocusDense Hironaka.BlowupSequences BlowupTowers
  HironakaSmoothSubmersionRelativeDifferentialIdeals HironakaSmoothSubmersionAdaptedProductCoordinates
  HironakaSmoothSubmersionContactCoefficientRestriction HironakaSmoothSubmersionContactCoordinates
  HironakaSmoothSubmersionTangentContact HironakaSmoothSubmersionMonomialOrdering
  GiraudAlong TangentDirectionAlong BlowupFlatCoordinates Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeal GermIdealOrder HironakaSmoothSubmersionMonomialOrdering
  HironakaSmoothSubmersionRelativeOrder HironakaSmoothSubmersionCoefficientIdeals
noncomputable section

theorem actual_projection_plane_inclusion (n a t : ℕ) (w : ComplexModel (a+t)) :
    actualTargetProjectionLinear n t (coordinateInclusion (n+t) (a+t) w) =
      coordinateInclusion n a (actualTargetProjectionLinear a t w) := by
  ext j
  rw [actualTargetProjectionLinear_apply,adaptedTargetProjection_apply,rotateBlocks_target_eq,
    coordinateInclusion_apply]
  by_cases hj : j.val < a
  · have hja : (actualTargetIndex n t j).val < a+t := by dsimp [actualTargetIndex];omega
    rw [dif_pos hja,coordinateInclusion_apply,dif_pos hj,
      actualTargetProjectionLinear_apply,adaptedTargetProjection_apply,rotateBlocks_target_eq]
    rfl
  · have hja : ¬ (actualTargetIndex n t j).val < a+t := by dsimp [actualTargetIndex];omega
    rw [dif_neg hja,coordinateInclusion_apply,dif_neg hj]

theorem actual_target_projection_isSubmersionOfComplement (a t : ℕ) :
    Manifold.IsSubmersionOfComplement (ComplexModel t)
      𝓘(ℂ, ComplexModel (a+t)) 𝓘(ℂ, ComplexModel a) ∞ (actualTargetProjectionLinear a t) := by
  intro w
  let e := (fibreFirstSplit a t).trans (ContinuousLinearEquiv.prodComm ℂ (ComplexModel t) (ComplexModel a))
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts e
    (OpenPartialHomeomorph.refl (ComplexModel (a+t))) (OpenPartialHomeomorph.refl (ComplexModel a))
  · exact mem_univ _
  · exact mem_univ _
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn <;> exact contMDiffOn_id
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn <;> exact contMDiffOn_id
  · intro z hz
    exact mem_univ _
  · intro z hz
    rfl

variable {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}

def restrictedOpenMap (V : TopologicalSpace.Opens Y) (U : TopologicalSpace.Opens X)
    (hVU : MapsTo f V U) : V → U := fun y => ⟨f y.val,hVU y.property⟩

theorem restrictedOpenMap_isSubmersionOfComplement
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (hf : Manifold.IsSubmersionOfComplement F 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (V : TopologicalSpace.Opens Y) (U : TopologicalSpace.Opens X) (hVU : MapsTo f V U) :
    Manifold.IsSubmersionOfComplement F
      𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (restrictedOpenMap V U hVU) := by
  intro y
  let h := hf y.val
  have hV : Nonempty V := ⟨y⟩
  have hU : Nonempty U := ⟨restrictedOpenMap V U hVU y⟩
  let a := V.openPartialHomeomorphSubtypeCoe hV
  let b := U.openPartialHomeomorphSubtypeCoe hU
  let d := a.trans h.domChart
  let c := b.trans h.codChart
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts h.equiv d c
  · exact ⟨mem_univ _,h.mem_domChart_source⟩
  · exact ⟨mem_univ _,h.mem_codChart_source⟩
  · exact restrictedChart_mem_maximal V hV h.domChart h.domChart_mem_maximalAtlas
  · exact restrictedChart_mem_maximal U hU h.codChart h.codChart_mem_maximalAtlas
  · intro z hz
    exact ⟨mem_univ _,h.source_subset_preimage_source hz.2⟩
  · intro z hz
    have hz' : z ∈ d.target := by simpa [mfld_simps] using hz
    have ha : (a.symm (h.domChart.symm z)).val = h.domChart.symm z := a.right_inv hz'.2
    have hzo : z ∈ (h.domChart.extend 𝓘(ℂ, ComplexModel m)).target := by
      simpa [mfld_simps] using hz'.1
    have he := h.writtenInCharts hzo
    simpa [c,d,b,OpenPartialHomeomorph.extend,Function.comp_def,mfld_simps,restrictedOpenMap,ha] using he

def parameterOpen {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (a : ℕ) :
    TopologicalSpace.Opens (ComplexModel a) :=
  ⟨coordinateInclusion n a ⁻¹' Φ.target,
    Φ.isOpen_target.preimage (coordinateInclusion n a).continuous⟩

def parameterMap {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (a : ℕ) :
    ComplexModel a → X := fun w => flatInv Φ (coordinateInclusion n a w)

theorem parameterMap_flat_dictionary {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (a : ℕ)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (w : ComplexModel a) (hw : w ∈ parameterOpen Φ a) :
    parameterMap Φ a w ∈ flatDomain Φ ∧
      flatMap Φ (parameterMap Φ a w) = coordinateInclusion n a w :=
  ⟨flatInv_mem_flatDomain hw hΦsrc,flatMap_flatInv hw hΦsrc⟩

theorem parameterMap_zero {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (a : ℕ)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) :
    (0 : ComplexModel a) ∈ parameterOpen Φ a ∧ parameterMap Φ a 0 = x := by
  have hzero : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  refine ⟨?_,?_⟩
  · change coordinateInclusion n a 0 ∈ Φ.target
    simpa only [map_zero] using hzero
  · change flatInv Φ (coordinateInclusion n a 0) = x
    rw [map_zero,flatInv_zero h0]

theorem parameterMap_roundtrip {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (a : ℕ) (ha : a ≤ n)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) :
    (∀ w ∈ parameterOpen Φ a,
      coordinateProjection n a (flatMap Φ (parameterMap Φ a w)) = w) ∧
    ∀ z ∈ flatDomain Φ, flatMap Φ z ∈ complexCoordinatePlane n a →
      coordinateProjection n a (flatMap Φ z) ∈ parameterOpen Φ a ∧
      parameterMap Φ a (coordinateProjection n a (flatMap Φ z)) = z := by
  constructor
  · intro w hw
    rw [(parameterMap_flat_dictionary Φ a hΦsrc w hw).2,
      coordinateProjection_coordinateInclusion ha]
  · intro z hz hplane
    have he := coordinateInclusion_coordinateProjection hplane
    refine ⟨?_,?_⟩
    · change coordinateInclusion n a (coordinateProjection n a (flatMap Φ z)) ∈ Φ.target
      rw [he]
      exact flatMap_mem_target hz
    · change flatInv Φ (coordinateInclusion n a (coordinateProjection n a (flatMap Φ z))) = z
      rw [he,flatInv_flatMap hz]

theorem parameterMap_contMDiffOn {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (a : ℕ)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) :
    ContMDiffOn 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel n) ∞
      (parameterMap Φ a) (parameterOpen Φ a) := by
  intro w hw
  have hi : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      Φ.invFun (coordinateInclusion n a w) :=
    (contDiffAt_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target hw).contMDiffAt
  have ht := hΦsrc (Φ.mapsTo_invFun hw)
  have hc := (contMDiffOn_chart_symm (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) (x := x)).contMDiffAt
    ((chartAt (ComplexModel n) x).open_target.mem_nhds ht)
  exact ((hc.comp (coordinateInclusion n a w) hi).comp w
    ((coordinateInclusion n a).contDiff (n := ∞)).contDiffAt.contMDiffAt).contMDiffWithinAt

theorem adapted_parameter_square {t : ℕ} {Z : CMfd.{u} (n+t)} {g : Z → X} {y : Z}
    (hg : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ g y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (g y) (g y)))
    (_hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (g y)).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) (g y) (g y)) = 0) (a : ℕ) :
    let Γ := adaptedCoordinates hg Φ h0
    MapsTo (actualTargetProjectionLinear a t) (parameterOpen Γ (a+t)) (parameterOpen Φ a) ∧
    ∀ w ∈ parameterOpen Γ (a+t),
      g (parameterMap Γ (a+t) w) = parameterMap Φ a (actualTargetProjectionLinear a t w) := by
  dsimp only
  let Γ := adaptedCoordinates hg Φ h0
  have hΓsrc := (adaptedCoordinates_dictionary hg Φ h0).1
  constructor
  · intro w hw
    have hz := (parameterMap_flat_dictionary Γ (a+t) hΓsrc w hw).1
    have hd := (adaptedCoordinates_dictionary hg Φ h0).2.2 _ hz
    have hp := adaptedCoordinates_flatMap_projection hg Φ h0 _ hz
    rw [(parameterMap_flat_dictionary Γ (a+t) hΓsrc w hw).2,
      actual_projection_plane_inclusion] at hp
    change coordinateInclusion n a (actualTargetProjectionLinear a t w) ∈ Φ.target
    rw [hp]
    exact flatMap_mem_target hd.1
  · intro w hw
    have hs := adaptedCoordinates_inverse_projection hg Φ h0
      (coordinateInclusion (n+t) (a+t) w) hw
    rw [actual_projection_plane_inclusion] at hs
    exact hs

/-- Only an internally produced output, never an assumed chart certificate. -/
private def JointContactParameters {m : ℕ} {Y : CMfd.{u} m}
    (f : Y → X) (N U : Set X) (u : X → ℂ) (y : Y) : Prop :=
  ∃ (k t : ℕ)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (Γ : LocalHolomorphicEquivAt (n := m) (chartAt (ComplexModel m) y y)),
    m = n+t ∧ 0 < k ∧ k ≤ n ∧
    Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target ∧
    Γ.source ⊆ (chartAt (ComplexModel m) y).target ∧
    Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0 ∧
    Γ.toFun (chartAt (ComplexModel m) y y) = 0 ∧ flatDomain Φ ⊆ U ∧
    (∀ z ∈ flatDomain Φ,
      (z ∈ N ↔ flatMap Φ z ∈ complexCoordinatePlane n k) ∧
      (z ∈ contactCarrier N U u ↔ flatMap Φ z ∈ complexCoordinatePlane n (k-1))) ∧
    (∀ z ∈ flatDomain Γ, f z ∈ flatDomain Φ ∧
      (f z ∈ N ↔ flatMap Γ z ∈ complexCoordinatePlane m (k+t)) ∧
      (f z ∈ contactCarrier N U u ↔ flatMap Γ z ∈ complexCoordinatePlane m ((k-1)+t))) ∧
    0 ∈ parameterOpen Φ (k-1) ∧ 0 ∈ parameterOpen Γ ((k-1)+t) ∧
    parameterMap Φ (k-1) 0 = f y ∧ parameterMap Γ ((k-1)+t) 0 = y ∧
    ContMDiffOn 𝓘(ℂ, ComplexModel (k-1)) 𝓘(ℂ, ComplexModel n) ∞
      (parameterMap Φ (k-1)) (parameterOpen Φ (k-1)) ∧
    ContMDiffOn 𝓘(ℂ, ComplexModel ((k-1)+t)) 𝓘(ℂ, ComplexModel m) ∞
      (parameterMap Γ ((k-1)+t)) (parameterOpen Γ ((k-1)+t)) ∧
    (∀ w ∈ parameterOpen Φ (k-1),
      parameterMap Φ (k-1) w ∈ contactCarrier N U u ∧
      coordinateProjection n (k-1) (flatMap Φ (parameterMap Φ (k-1) w)) = w) ∧
    (∀ z ∈ flatDomain Φ, z ∈ contactCarrier N U u →
      coordinateProjection n (k-1) (flatMap Φ z) ∈ parameterOpen Φ (k-1) ∧
      parameterMap Φ (k-1) (coordinateProjection n (k-1) (flatMap Φ z)) = z) ∧
    (∀ w ∈ parameterOpen Γ ((k-1)+t),
      f (parameterMap Γ ((k-1)+t) w) ∈ contactCarrier N U u ∧
      coordinateProjection m ((k-1)+t) (flatMap Γ (parameterMap Γ ((k-1)+t) w)) = w) ∧
    (∀ z ∈ flatDomain Γ, f z ∈ contactCarrier N U u →
      coordinateProjection m ((k-1)+t) (flatMap Γ z) ∈ parameterOpen Γ ((k-1)+t) ∧
      parameterMap Γ ((k-1)+t) (coordinateProjection m ((k-1)+t) (flatMap Γ z)) = z) ∧
    ∃ hMaps : MapsTo (actualTargetProjectionLinear (k-1) t)
        (parameterOpen Γ ((k-1)+t)) (parameterOpen Φ (k-1)),
      (∀ w ∈ parameterOpen Γ ((k-1)+t),
        f (parameterMap Γ ((k-1)+t) w) =
          parameterMap Φ (k-1) (actualTargetProjectionLinear (k-1) t w)) ∧
      Manifold.IsSubmersionOfComplement (ComplexModel t)
        𝓘(ℂ, ComplexModel ((k-1)+t)) 𝓘(ℂ, ComplexModel (k-1)) ∞
        (restrictedOpenMap (X := CMfd.of (n := k-1) (ComplexModel (k-1)))
          (Y := CMfd.of (n := (k-1)+t) (ComplexModel ((k-1)+t)))
          (f := actualTargetProjectionLinear (k-1) t)
          (parameterOpen Γ ((k-1)+t)) (parameterOpen Φ (k-1)) hMaps)

theorem exists_actual_joint_contact_parameters
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} (hI : I.IsCoherent) {N : Set X} (hN : IsClosedSubmanifold n N)
    {μ : ℕ} {U : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong N I μ U u)
    (y : Y) (hy : y ∈ f ⁻¹' contactCarrier N U u) :
    JointContactParameters f N U u y := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le (dimension_le_of_submersionAt (hf.isSubmersionAt y))
  obtain ⟨k,l,Φ,hk,hl,hΦsrc,hΦ0,hΦU,hΦ⟩ := exists_original_contact_coordinates hI hN hu (f y) hy
  have hkn : k ≤ n := by have := l.isLt; omega
  have han : k-1 ≤ n := by omega
  let Γ := adaptedCoordinates (hf.isSubmersionAt y) Φ hΦ0
  obtain ⟨hΓsrc,hΓ0,hΓ⟩ := adaptedCoordinates_dictionary (hf.isSubmersionAt y) Φ hΦ0
  have hNΓ : ∀ z ∈ flatDomain Γ,
      f z ∈ N ↔ flatMap Γ z ∈ complexCoordinatePlane (n+t) (k+t) := by
    intro z hz
    have hp := adaptedCoordinates_whole_centre (hf.isSubmersionAt y)
      Φ hΦ0 N k (fun w hw => (hΦ w hw).1) z hz
    change f z ∈ N ↔ flatMap Γ z ∈ complexCoordinatePlane (n+t) (t+k) at hp
    simpa only [Nat.add_comm] using hp
  have hCΓ : ∀ z ∈ flatDomain Γ,
      f z ∈ contactCarrier N U u ↔ flatMap Γ z ∈ complexCoordinatePlane (n+t) ((k-1)+t) := by
    intro z hz
    have hp := adaptedCoordinates_whole_centre (hf.isSubmersionAt y)
      Φ hΦ0 (contactCarrier N U u) (k-1) (fun w hw => (hΦ w hw).2.1) z hz
    change f z ∈ contactCarrier N U u ↔
      flatMap Γ z ∈ complexCoordinatePlane (n+t) (t+(k-1)) at hp
    simpa only [Nat.add_comm] using hp
  have hpΦ := parameterMap_roundtrip Φ (k-1) han hΦsrc
  have hpΓ := parameterMap_roundtrip Γ ((k-1)+t) (Nat.add_le_add_right han t) hΓsrc
  obtain ⟨hMaps,hSquare⟩ := adapted_parameter_square (hf.isSubmersionAt y) Φ hΦsrc hΦ0 (k-1)
  refine ⟨k,t,Φ,Γ,rfl,hk,hkn,hΦsrc,hΓsrc,hΦ0,hΓ0,hΦU,?_,?_,
    (parameterMap_zero Φ (k-1) hΦ0).1,(parameterMap_zero Γ ((k-1)+t) hΓ0).1,
    (parameterMap_zero Φ (k-1) hΦ0).2,(parameterMap_zero Γ ((k-1)+t) hΓ0).2,
    parameterMap_contMDiffOn Φ (k-1) hΦsrc,parameterMap_contMDiffOn Γ ((k-1)+t) hΓsrc,
    ?_,?_,?_,?_,hMaps,hSquare,?_⟩
  · intro z hz
    exact ⟨(hΦ z hz).1,(hΦ z hz).2.1⟩
  · intro z hz
    exact ⟨(hΓ z hz).1,hNΓ z hz,hCΓ z hz⟩
  · intro w hw
    have hd := parameterMap_flat_dictionary Φ (k-1) hΦsrc w hw
    refine ⟨(hΦ _ hd.1).2.1.mpr ?_,hpΦ.1 w hw⟩
    rw [hd.2]
    exact coordinateInclusion_mem_complexCoordinatePlane w
  · intro z hz hcz
    exact hpΦ.2 z hz ((hΦ z hz).2.1.mp hcz)
  · intro w hw
    have hd := parameterMap_flat_dictionary Γ ((k-1)+t) hΓsrc w hw
    refine ⟨(hCΓ _ hd.1).mpr ?_,hpΓ.1 w hw⟩
    rw [hd.2]
    exact coordinateInclusion_mem_complexCoordinatePlane w
  · intro z hz hcz
    exact hpΓ.2 z hz ((hCΓ z hz).mp hcz)
  · exact restrictedOpenMap_isSubmersionOfComplement
      (X := CMfd.of (n := k-1) (ComplexModel (k-1)))
      (Y := CMfd.of (n := (k-1)+t) (ComplexModel ((k-1)+t)))
      (f := actualTargetProjectionLinear (k-1) t)
      (actual_target_projection_isSubmersionOfComplement (k-1) t) _ _ hMaps

theorem exists_original_only_joint_contact_parameters
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    (hd : 1 ≤ M.d) (y : Y) (hy : y ∈ (markedPullback (m := m) f M).cosupp)
    (hmax : ¬ OrderGE n M.N M.ideal (f y) (M.d+1)) :
    ∃ (U : TopologicalSpace.Opens X) (u : X → ℂ), f y ∈ U ∧
      IsTangentDirectionAlong M.N M.ideal M.d (U : Set X) u ∧
      IsTangentDirectionAlong (f ⁻¹' M.N) (GermIdeal.pullback (m := m) f M.ideal)
        M.d (f ⁻¹' (U : Set X)) (u ∘ f) ∧
      JointContactParameters f M.N (U : Set X) u y := by
  obtain ⟨U,u,hyU,hu,hup,_,_,hC,_⟩ := exists_joint_original_closed_contacts hf hI hN hd y hy hmax
  have hyt : f y ∈ cosupport n M.N M.ideal M.d := by
    have hyp : y ∈ f ⁻¹' cosupport n M.N M.ideal M.d := by
      rw [← cosupport_preimage_eq hf hI M.N M.d]
      exact hy
    exact hyp
  exact ⟨U,u,hyU,hu,hup,exists_actual_joint_contact_parameters hf hI hN hu y (hC ⟨hyt,hyU⟩)⟩

end
end Hironaka.HironakaSmoothSubmersionContactParameterCharts
