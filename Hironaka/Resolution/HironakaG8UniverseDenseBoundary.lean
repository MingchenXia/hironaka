import Hironaka.Resolution.HironakaG8UniverseBMTransport
import Hironaka.Resolution.HironakaG8DenseBoundaryEmbeddedResolution
import Hironaka.Resolution.HironakaG3UniverseShrinkManifold
import Hironaka.Resolution.HironakaG3UniverseAnalyticTransport
import Hironaka.Resolution.HironakaG3UniverseOrderedBoundary
import Hironaka.Resolution.HironakaG3UniverseLiftedTowerFootprint
import Hironaka.Resolution.HironakaMixedDimensionalBoundaryFiniteResolution

/-! Ambient-universe and dimension transport for the physical dense-boundary
embedded resolution, retaining every original and accumulated boundary slot. -/

set_option autoImplicit false

open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8UniverseDenseBoundary

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaEmbeddedAnalytic HironakaAdmissibleSequence RestrictEmptyTower
  HironakaG8UniverseBMTransport HironakaG8DenseBoundaryEmbeddedResolution HironakaG8SurfaceLimitEndpoint
  HironakaG11PresTowerState HironakaG8BFamilyPad
  HironakaG3UniverseSmallManifold HironakaG3UniverseShrinkManifold HironakaG3UniverseLiftManifold
  HironakaG3UniverseAnalyticTransport HironakaG3UniverseCarrierGeometry
  HironakaG3UniverseOrderedBoundary HironakaG3UniverseNormalCrossings G3UniverseLiftedTower
  G3UniverseLiftedTowerFootprint HironakaG3UniverseDiffeoDerivative MarkedIdealTowerTransport
  HironakaCoherentTransformExtension HironakaSharpActualFiniteChronologicalHistory
  NormalCrossingsInvariance HironakaMixedDimensionalBoundaryFiniteResolution

/-- The finite physical resolution and its full ordered boundary, with the
literal centre law at every prefix. -/
def DenseBoundaryResolution {n : ℕ} {X Y : CMfd.{u} n}
    (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) : Prop :=
  let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
  let F := singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H)
  let A := strictTransform n T.proj W
  let B := (geoTransformAlong M T).E
  IsAdmissibleBlowupSequence n X E F Y T.proj B ∧
  BMStages W E T ∧ IsClosedSubmanifold n A ∧ IsSNCDivisor n B ∧
  HasNormalCrossings n A B ∧ IsTransverse n A B ∧
  A ⊆ closure (A \ ⋃ H ∈ B, H) ∧
  ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ T.proj ∧
  IsProperMap T.proj ∧ Surjective T.proj ∧ T.proj '' A = W ∧
  IsIsomorphismOver n T.proj Fᶜ ∧
  (E = [] → exceptionalLocus n T.proj = T.proj ⁻¹' singularSet (n := n) W)

private theorem dimension_zero_boundary_empty {X : CMfd.{0} 0}
    (E : List (Set X)) (hE : IsSNCDivisor 0 E) :
    ∀ H ∈ E, H = ∅ := by
  intro H hH
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨S, _, hCard, _⟩ := hE.2 x
  have hBound := Finset.card_le_univ (S i)
  simp only [Fintype.card_fin] at hBound
  rw [hCard i hx] at hBound
  exact Nat.not_succ_le_zero 0 hBound

/-- The identity tower resolves every analytic carrier in dimension zero
and retains each original boundary slot. -/
theorem zero_dimensional_dense_boundary_resolution {X : CMfd.{0} 0} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := 0) W)
    (E : List (Set X)) (hE : IsSNCDivisor 0 E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H)) :
    DenseBoundaryResolution W E (BlowupTower.refl (X := X)) := by
  have hSmooth := low_ambient_dimension_analytic_smooth (by decide : 0 ≤ 1) W hW
  have hEmpty := dimension_zero_boundary_empty E hE
  have hNC : HasNormalCrossings 0 W E := by
    clear hE hDense
    induction E with
    | nil => exact hasNormalCrossings_nil_of_isClosedSubmanifold hSmooth
    | cons B E ih =>
      rw [hEmpty B List.mem_cons_self, hasNormalCrossings_cons_empty_iff]
      exact ih (fun H hH => hEmpty H (List.mem_cons_of_mem _ hH))
  have hTrans : IsTransverse 0 W E :=
    HironakaNormalCrossingsTransversality.isTransverse_of_hasNormalCrossings_of_subset_closure_diff hNC hDense
  have hS : singularSet (n := 0) W = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x h
    obtain ⟨d, hd⟩ := hSmooth.2 x (singularSet_subset W h)
    exact (mem_singularSet_iff.mp h).2 d hd
  change IsAdmissibleBlowupSequence 0 X E _ X id E ∧ True ∧ _
  simp only [BlowupTower.proj_refl, geoTransformAlong_refl, strictTransform_id hW.isClosed, image_id]
  exact ⟨IsAdmissibleBlowupSequence.refl, trivial, hSmooth, hE, hNC, hTrans, hDense,
    contMDiff_id, isProperMap_id, surjective_id, trivial,
    ⟨bijOn_id _, by rw [exceptionalLocus_id]; exact disjoint_empty _⟩,
    fun _ => by rw [exceptionalLocus_id, hS, preimage_empty]⟩

/-- The base-universe dense-boundary theorem in every dimension. In
dimension zero the actual identity tower retains all empty boundary slots. -/
theorem exists_small_dense_boundary_resolution {n : ℕ} {X : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hK : IsCompact (singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H))) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y), DenseBoundaryResolution W E T := by
  cases n with
  | succ m =>
    obtain ⟨Y, T, hAdm, hStages, hSmooth, hSNC, hNC, hTrans, hDenseT,
      hHolo, hProper, hSurj, hImage, hIso, hExc⟩ :=
      exists_embedded_resolution_of_dense_boundary_complement hW E hE hDense hK
    exact ⟨Y, T, hAdm, (bm_stages_iff_markOne W E T).mpr hStages, hSmooth, hSNC,
      hNC, hTrans, hDenseT, hHolo, hProper, hSurj, hImage, hIso, hExc⟩
  | zero => exact ⟨X, .refl, zero_dimensional_dense_boundary_resolution hW E hE hDense⟩

/-- Lift an actual finite resolution from a small biholomorphic ambient
manifold, preserving its full chronological boundary and stage laws. -/
theorem dense_boundary_resolution_of_small_biholomorphism
    {n : ℕ} {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₀)
    (W : Set X) (E : List (Set X))
    (hE₀ : IsSNCDivisor n (E.map (e.symm ⁻¹' ·)))
    (hSing₀ : singularSet (n := n) (e.symm ⁻¹' W) = e.symm ⁻¹' singularSet (n := n) W)
    (T₀ : BlowupTower X₀ Y₀) (hSmall : DenseBoundaryResolution (e.symm ⁻¹' W) (E.map (e.symm ⁻¹' ·)) T₀) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), DenseBoundaryResolution W E T := by
  let W₀ : Set X₀ := e.symm ⁻¹' W
  let E₀ : List (Set X₀) := E.map (e.symm ⁻¹' ·)
  let F := singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H)
  let F₀ := singularSet (n := n) W₀ ∪ (W₀ ∩ ⋃ H ∈ E₀, H)
  have hF₀ : F₀ = e.symm ⁻¹' F := by
    dsimp only [F₀, F, W₀, E₀]
    rw [hSing₀, ← HironakaEmbeddedBoundary.preimage_biUnion_list, preimage_union, preimage_inter]
  obtain ⟨hAdm₀, hStages₀, hSmooth₀, hSNC₀, hNC₀, _hTrans₀, hFinalDense₀,
    hHolo₀, hProper₀, hSurj₀, hImage₀, hIso₀, hExc₀⟩ := hSmall
  let M₀ : MarkedIdeal n X₀ := ⟨univ, E₀, vanishingIdeal (n := n) W₀, 1⟩
  let A₀ := strictTransform n T₀.proj W₀
  let B₀ := (geoTransformAlong M₀ T₀).E
  let lX := liftDiffeomorph.{u} X₀
  let lY := liftDiffeomorph.{u} Y₀
  let TL := liftTower.{u} T₀
  let WL := lX.symm ⁻¹' W₀
  let EL := E₀.map (lX.symm ⁻¹' ·)
  let b := e.trans lX
  let R := transport b TL
  let T := R.tower
  let a := R.back.trans lY.symm
  let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
  let A := strictTransform n T.proj W
  let B := (geoTransformAlong M T).E
  have hWL : b ⁻¹' WL = W := by ext x; simp [b, WL, W₀]
  have hEL : EL.map (b ⁻¹' ·) = E := by
    dsimp only [EL, E₀]
    rw [List.map_map, List.map_map]
    refine (List.map_congr_left (g := id) ?_).trans (List.map_id E)
    intro D _
    ext x
    simp [b]
  have hSNC_L : IsSNCDivisor n EL := transported_list_snc X₀ Homeomorph.ulift.symm E₀ hE₀
  have hStagesL : BMStages WL EL TL := lift_bm_stages W₀ E₀ hE₀ T₀ hStages₀
  have hStages : BMStages W E T := by
    rw [← hWL, ← hEL]
    exact rebase_bm_stages b WL EL hSNC_L TL hStagesL
  have hProj : T.proj = e.symm ∘ T₀.proj ∘ a := by
    funext z
    have hz := congrArg (fun x => e.symm (lX.symm x)) (proj_transport b TL z)
    change e.symm (lX.symm (lX (e (T.proj z)))) =
      e.symm (lX.symm (TL.proj (R.back z))) at hz
    rw [lX.symm_apply_apply, e.symm_apply_apply, liftTower_proj] at hz
    change T.proj z = e.symm (lX.symm (lX (T₀.proj (a z)))) at hz
    rw [lX.symm_apply_apply] at hz
    exact hz
  have hWback : e ⁻¹' W₀ = W := by ext x; simp [W₀]
  have hFback : e ⁻¹' F₀ = F := by rw [hF₀]; ext x; simp
  have hGood : e ⁻¹' F₀ᶜ = Fᶜ := by
    change (e ⁻¹' F₀)ᶜ = Fᶜ
    rw [hFback]
  have hA : A = a ⁻¹' A₀ := by
    have h : strictTransform n (e.symm ∘ T₀.proj ∘ a) (e ⁻¹' W₀) = a ⁻¹' A₀ :=
      conjugate_strictTransform a.symm e.symm T₀.proj hHolo₀ W₀
    rw [hWback] at h
    change strictTransform n T.proj W = _
    rw [hProj]
    exact h
  have hB : B = B₀.map (a ⁻¹' ·) := by
    let G := geometricTemplate (univ : Set X) E
    let G₀ := geometricTemplate (univ : Set X₀) E₀
    have hB₀' : (geoTransformAlong G₀ T₀).E = B₀ :=
      geoTransformAlong_E_eq_of_E_eq (𝔍 := G₀) (𝔪 := M₀) rfl T₀
    have hBL : (geoTransformAlong (geometricTemplate (univ : Set (liftCMfd.{u} X₀)) EL) TL).E =
        B₀.map (lY.symm ⁻¹' ·) :=
      (lift_bm_boundary_eq.{u} W₀ E₀ hE₀ T₀ hStages₀).trans
        (congrArg (List.map (lY.symm ⁻¹' ·)) hB₀')
    have hBR := rebase_bm_boundary_eq b WL EL hSNC_L TL hStagesL
    change (geoTransformAlong (geometricTemplate (univ : Set X) (EL.map (b ⁻¹' ·))) T).E =
      (geoTransformAlong (geometricTemplate (univ : Set (liftCMfd.{u} X₀)) EL) TL).E.map (R.back ⁻¹' ·) at hBR
    rw [hEL, hBL, List.map_map] at hBR
    have hBG : B = (geoTransformAlong G T).E :=
      geoTransformAlong_E_eq_of_E_eq (𝔍 := M) (𝔪 := G) rfl T
    exact hBG.trans hBR
  have hOver₀ : CentresOver F₀ T₀ := by
    apply centresOver_of_exceptionalDivisor_support_subset F₀ T₀
    rw [HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop M₀ hE₀.1 T₀]
    exact (HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop hAdm₀).2
  have hOver : CentresOver F T := by
    have hL := (liftTower_centresOver_iff.{u} F₀ T₀).mpr hOver₀
    have h := centresOver_rebase b (lX.symm ⁻¹' F₀) TL hL
    change CentresOver (b ⁻¹' (lX.symm ⁻¹' F₀)) T at h
    have hFootprint : b ⁻¹' (lX.symm ⁻¹' F₀) = F := by
      ext x
      change lX.symm (lX (e x)) ∈ F₀ ↔ x ∈ F
      rw [lX.symm_apply_apply]
      exact Set.ext_iff.mp hFback x
    rwa [hFootprint] at h
  have hAdm : IsAdmissibleBlowupSequence n X E F R.target T.proj B := by
    have h := isAdmissibleBlowupSequence_proj (geometricTemplate (univ : Set X) E) F T
      (bm_stage_test W E T hStages) hOver
    have hEq : (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E = B :=
      geoTransformAlong_E_eq_of_E_eq (𝔍 := geometricTemplate (univ : Set X) E) (𝔪 := M) rfl T
    rw [hEq] at h
    exact h
  have hSmooth : IsClosedSubmanifold n A := by
    rw [hA]
    have hLift : IsClosedSubmanifold n (lY.symm ⁻¹' A₀) :=
      transported_closedSubmanifold Homeomorph.ulift.symm A₀ hSmooth₀
    exact (isClosedSubmanifold_preimage_iff R.back).mpr hLift
  have hSNC : IsSNCDivisor n B := by
    rw [hB]
    have hLift : IsSNCDivisor n (B₀.map (lY.symm ⁻¹' ·)) :=
      transported_list_snc Y₀ Homeomorph.ulift.symm B₀ hSNC₀
    have h := isSNCDivisor_map_preimage (pullsBackCoordinates R.back) R.back.continuous hLift
    rw [List.map_map] at h
    exact h
  have hNC : HasNormalCrossings n A B := by
    rw [hA, hB]
    have hLift : HasNormalCrossings n (lY.symm ⁻¹' A₀) (B₀.map (lY.symm ⁻¹' ·)) :=
      transported_list_normalCrossings Y₀ Homeomorph.ulift.symm A₀ B₀ hNC₀
    have h := hasNormalCrossings_preimage (pullsBackCoordinates R.back) hLift
    rw [List.map_map] at h
    exact h
  have hDenseA : A ⊆ closure (A \ ⋃ H ∈ B, H) := by
    have hClosure := a.toHomeomorph.preimage_closure (A₀ \ ⋃ H ∈ B₀, H)
    simp only [Diffeomorph.coe_toHomeomorph] at hClosure
    rw [hA, hB, ← HironakaEmbeddedBoundary.preimage_biUnion_list, ← preimage_sdiff, ← hClosure]
    exact preimage_mono hFinalDense₀
  have hTrans :=
    HironakaNormalCrossingsTransversality.isTransverse_of_hasNormalCrossings_of_subset_closure_diff hNC hDenseA
  let P := e.symm ∘ T₀.proj ∘ a
  have hProj' : T.proj = P := hProj
  have hMap : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P ∧
      IsProperMap P ∧ Surjective P :=
    conjugate_map_properties a.symm e.symm T₀.proj hHolo₀ hProper₀ hSurj₀
  rw [← hProj'] at hMap
  have hImage : P '' strictTransform n P (e ⁻¹' W₀) = e ⁻¹' W₀ :=
    conjugate_non_erasure a.symm e.symm T₀.proj hHolo₀ W₀ hImage₀
  rw [← hProj', hWback] at hImage
  have hIso : IsIsomorphismOver n P (e ⁻¹' F₀ᶜ) :=
    conjugate_isomorphismOver a.symm e.symm T₀.proj hHolo₀ F₀ᶜ hIso₀
  rw [← hProj', hGood] at hIso
  refine ⟨R.target, T, hAdm, hStages, hSmooth, hSNC, hNC, hTrans, hDenseA,
    hMap.1, hMap.2.1, hMap.2.2, hImage, hIso, fun hNil => ?_⟩
  have hNil₀ : E₀ = [] := by simp [E₀, hNil]
  have h : exceptionalLocus n P = a ⁻¹' exceptionalLocus n T₀.proj :=
    conjugate_exceptionalLocus a.symm e.symm T₀.proj hHolo₀
  rw [← hProj', hExc₀ hNil₀] at h
  rw [h, hProj]
  ext z
  change T₀.proj (a z) ∈ singularSet (n := n) W₀ ↔ e.symm (T₀.proj (a z)) ∈ singularSet (n := n) W
  rw [hSing₀]
  rfl


/-- In every dimension and universe, the dense-boundary result produces
one finite actual tower on the original ambient manifold. -/
theorem exists_embedded_resolution_of_dense_boundary_complement_all_universes
    {n : ℕ} {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hK : IsCompact (singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H))) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), DenseBoundaryResolution W E T := by
  let X₀ := shrinkCMfd X
  let e := shrinkDiffeomorph X
  let : Small.{0} X := complex_manifold_small X
  let W₀ : Set X₀ := e.symm ⁻¹' W
  let E₀ : List (Set X₀) := E.map (e.symm ⁻¹' ·)
  let F := singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H)
  let F₀ := singularSet (n := n) W₀ ∪ (W₀ ∩ ⋃ H ∈ E₀, H)
  have hW₀ : IsComplexAnalyticSubset (n := n) W₀ :=
    (transported_analytic_iff (Shrink.homeomorph X) W).2 hW
  have hE₀ : IsSNCDivisor n E₀ := transported_list_snc X (Shrink.homeomorph X) E hE
  have hSing₀ : singularSet (n := n) W₀ = e.symm ⁻¹' singularSet (n := n) W :=
    transported_singular_set (Shrink.homeomorph X) W
  have hF₀ : F₀ = e.symm ⁻¹' F := by
    dsimp only [F₀, F, W₀, E₀]
    rw [hSing₀, ← HironakaEmbeddedBoundary.preimage_biUnion_list, preimage_union, preimage_inter]
  have hDense₀ : W₀ ⊆ closure (W₀ \ ⋃ H ∈ E₀, H) := by
    dsimp only [W₀, E₀]
    have hClosure := e.symm.toHomeomorph.preimage_closure (W \ ⋃ H ∈ E, H)
    simp only [Diffeomorph.coe_toHomeomorph] at hClosure
    rw [← HironakaEmbeddedBoundary.preimage_biUnion_list, ← preimage_sdiff, ← hClosure]
    exact preimage_mono hDense
  have hK₀ : IsCompact F₀ := hF₀.symm ▸ e.symm.toHomeomorph.isProperMap.isCompact_preimage hK
  obtain ⟨Y₀, T₀, hSmall⟩ := exists_small_dense_boundary_resolution hW₀ E₀ hE₀ hDense₀ hK₀
  exact dense_boundary_resolution_of_small_biholomorphism e W E hE₀ hSing₀ T₀ hSmall

end
end Hironaka.HironakaG8UniverseDenseBoundary
