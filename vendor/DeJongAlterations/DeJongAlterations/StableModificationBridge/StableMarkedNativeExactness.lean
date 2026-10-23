/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableMarkedNativeCokernel

/-! Native injectivity and off-mark surjectivity, derived from the actual original
canonical section and integral source. Blueprint: `stable-marked-native-exactness.tex`. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace DeJongAlterations.StableModificationBridge.StableMarkedNativeExactness
open StableModification StableModification.Projectivity Cohomology
open StableMarkedNativePullback
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private structure FrameChart {X Y : Scheme.{u}} (E : LocalEquations X) (M : X.Modules)
    (ν : Y ⟶ X) (W₀ : Y.Opens) (y : Y) where
  i : E.ι
  W : X.Opens
  affineW : IsAffineOpen W
  le_chart : W ≤ E.U i
  σ : Γ(M, W)
  free : IsFreeGenerator M σ
  V : Y.Opens
  affineV : IsAffineOpen V
  mem : y ∈ V
  le_orig : V ≤ W₀
  le_preimage : V ≤ ν ⁻¹ᵁ W

private theorem exists_frameChart {X Y : Scheme.{u}} (E : LocalEquations X) (M : X.Modules)
    (hM : Omega.IsInvertibleModule M) (ν : Y ⟶ X) (W₀ : Y.Opens) (y : Y) (hy : y ∈ W₀) :
    Nonempty (FrameChart E M ν W₀ y) := by
  obtain ⟨U, σ, hxU, hσ⟩ := exists_isFreeGenerator hM (ν y)
  obtain ⟨i, hi⟩ := E.toLineBundleData.exists_mem_U (ν y)
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (x := ν y) (U := U ⊓ E.U i) ⟨hxU, hi⟩
  obtain ⟨V, hV, hyV, hVW⟩ := exists_isAffineOpen_mem_and_subset
    (x := y) (U := W₀ ⊓ ν ⁻¹ᵁ W) ⟨hy, hxW⟩
  exact ⟨⟨i, W, hW, hWU.trans inf_le_right,
    M.presheaf.map (homOfLE (hWU.trans inf_le_left)).op σ,
    hσ.restrict (hWU.trans inf_le_left), V, hV, hyV,
    hVW.trans inf_le_left, hVW.trans inf_le_right⟩⟩

private theorem equation_basicOpen {X Y : Scheme.{u}} (E : LocalEquations X)
    (ν : Y ⟶ X) {i : E.ι} {W : X.Opens} (hWi : W ≤ E.U i)
    {V : Y.Opens} (hVW : V ≤ ν ⁻¹ᵁ W) :
    Y.basicOpen (ν.appLE W V hVW (res hWi (E.f i))) =
      V ⊓ ν ⁻¹ᵁ E.canonicalSection.nonvanishingLocus := by
  rw [Scheme.basicOpen_appLE, Scheme.basicOpen_res]
  apply le_antisymm
  · intro y hy
    refine ⟨hy.1, ?_⟩
    have hm : ν y ∈ E.canonicalSection.nonvanishingLocus ⊓ E.U i := by
      rw [E.nonvanishingLocus_canonicalSection_inf]
      exact hy.2.2
    exact hm.1
  · intro y hy
    refine ⟨hy.1, hVW hy.1, ?_⟩
    have hm : ν y ∈ E.canonicalSection.nonvanishingLocus ⊓ E.U i :=
      ⟨hy.2, hWi (hVW hy.1)⟩
    rwa [E.nonvanishingLocus_canonicalSection_inf] at hm

/-- The WHOLE native pulled original marking map is injective on EVERY open,
from genuine invertibility and original generic-point nonvanishing. -/
theorem injective_app {X Y : Scheme.{u}} [IsIntegral Y] (E : LocalEquations X)
    (M : X.Modules) (hM : Omega.IsInvertibleModule M) (ν : Y ⟶ X)
    (hη : ν (genericPoint Y) ∈ E.canonicalSection.nonvanishingLocus) (W₀ : Y.Opens) :
    Function.Injective ((pullbackMarkedTwistMap E M ν).app W₀) := by
  let : M.IsQuasicoherent := Omega.RosenlichtComponent.isQuasicoherent_of_isInvertibleModule M hM
  apply Omega.RosenlichtComponent.injective_app_of_local
  intro U y hy
  obtain ⟨C⟩ := exists_frameChart E M hM ν U y hy
  let t := ν.appLE C.W C.V C.le_preimage (res C.le_chart (E.f C.i))
  have hηV : genericPoint Y ∈ C.V :=
    ((genericPoint_spec Y).mem_open_set_iff C.V.isOpen).mpr ⟨y, trivial, C.mem⟩
  have ht : t ≠ 0 := by
    intro ht
    have hmem : genericPoint Y ∈ Y.basicOpen t := by
      rw [equation_basicOpen]
      exact ⟨hηV, hη⟩
    rw [ht, Y.basicOpen_zero] at hmem
    exact hmem.elim
  let : Nonempty C.V := ⟨⟨y, C.mem⟩⟩
  let : IsDomain Γ(Y, C.V) := IsIntegral.component_integral C.V
  have hσ := Omega.RosenlichtComponent.bijective_smul_pullbackSectionLE ν M
    C.affineW C.affineV C.le_preimage C.σ (by simpa using C.free C.W le_rfl)
  have hτ := bijective_target_frame E M ν C.affineW C.le_chart C.affineV C.le_preimage
    C.σ (by simpa using C.free C.W le_rfl)
  refine ⟨C.V, C.le_orig, C.mem, ?_⟩
  intro a b hab
  obtain ⟨r, rfl⟩ := hσ.2 a
  obtain ⟨s, rfl⟩ := hσ.2 b
  have he := hτ.1 ((pullbackMarkedTwistMap_frame E M ν C.le_chart C.le_preimage C.σ r).symm.trans
    (hab.trans (pullbackMarkedTwistMap_frame E M ν C.le_chart C.le_preimage C.σ s)))
  have hrs : r = s := mul_right_cancel₀ ht he
  rw [hrs]

/-- On ANY original open contained in the exact original canonical nonvanishing
preimage, the WHOLE actual native marking map is surjective. -/
theorem surjective_app_of_nonvanishing {X Y : Scheme.{u}} [IsIntegral Y]
    (E : LocalEquations X) (M : X.Modules) (hM : Omega.IsInvertibleModule M) (ν : Y ⟶ X)
    (hη : ν (genericPoint Y) ∈ E.canonicalSection.nonvanishingLocus)
    (W₀ : Y.Opens) (hW₀ : W₀ ≤ ν ⁻¹ᵁ E.canonicalSection.nonvanishingLocus) :
    Function.Surjective ((pullbackMarkedTwistMap E M ν).app W₀) := by
  let : M.IsQuasicoherent := Omega.RosenlichtComponent.isQuasicoherent_of_isInvertibleModule M hM
  let α := pullbackMarkedTwistMap E M ν
  let F := (Scheme.Modules.pullback ν).obj M
  let G := (Scheme.Modules.pullback ν).obj (E.toLineBundleData.twist M 1)
  have hlocal : ∀ y : W₀, ∃ (V : Y.Opens) (hV : V ≤ W₀), y.1 ∈ V ∧
      Function.Surjective (α.app V) := by
    intro y
    obtain ⟨C⟩ := exists_frameChart E M hM ν W₀ y.1 y.2
    let t := ν.appLE C.W C.V C.le_preimage (res C.le_chart (E.f C.i))
    have ht : IsUnit t := by
      apply isUnit_of_basicOpen_eq
      rw [equation_basicOpen]
      exact inf_eq_left.mpr (C.le_orig.trans hW₀)
    have hτ := bijective_target_frame E M ν C.affineW C.le_chart C.affineV C.le_preimage
      C.σ (by simpa using C.free C.W le_rfl)
    refine ⟨C.V, C.le_orig, C.mem, ?_⟩
    intro z
    obtain ⟨r, rfl⟩ := hτ.2 z
    refine ⟨(r * ↑ht.unit⁻¹) • pullbackSectionLE ν M C.le_preimage C.σ, ?_⟩
    change (pullbackMarkedTwistMap E M ν).app C.V _ = _
    rw [pullbackMarkedTwistMap_frame]
    change ((r * ↑ht.unit⁻¹) * t) • _ = r • _
    rw [mul_assoc, ht.val_inv_mul, mul_one]
  intro s
  choose V hV hyV hv using hlocal
  choose t ht using fun y : W₀ => hv y (G.presheaf.map (homOfLE (hV y)).op s)
  have hcov : W₀ ≤ ⨆ y : W₀, V y := fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩
  obtain ⟨z, hz⟩ := Scheme.Modules.exists_glue F V hcov hV t (by
    intro y y'
    apply injective_app E M hM ν hη
    rw [Scheme.Modules.Hom.app_map, Scheme.Modules.Hom.app_map, ht, ht,
      Cohomology.presheaf_map_map G _ _ (inf_le_left.trans (hV y)),
      Cohomology.presheaf_map_map G _ _ (inf_le_right.trans (hV y'))])
  refine ⟨z, Scheme.Modules.eq_of_restrict_eq G V hcov hV _ _ fun y => ?_⟩
  rw [← Scheme.Modules.Hom.app_map, hz, ht]

end DeJongAlterations.StableModificationBridge.StableMarkedNativeExactness
