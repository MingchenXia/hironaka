/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableMarkedNativePullback
import DeJongAlterations.StableModification.Omega.RosenlichtComponentDegree

/-! The native section cokernel is the quotient by the SAME original pulled-back
Cartier equation, with the ORIGINAL coefficient-field action. Blueprint:
`stable-marked-native-cokernel.tex`. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace DeJongAlterations.StableModificationBridge.StableMarkedNativeCokernel
open StableModification StableModification.Projectivity Cohomology Omega.RosenlichtComponent
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- Two actual free frames and the whole original coefficient formula identify
the WHOLE native section cokernel with the SAME principal-ideal quotient. -/
def sectionsCokerEquivQuotient {Y : Scheme.{u}} {K : Type u} [Field K]
    (c : K →+* Γ(Y, ⊤)) {F G : Y.Modules} (α : F ⟶ G) (W : Y.Opens)
    (σ : Γ(F, W)) (τ : Γ(G, W))
    (hσ : Function.Bijective (fun r : Γ(Y, W) => r • σ))
    (hτ : Function.Bijective (fun r : Γ(Y, W) => r • τ))
    (t : Γ(Y, W))
    (ht : ∀ r : Γ(Y, W), α.app W (r • σ) = (r * t) • τ) :
    letI := (sectionsRingHom c (le_top : W ≤ ⊤)).toAlgebra
    sectionsCoker c α W ≃ₗ[K] (Γ(Y, W) ⧸ Ideal.span {t}) := by
  letI := (sectionsRingHom c (le_top : W ≤ ⊤)).toAlgebra
  let L₀ : Γ(Y, W) →ₗ[K] sectionsModuleCat G c W le_top :=
    { toFun := fun r => r • τ
      map_add' := fun r s => add_smul r s τ
      map_smul' := fun k r => by
        change (sectionsRingHom c (le_top : W ≤ ⊤) k * r) • τ =
          sectionsRingHom c (le_top : W ≤ ⊤) k • (r • τ)
        exact mul_smul _ _ _ }
  let P := LinearMap.range (sectionsMap c α W le_top).hom
  let L : Γ(Y, W) →ₗ[K] sectionsCoker c α W := P.mkQ ∘ₗ L₀
  have hL : Function.Surjective L := (Submodule.mkQ_surjective P).comp hτ.2
  have hker : LinearMap.ker L = (Ideal.span {t}).restrictScalars K := by
    ext r
    rw [LinearMap.mem_ker]
    change Submodule.Quotient.mk (p := P) (L₀ r) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem,
      Ideal.mem_span_singleton', LinearMap.mem_range]
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨b, rfl⟩ := hσ.2 s
      refine ⟨b, hτ.1 ?_⟩
      change α.app W (b • σ) = r • τ at hs
      exact (ht b).symm.trans hs
    · rintro ⟨b, rfl⟩
      exact ⟨b • σ, ht b⟩
  let e₁ := LinearMap.quotKerEquivOfSurjective L hL
  let e₂ : (Γ(Y, W) ⧸ LinearMap.ker L) ≃ₗ[K] (Γ(Y, W) ⧸ Ideal.span {t}) :=
    (Submodule.quotEquivOfEq _ _ hker).trans (Submodule.Quotient.restrictScalarsEquiv K _)
  exact e₁.symm.trans e₂

/-- The actual native pulled marking map supplies its own free pullback frames
and exact same-ideal cokernel comparison, over the ORIGINAL field action. -/
def pullbackMarkedCokerEquivQuotient {X Y : Scheme.{u}} {K : Type u} [Field K]
    (c : K →+* Γ(Y, ⊤)) (E : LocalEquations X)
    (M : X.Modules) [M.IsQuasicoherent] (ν : Y ⟶ X) {i : E.ι}
    {W : X.Opens} (hW : IsAffineOpen W) (hWi : W ≤ E.U i)
    {V : Y.Opens} (hV : IsAffineOpen V) (hVW : V ≤ ν ⁻¹ᵁ W)
    (σ : Γ(M, W)) (hσ : Function.Bijective (fun r : Γ(X, W) => r • σ)) :
    letI := (sectionsRingHom c (le_top : V ≤ ⊤)).toAlgebra
    sectionsCoker c (StableMarkedNativePullback.pullbackMarkedTwistMap E M ν) V ≃ₗ[K]
      (Γ(Y, V) ⧸ Ideal.span {ν.appLE W V hVW (res hWi (E.f i))}) :=
  sectionsCokerEquivQuotient c _ V (pullbackSectionLE ν M hVW σ)
    (pullbackSectionLE ν (E.toLineBundleData.twist M 1) hVW
      (E.toLineBundleData.ofLocal M 1 hWi σ))
    (Omega.RosenlichtComponent.bijective_smul_pullbackSectionLE ν M hW hV hVW σ hσ)
    (StableMarkedNativePullback.bijective_target_frame E M ν hW hWi hV hVW σ hσ)
    _ (StableMarkedNativePullback.pullbackMarkedTwistMap_frame E M ν hWi hVW σ)

end DeJongAlterations.StableModificationBridge.StableMarkedNativeCokernel
