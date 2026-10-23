/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableMarkedDualizingBundle
import DeJongAlterations.StableModification.Omega.RosenlichtComponentPullback
import DeJongAlterations.Geometry.LineBundleNativePullback

/-! The actual native pullback marking morphism has the SAME original equation
under the original whole coefficient map. Blueprint: `stable-marked-native-pullback.tex`. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace DeJongAlterations.StableModificationBridge.StableMarkedNativePullback
open StableModification StableModification.Projectivity Cohomology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- Pull back the WHOLE actual original marking map by the native module functor. -/
def pullbackMarkedTwistMap {X Y : Scheme.{u}} (E : LocalEquations X) (M : X.Modules)
    (ν : Y ⟶ X) :
    (Scheme.Modules.pullback ν).obj M ⟶
      (Scheme.Modules.pullback ν).obj (E.toLineBundleData.twist M 1) :=
  (Scheme.Modules.pullback ν).map (StableMarkedDualizingBundle.markedTwistMap E M)

/-- The actual whole map in native source and target frames is multiplication
by the SAME original Cartier equation through the actual original appLE map. -/
theorem pullbackMarkedTwistMap_frame {X Y : Scheme.{u}} (E : LocalEquations X)
    (M : X.Modules) (ν : Y ⟶ X) {i : E.ι} {W : X.Opens}
    (hWi : W ≤ E.U i) {V : Y.Opens} (hVW : V ≤ ν ⁻¹ᵁ W)
    (σ : Γ(M, W)) (r : Γ(Y, V)) :
    (pullbackMarkedTwistMap E M ν).app V (r • pullbackSectionLE ν M hVW σ) =
      (r * ν.appLE W V hVW (res hWi (E.f i))) •
        pullbackSectionLE ν (E.toLineBundleData.twist M 1) hVW
          (E.toLineBundleData.ofLocal M 1 hWi σ) := by
  have hm : (StableMarkedDualizingBundle.markedTwistMap E M).app W σ =
      res hWi (E.f i) • E.toLineBundleData.ofLocal M 1 hWi σ := by
    apply (E.toLineBundleData.localEquiv M 1 hWi).injective
    change E.toLineBundleData.toLocal M 1 hWi _ = E.toLineBundleData.toLocal M 1 hWi _
    rw [StableMarkedDualizingBundle.markedTwistMap_toLocal,
      E.toLineBundleData.toLocal_smul, E.toLineBundleData.toLocal_ofLocal]
  rw [Scheme.Modules.Hom.app_smul]
  change r • ((Scheme.Modules.pullback ν).map
    (StableMarkedDualizingBundle.markedTwistMap E M)).app V _ = _
  rw [← pullbackSectionLE_naturality, hm, pullbackSectionLE_smul, mul_smul]

/-- The native pullback target frame is genuinely free: no frame certificate
on the target or native pullback is an input. -/
theorem bijective_target_frame {X Y : Scheme.{u}} (E : LocalEquations X)
    (M : X.Modules) [M.IsQuasicoherent] (ν : Y ⟶ X) {i : E.ι}
    {W : X.Opens} (hW : IsAffineOpen W) (hWi : W ≤ E.U i)
    {V : Y.Opens} (hV : IsAffineOpen V) (hVW : V ≤ ν ⁻¹ᵁ W)
    (σ : Γ(M, W)) (hσ : Function.Bijective (fun c : Γ(X, W) => c • σ)) :
    Function.Bijective (fun r : Γ(Y, V) => r •
      pullbackSectionLE ν (E.toLineBundleData.twist M 1) hVW
        (E.toLineBundleData.ofLocal M 1 hWi σ)) := by
  apply Omega.RosenlichtComponent.bijective_smul_pullbackSectionLE ν
    (E.toLineBundleData.twist M 1) hW hV hVW
  have he (r : Γ(X, W)) : E.toLineBundleData.toLocal M 1 hWi
      (r • E.toLineBundleData.ofLocal M 1 hWi σ) = r • σ := by
    rw [E.toLineBundleData.toLocal_smul, E.toLineBundleData.toLocal_ofLocal]
  constructor
  · intro r s hrs
    apply hσ.1
    exact (he r).symm.trans ((congrArg (E.toLineBundleData.toLocal M 1 hWi) hrs).trans (he s))
  · intro z
    obtain ⟨r, hr⟩ := hσ.2 (E.toLineBundleData.toLocal M 1 hWi z)
    exact ⟨r, (E.toLineBundleData.localEquiv M 1 hWi).injective ((he r).trans hr)⟩

end DeJongAlterations.StableModificationBridge.StableMarkedNativePullback
