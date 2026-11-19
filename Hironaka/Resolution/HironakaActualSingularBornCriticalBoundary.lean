import Hironaka.Resolution.HironakaActualStrictDivisorZeroExponent
import Hironaka.Resolution.HironakaGeneralSingularCentreCodimension
import Hironaka.Resolution.HironakaActualGeneralNCDriverBridge
import Hironaka.Blowup.BlowupCodimOne
import Hironaka.Resolution.HironakaStageCenters

/-! All literal born boundary positions of an actual intrinsic-singular
history lie in the differential exceptional locus of its SAME projection.
The resulting current strict-ideal exponent zero is derived from genuine
critical geometry, coherence and explicit current Cartier/nonzero data.
Blueprint: hironaka-actual-singular-born-critical-boundary-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualSingularBornCriticalBoundary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaGeneralSingularCentreCodimension BlowupFlatCoordinates BlowupCodimOne
  HironakaStageCenters HironakaActualGeneralNCDriverBridge
  HironakaActualStrictDivisorZeroExponent DivisorExponentAlong HironakaEmbeddedAnalytic

variable {n : ℕ}

/-- Actual intrinsic singular geometry forces EVERY newborn point to be
critical; no supplied codimension/critical-support certificate is used. -/
theorem preimage_singular_centre_subset_critical
    {X Y : CMfd.{u} n} {W C : Set X} (hW : IsComplexAnalyticSubset (n:=n) W)
    (hSing : C⊆singularSet (n:=n) W) {π : Y → X} (hπ : IsBlowupAlong n C π) :
    π ⁻¹' C ⊆ exceptionalLocus n π := by
  intro z hz
  obtain ⟨k,hReg⟩ := hπ.1.2 (π z) hz
  have hk := regular_intrinsic_singular_centre_add_two_le hW hSing hReg
  obtain ⟨_hkn,_hx,Φ,hΦsrc,_hΦ0,hFlat⟩ := hReg
  exact mem_exceptionalLocus_of_codim_ge_two hπ hΦsrc hFlat hk (mem_flatDomain_self Φ) hz

private theorem empty_initial_boundary_subset_critical
    {X : CMfd.{u} n} (Q : MarkedIdeal n X) (hQE : Q.E=[])
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      StageCentres (fun S C=>C⊆singularSet (n:=n) (strictTransform n S.proj W)) T →
      ∀ H∈(geoTransformAlong Q T).E,H⊆exceptionalLocus n T.proj
  | _,.refl,_hStage,H,hH => by
      change H∈Q.E at hH
      rw [hQE] at hH
      exact False.elim (List.not_mem_nil hH)
  | _,.step T C π hπ,hStage,H,hH => by
      have hPrev := empty_initial_boundary_subset_critical Q hQE W hW T hStage.1
      change H∈((geoTransformAlong Q T).E.map (geoStrictTransform π C)++[π ⁻¹' C]) at hH
      rw [BlowupTower.proj_step,exceptionalLocus_comp
        (T.contMDiff_proj.mdifferentiable (by simp)) (hπ.contMDiff.mdifferentiable (by simp))]
      rcases List.mem_append.mp hH with hOld | hNew
      · obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hOld
        intro z hz
        right
        have hClosed : IsClosed (π ⁻¹' exceptionalLocus n T.proj) :=
          (isOpen_compl_iff.mp (StrictTransformComposition.isOpen_compl_exceptionalLocus
            T.contMDiff_proj)).preimage hπ.contMDiff.continuous
        have hSubset : (π ⁻¹' A \ π ⁻¹' C) ⊆ π ⁻¹' exceptionalLocus n T.proj := by
          intro y hy
          exact hPrev A hA hy.1
        exact (closure_minimal hSubset hClosed) hz
      · have hNewEq : H=π ⁻¹' C := List.mem_singleton.mp hNew
        subst H
        intro z hz
        left
        exact preimage_singular_centre_subset_critical
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T)
          hStage.2 hπ hz

/-- EVERY literal born entry on the SAME original clock is critical for
the actual full projection, including original-empty-slot offsets. -/
theorem born_boundary_subset_critical {X Y : CMfd.{u} n}
    (Q : MarkedIdeal n X) (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (T : BlowupTower X Y)
    (hStage : StageCentres (fun S C=>C⊆singularSet (n:=n) (strictTransform n S.proj W)) T)
    (H : Set Y) (hH : H∈(geoTransformAlong Q T).E.drop Q.E.length) :
    H⊆exceptionalLocus n T.proj := by
  have hBorn := born_boundary_geoTransformAlong_withE Q [] T
  simp only [List.length_nil,List.drop_zero] at hBorn
  rw [← hBorn] at hH
  exact empty_initial_boundary_subset_critical {Q with E:=[]} rfl W hW T hStage H hH

/-- Actual recorded singular geometry derives the native born exponent
zero; current coherence follows from the SAME analytic strict transform. -/
theorem born_boundary_vanishing_exponent_zero {X Y : CMfd.{u} n}
    (Q : MarkedIdeal n X) (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (T : BlowupTower X Y)
    (hStage : StageCentres (fun S C=>C⊆singularSet (n:=n) (strictTransform n S.proj W)) T)
    (H : Set Y) (hBorn : H∈(geoTransformAlong Q T).E.drop Q.E.length)
    (hH : IsClosedSubmanifold n H) (hInv : (vanishingIdeal (n:=n) H).IsInvertible)
    (x : Y) (hNZ : IsNonzeroAlongAt univ (vanishingIdeal (n:=n) (strictTransform n T.proj W)) x) :
    divExpAlong n univ (vanishingIdeal (n:=n) (strictTransform n T.proj W)) H x=0 :=
  strictTransform_divExpAlong_eq_zero T.proj W
    (born_boundary_subset_critical Q W hW T hStage H hBorn)
    (CartanIrreducible.cartanCoherence _
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T)) hH hInv x hNZ

end
end Hironaka.HironakaActualSingularBornCriticalBoundary
