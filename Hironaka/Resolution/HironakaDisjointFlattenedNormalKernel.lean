/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionGermIdealColon
import Hironaka.Blowup.BlowupFlatCoordinates

/-! The original vanishing ideal inclusion and the SAME supplied actual
flattening internally give the entire normal-plane trace kernel inclusion.
No coherence, radicalization or target-kernel certificate is assumed.
Blueprint: hironaka-disjoint-flattened-normal-kernel-extension.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaDisjointFlattenedNormalKernel
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm BlowupFlatCoordinates
 HironakaSmoothSubmersionGermIdealColon HironakaRelativeNormalIdeal
 HironakaHolomorphicJetMonomialSpan
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y]
 [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

private theorem adapted_flatCoord (y : Y)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hsrc : Θ.source⊆(chartAt (ComplexModel n) y).target)
    (h0 : Θ.toFun (chartAt (ComplexModel n) y y)=0) (i : Fin n) :
    adaptedGerm y Θ h0 (flatCoord Θ i)
      (holomorphicAt_flatCoord Θ i (mem_flatDomain_self Θ))=coordinateGerm i := by
  unfold adaptedGerm coordinateGerm
  apply HolGerm.mk_eq_mk_iff.mpr
  have htar : (0 : ComplexModel n)∈Θ.target := by
    simpa only [h0] using Θ.mapsTo_toFun Θ.center_mem_source
  filter_upwards [Θ.isOpen_target.mem_nhds htar] with v hv
  exact congrArg (fun z : ComplexModel n=>z i) (flatInverse_mem Θ hv hsrc).2

theorem ker_planeTrace_le_adaptedIdeal {d t : ℕ} {Z : Type u}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel (d+t)) Z] [IsComplexManifold (d+t) Z]
    (S : Set Z) (y : Z)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
    (hsrc : Θ.source⊆(chartAt (ComplexModel (d+t)) y).target)
    (h0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y)=0)
    (hflat : ∀z : Z,z∈(chartAt (ComplexModel (d+t)) y).source →
      chartAt (ComplexModel (d+t)) y z∈Θ.source →
      (z∈S ↔ Θ.toFun (chartAt (ComplexModel (d+t)) y z)∈complexCoordinatePlane (d+t) d))
    (A : GermIdeal (d+t) Z) (hInc : (vanishingIdeal (n:=d+t) S).Le A) :
    RingHom.ker (planeTrace d t).toRingHom≤adaptedIdeal A y Θ h0 := by
  rw [←normalIdeal_eq_ker_planeTrace]
  apply Ideal.span_le.mpr
  rintro g ⟨j,rfl⟩
  change coordinateGerm (j.natAdd d)∈adaptedIdeal A y Θ h0
  have hNormal : (vanishingIdeal (n:=d+t) S).mem y (flatCoord Θ (j.natAdd d)) :=
    flatCoord_mem_vanishingIdeal Θ (fun {_} hz hΘz=>hflat _ hz hΘz)
      (by change d≤d+j.val;omega) (mem_flatDomain_self Θ)
  have hA := hInc y _ hNormal
  rw [←adapted_flatCoord y Θ hsrc h0 (j.natAdd d)]
  exact Ideal.subset_span ⟨_,holomorphicAt_flatCoord Θ _ (mem_flatDomain_self Θ),hA,rfl⟩

end
end Hironaka.HironakaDisjointFlattenedNormalKernel
