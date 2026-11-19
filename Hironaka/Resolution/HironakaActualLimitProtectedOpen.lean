import Hironaka.Resolution.HironakaActualLocallyFiniteHistoryLimit
import Hironaka.Resolution.HironakaActualLocallyFiniteHistoryFactors

set_option autoImplicit false

/-! Actual centre footprint and protected open of a genuine locally finite limit.
Blueprint: `hironaka-actual-limit-protected-open.tex`. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaActualLimitProtectedOpen

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq RestrictEmptyTower HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryComparison HironakaActualLocallyFiniteHistoryOverlap
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteHistoryFactors

variable {n : ℕ} {X : CMfd.{u} n}

attribute [local instance] limitChartedSpace

/-- The literal union of all ACTUAL original-base centre images. -/
def actualCentreFootprint (s : GrowingSeq X) : Set X := ⋃ i, centreImage s i

/-- Real locally finite closed centre images give a closed original footprint. -/
theorem isClosed_actualCentreFootprint (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) : IsClosed (actualCentreFootprint s) :=
  hLF.isClosed_iUnion (fun i => isClosed_centreImage s i)

/-- The recorded zero and successor tower equalities internally locate EVERY
centre of EVERY actual prefix over the same original footprint. -/
theorem centresOver_actualCentreFootprint_stage (s : GrowingSeq X) (k : ℕ) :
    CentresOver (actualCentreFootprint s) (s.stage k).2 := by
  induction k with
  | zero =>
    change (fun q : Σ Y : CMfd.{u} n, BlowupTower X Y =>
      CentresOver (actualCentreFootprint s) q.2) (s.stage 0)
    rw [s.zero]
    trivial
  | succ k ih =>
    obtain ⟨π, hπ, hstep⟩ := exists_step_map s k
    rw [hstep]
    refine ⟨ih, fun y hy => ?_⟩
    exact mem_iUnion.mpr ⟨k, y, hy, rfl⟩

private theorem finite_exceptional_subset_preimage (F : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresOver F T →
      exceptionalLocus n T.proj ⊆ T.proj ⁻¹' F
  | _, .refl, _ => by simp only [BlowupTower.proj_refl, exceptionalLocus_id, empty_subset]
  | _, .step T C π hπ, hOver => by
    rw [BlowupTower.proj_step, exceptionalLocus_comp
      (T.contMDiff_proj.mdifferentiable (by simp)) (hπ.contMDiff.mdifferentiable (by simp))]
    intro z hz
    rcases hz with hzπ | hzT
    · exact hOver.2 (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ hzπ)
    · exact finite_exceptional_subset_preimage F T hOver.1 hzT

private theorem prefix_isomorphism_off_footprint (s : GrowingSeq X) (k : ℕ) :
    IsIsomorphismOver n (s.stage k).2.proj (actualCentreFootprint s)ᶜ := by
  apply HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    (s.stage k).2.isBlowupSequence
  rintro _ ⟨z, hz, rfl⟩
  exact finite_exceptional_subset_preimage _ _ (centresOver_actualCentreFootprint_stage s k) hz

/-- The independently constructed true locally finite limit preserves the
ENTIRE complement of its actual centre footprint. No prefix isomorphism or
future-selector certificate is supplied. -/
theorem gluedProjection_isIsomorphismOver_compl_actualCentreFootprint
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsIsomorphismOver n (gluedProjection s hLF : limitManifold s hLF → X)
      (actualCentreFootprint s)ᶜ := by
  refine ⟨⟨fun _ hx => hx, ?_, ?_⟩, ?_⟩
  · intro q hq r hr hqr
    let x := gluedProjection s hLF q
    have hqRange : q ∈ range (actualHistoryLocalInclusion s hLF x) := by
      rw [localInclusion_range]
      exact point_mem_stableWindow s hLF x
    have hrRange : r ∈ range (actualHistoryLocalInclusion s hLF x) := by
      rw [localInclusion_range]
      change gluedProjection s hLF r ∈ stableWindow s hLF x
      rw [← hqr]
      exact point_mem_stableWindow s hLF x
    obtain ⟨z, hzq⟩ := hqRange
    obtain ⟨w, hwr⟩ := hrRange
    have hz : (s.stage (stableIndex s hLF x)).2.proj z.val ∈ (actualCentreFootprint s)ᶜ := by
      change localProjection s hLF x z ∈ (actualCentreFootprint s)ᶜ
      rw [← gluedProjection_local, hzq]
      exact hq
    have hw : (s.stage (stableIndex s hLF x)).2.proj w.val ∈ (actualCentreFootprint s)ᶜ := by
      change localProjection s hLF x w ∈ (actualCentreFootprint s)ᶜ
      rw [← gluedProjection_local, hwr]
      exact hr
    have hp : (s.stage (stableIndex s hLF x)).2.proj z.val =
        (s.stage (stableIndex s hLF x)).2.proj w.val := by
      change localProjection s hLF x z = localProjection s hLF x w
      rw [← gluedProjection_local, ← gluedProjection_local, hzq, hwr]
      exact hqr
    exact hzq.symm.trans ((congrArg (actualHistoryLocalInclusion s hLF x)
      (Subtype.ext ((prefix_isomorphism_off_footprint s _).1.2.1 hz hw hp))).trans hwr)
  · intro x hx
    obtain ⟨z, hz⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective
      (s.stage (stableIndex s hLF x)).2.isBlowupSequence x
    let q : localEndpoint s hLF x := ⟨z, by
      change (s.stage (stableIndex s hLF x)).2.proj z ∈ stableWindow s hLF x
      rw [hz]
      exact point_mem_stableWindow s hLF x⟩
    have hproj : gluedProjection s hLF (actualHistoryLocalInclusion s hLF x q) = x :=
      (gluedProjection_local s hLF x q).trans hz
    refine ⟨actualHistoryLocalInclusion s hLF x q, ?_, hproj⟩
    change gluedProjection s hLF (actualHistoryLocalInclusion s hLF x q) ∈ (actualCentreFootprint s)ᶜ
    rw [hproj]
    exact hx
  · apply disjoint_left.mpr
    intro q hq hqExc
    obtain ⟨x, z, rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF q
    let T := (s.stage (stableIndex s hLF x)).2
    let U := stableWindow s hLF x
    have hz : T.proj z.val ∈ (actualCentreFootprint s)ᶜ := by
      change localProjection s hLF x z ∈ (actualCentreFootprint s)ᶜ
      rw [← gluedProjection_local]
      exact hq
    have hzNot : z.val ∉ exceptionalLocus n T.proj :=
      fun h => disjoint_left.mp (prefix_isomorphism_off_footprint s _).2 hz h
    have hValNot : z ∉ exceptionalLocus n
        (Subtype.val : openPreimage T U → (s.stage (stableIndex s hLF x)).1) := by
      intro h
      apply h
      rw [BlowupIsomorphismOff.mfderiv_subtype_val]
      exact Function.bijective_id
    have hCompositeNot : z ∉ exceptionalLocus n (T.proj ∘
        (Subtype.val : openPreimage T U → (s.stage (stableIndex s hLF x)).1)) := by
      rw [exceptionalLocus_comp (T.contMDiff_proj.mdifferentiable (by simp))
        ((contMDiff_subtype_val (n := ∞) : ContMDiff 𝓘(ℂ, ComplexModel n)
          𝓘(ℂ, ComplexModel n) ∞
            (Subtype.val : openPreimage T U → (s.stage (stableIndex s hLF x)).1)).mdifferentiable (by simp))]
      exact fun h => h.elim hValNot hzNot
    have hSquare : (gluedProjection s hLF : limitManifold s hLF → X) ∘
        actualHistoryLocalInclusion s hLF x = T.proj ∘
          (Subtype.val : openPreimage T U → (s.stage (stableIndex s hLF x)).1) :=
      funext (gluedProjection_local s hLF x)
    have hBad : z ∈ exceptionalLocus n ((gluedProjection s hLF : limitManifold s hLF → X) ∘
        actualHistoryLocalInclusion s hLF x) := by
      rw [exceptionalLocus_comp ((gluedProjection_contMDiff s hLF).mdifferentiable (by simp))
        ((localInclusion_contMDiff s hLF x).mdifferentiable (by simp))]
      exact Or.inr hqExc
    rw [hSquare] at hBad
    exact hCompositeNot hBad

/-- The NATIVE actual critical set of the actual projection has no image
outside the actual centre footprint. -/
theorem gluedProjection_exceptionalImage_subset_actualCentreFootprint
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    (gluedProjection s hLF) '' exceptionalLocus n
      (gluedProjection s hLF : limitManifold s hLF → X) ⊆ actualCentreFootprint s := by
  rintro _ ⟨z, hz, rfl⟩
  by_contra hnot
  exact disjoint_left.mp (gluedProjection_isIsomorphismOver_compl_actualCentreFootprint s hLF).2 hnot hz

/-- Actual support of the REAL centre images preserves the entire original
complement at the genuine locally finite endpoint. -/
theorem gluedProjection_isIsomorphismOver_compl_of_centreImages_subset
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (B : Set X)
    (hB : ∀ i, centreImage s i ⊆ B) :
    IsIsomorphismOver n (gluedProjection s hLF : limitManifold s hLF → X) Bᶜ := by
  have hFoot : actualCentreFootprint s ⊆ B := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hB i hi
  have hIso := gluedProjection_isIsomorphismOver_compl_actualCentreFootprint s hLF
  have hsub : Bᶜ ⊆ (actualCentreFootprint s)ᶜ := compl_subset_compl.mpr hFoot
  refine ⟨⟨fun _ hx => hx, fun _ hx _ hy hxy => hIso.1.2.1 (hsub hx) (hsub hy) hxy, ?_⟩,
    disjoint_left.mpr fun _ hx hexc => disjoint_left.mp hIso.2 (hsub hx) hexc⟩
  intro x hx
  obtain ⟨z, _hz, hzx⟩ := hIso.1.2.2 (hsub hx)
  refine ⟨z, ?_, hzx⟩
  change gluedProjection s hLF z ∈ Bᶜ
  rw [hzx]
  exact hx

end

end Hironaka.HironakaActualLimitProtectedOpen
