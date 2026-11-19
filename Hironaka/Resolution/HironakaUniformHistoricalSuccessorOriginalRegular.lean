import Hironaka.Resolution.HironakaActualHistoricalNativeGivenTower
import Hironaka.Resolution.HironakaActualHSSingularOriginalPrefix

/-! Whole ORIGINAL regular-open protection from the SAME actual intrinsic
singular-centre history, without purity or a uniform regular dimension.
No actual history, boundary position or clock is replaced or erased.
Blueprint: `hironaka-uniform-historical-successor-original-regular.tex`. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaUniformHistoricalSuccessorOriginalRegular
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualHistoricalNativeGivenTower HironakaEmbeddedAnalytic HironakaStageCenters
  BlowupTowers BlowupTowerTransforms RestrictEmptyTower
variable {n : ℕ} {X : CMfd.{0} n}

-- Same old off-exceptional regularity induction, with EACH original point's
-- own actual regular dimension rather than an unjustified global pure d.
private theorem avoid_of_intrinsic_singular_history (W : Set X) (hW : IsClosed W)
    (O : Opens X) (hReg : ∀x∈W,x∈O → ∃d,RegularAtDim (n:=n) W x d) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),ActualHistoricalNativeTowerCentres W T → CentresAvoid O T
  | _,.refl,_ => trivial
  | _,.step T _C _pi _hpi,hStage => by
    have hAvoid:=avoid_of_intrinsic_singular_history W hW O hReg T hStage.1
    refine ⟨hAvoid,disjoint_left.mpr fun c hc hcO=>?_⟩
    have hSing:=mem_singularSet_iff.mp (hStage.2 hc)
    have hOriginalW:=HironakaAdmissibleCalculus.strictTransform_subset_preimage
      T.contMDiff_proj.continuous hW hSing.1
    obtain ⟨d,hd⟩:=hReg (T.proj c) hOriginalW hcO
    have hCurrentReg:=(regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus
      T.contMDiff_proj hW (EmbeddedFromResolution.notMem_exceptionalLocus_of_centresAvoid O T hAvoid c hcO) d).mpr hd
    exact hSing.2 d hCurrentReg

/-- The actual SAME intrinsic singular history DERIVES full original
regular-open protection, actual current support/compact geometry and the
literal regular stopping criterion, with no pure-dimension assumption. -/
theorem actual_singular_history_original_regular_protection {Y : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W) (T : BlowupTower X Y)
    (hStage : ActualHistoricalNativeTowerCentres W T) :
    let O : Opens X:=⟨(singularSet (n:=n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
    CentresAvoid O T ∧ IsIsomorphismOver n T.proj (singularSet (n:=n) W)ᶜ ∧
      IsProperMap T.proj ∧ IsComplexAnalyticSubset (n:=n) (strictTransform n T.proj W) ∧
      (IsCompact W → IsCompact (strictTransform n T.proj W)) ∧
      singularSet (n:=n) (strictTransform n T.proj W)⊆T.proj ⁻¹' singularSet (n:=n) W ∧
      (singularSet (n:=n) (strictTransform n T.proj W)=∅ ↔ IsClosedSubmanifold n (strictTransform n T.proj W)) := by
  let O : Opens X:=⟨(singularSet (n:=n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
  have hReg (x : X) (hx : x∈W) (hxO : x∈O) : ∃d,RegularAtDim (n:=n) W x d := by
    by_contra hNo
    exact hxO (mem_singularSet_iff.mpr ⟨hx,fun d hd=>hNo ⟨d,hd⟩⟩)
  have hAvoid:=avoid_of_intrinsic_singular_history W hW.isClosed O hReg T hStage
  have hIso:=HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    T.isBlowupSequence (EmbeddedFromResolution.image_exceptionalLocus_subset_compl O T hAvoid)
  have hCurrentA:=HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform T.isBlowupSequence hW
  refine ⟨hAvoid,?_,HironakaLocalPrincipalization.isProperMap_proj T,hCurrentA,
    (fun hK=>HironakaAdmissibleCalculus.isCompact_strictTransform T.isBlowupSequence hK),?_,?_⟩
  · have hO : (O : Set X) = (singularSet (n := n) W)ᶜ := rfl
    simpa only [compl_compl, hO] using hIso
  · intro y hy
    have hSing:=mem_singularSet_iff.mp hy
    have hOriginalW:=HironakaAdmissibleCalculus.strictTransform_subset_preimage
      T.contMDiff_proj.continuous hW.isClosed hSing.1
    by_contra hNotSing
    obtain ⟨d,hd⟩:=hReg (T.proj y) hOriginalW hNotSing
    exact hSing.2 d ((regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus
      T.contMDiff_proj hW.isClosed
      (EmbeddedFromResolution.notMem_exceptionalLocus_of_centresAvoid O T hAvoid y hNotSing) d).mpr hd)
  · constructor
    · intro hEmpty
      refine ⟨hCurrentA.isClosed,fun y hy=>?_⟩
      by_contra hNo
      have hs:=mem_singularSet_iff.mpr ⟨hy,fun d hd=>hNo ⟨d,hd⟩⟩
      rw [hEmpty] at hs
      exact hs
    · intro hSmooth
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hs:=mem_singularSet_iff.mp hy
      obtain ⟨d,hd⟩:=hSmooth.2 y hs.1
      exact hs.2 d hd

end
end Hironaka.HironakaUniformHistoricalSuccessorOriginalRegular
