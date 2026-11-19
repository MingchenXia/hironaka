import Hironaka.Resolution.HironakaG8FiniteSingularHSPotential
import Hironaka.Resolution.HironakaActualProcessedAllMasksDrop
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8HereditaryDiscreteFiniteService
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves AnalyticDimensionBasics
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaHolomorphicJetChartInvariance
  HironakaG8FiniteIsolatedProfilePhase HironakaG8FiniteSingularHSPotential
  HironakaG8IntrinsicSingularBlockSchedule
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaActualHilbertSamuelWellFounded
  HironakaG11PresTowerState NormalCrossings

/-- Serve all descendants above a finite nonempty set in one phase, strictly
reducing their finite multiset of profiles. -/
theorem hereditary_discrete_finite_subset_phase {n : ℕ} (hn : 0<n) {X : CMfd.{0} n} (W F : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) [DiscreteTopology (singularSet (n := n) W)]
    (hPersist : ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      DiscreteTopology (singularSet (n := n) (strictTransform n T.proj W)))
    (hF : F.Finite)
    (hFS : F ⊆ singularSet (n := n) W) (hNe : F.Nonempty) :
    ∃ (Y : CMfd.{0} n) (Q : BlowupTower X Y)
      (hNew : (singularSet (n := n) (strictTransform n Q.proj W) ∩ Q.proj ⁻¹' F).Finite),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
      CentresOver F Q ∧
      Multiset.IsDershowitzMannaLT
        (finiteHSProfiles (strictTransform n Q.proj W)
          (singularSet (n := n) (strictTransform n Q.proj W) ∩ Q.proj ⁻¹' F) hNew)
        (finiteHSProfiles W F hF) := by
  let finiteF : Fintype F := hF.fintype
  let a : F → X := Subtype.val
  obtain ⟨D,Y,Q,hD,hTest,hStage,hFoot,hBound,hDrop⟩ :=
    finite_discrete_singular_global_phase hn W hW a (fun i => hFS i.property) Subtype.val_injective
  have hOver : CentresOver F Q := by
    have heq : range a = F := Subtype.range_coe
    simpa only [heq] using hFoot
  have hGeo := actual_singular_history_original_regular_protection W hW Q
    (intrinsic_stage_native_history W Q hStage)
  let discreteQ : DiscreteTopology (singularSet (n := n) (strictTransform n Q.proj W)) := hPersist Q hStage
  have hClosed : IsClosed (singularSet (n := n) (strictTransform n Q.proj W) ∩ Q.proj ⁻¹' F) :=
    (isClosed_singularSet hGeo.2.2.2.1.isClosed).inter (hF.isClosed.preimage Q.contMDiff_proj.continuous)
  have hCompact : IsCompact (singularSet (n := n) (strictTransform n Q.proj W) ∩ Q.proj ⁻¹' F) :=
    (hGeo.2.2.1.isCompact_preimage hF.isCompact).of_isClosed_subset hClosed inter_subset_right
  have hNew := hCompact.finite ((isDiscrete_iff_discreteTopology.mpr inferInstance).mono inter_subset_left)
  have hDropEach : ∀ y ∈ singularSet (n := n) (strictTransform n Q.proj W) ∩ Q.proj ⁻¹' F,
      (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (Q.proj y) ℓ) ∧
      ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y ℓ <
        hilbertSamuelAt (vanishingIdeal (n := n) W) (Q.proj y) ℓ := by
    intro y hy
    let i : F := ⟨Q.proj y,hy.2⟩
    let y' : openPreimage Q (D i) := ⟨y,hD i⟩
    simpa [a,i,y'] using hDrop i y'
  exact ⟨Y,Q,hNew,hStage,hOver,
    finiteHSProfiles_descent W (strictTransform n Q.proj W) F _ hF hNew hNe Q.proj
      (fun _ hy => hy.2) hDropEach⟩
/-- Finite singular-point footprint service: every actual singular descendant
above the chosen finite set disappears, with centres supported over that set. -/
theorem hereditary_discrete_finite_subset_service_core {n : ℕ} (hn : 0<n) {X : CMfd.{0} n} (W F : Set X)
    (P : ∀ (A : CMfd.{0} n), Set A → Prop)
    (hDisc : ∀ (A : CMfd.{0} n) (V : Set A), IsComplexAnalyticSubset (n := n) V → P A V →
      DiscreteTopology (singularSet (n := n) V))
    (hNext : ∀ {A B : CMfd.{0} n} (V : Set A), IsComplexAnalyticSubset (n := n) V → P A V →
      ∀ (T : BlowupTower A B),
        StageCentres (fun Q C => C ⊆ singularSet (n := n) (strictTransform n Q.proj V)) T →
        P B (strictTransform n T.proj V))
    (hW : IsComplexAnalyticSubset (n := n) W) (hP : P X W) (hF : F.Finite)
    (hFS : F ⊆ singularSet (n := n) W) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T ∧
      CentresOver F T ∧
      singularSet (n := n) (strictTransform n T.proj W) ∩ T.proj ⁻¹' F = ∅ := by
  let wfHS : WellFoundedLT (ActualHilbertSamuelProfile n) := actual_hilbertSamuel_wellFounded n
  have hwf : WellFounded (Multiset.IsDershowitzMannaLT : Multiset (ActualHilbertSamuelProfile n) → Multiset (ActualHilbertSamuelProfile n) → Prop) :=
    Multiset.wellFounded_isDershowitzMannaLT
  have hall : ∀ (s : Multiset (ActualHilbertSamuelProfile n)) (A : CMfd.{0} n) (V G : Set A)
      (hV : IsComplexAnalyticSubset (n := n) V) (hPV : P A V) (hG : G.Finite)
      (hGS : G ⊆ singularSet (n := n) V), finiteHSProfiles V G hG = s →
      ∃ (B : CMfd.{0} n) (T : BlowupTower A B),
        StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj V)) T ∧
        CentresOver G T ∧
        singularSet (n := n) (strictTransform n T.proj V) ∩ T.proj ⁻¹' G = ∅ := by
    intro s
    induction s using hwf.induction with
    | h s ih =>
      intro A V G hV hPV hG hGS hs
      by_cases hNe : G.Nonempty
      · let discreteV : DiscreteTopology (singularSet (n := n) V) := hDisc A V hV hPV
        have hPersist : ∀ {B : CMfd.{0} n} (Q : BlowupTower A B),
            StageCentres (fun R C => C ⊆ singularSet (n := n) (strictTransform n R.proj V)) Q →
            DiscreteTopology (singularSet (n := n) (strictTransform n Q.proj V)) := by
          intro B Q hQ
          have hGeo := actual_singular_history_original_regular_protection V hV Q
            (intrinsic_stage_native_history V Q hQ)
          exact hDisc B _ hGeo.2.2.2.1 (hNext V hV hPV Q hQ)
        obtain ⟨B,Q,hNew,hStage,hOver,hDrop⟩ := hereditary_discrete_finite_subset_phase hn V G hV hPersist hG hGS hNe
        let G' := singularSet (n := n) (strictTransform n Q.proj V) ∩ Q.proj ⁻¹' G
        have hGeo := actual_singular_history_original_regular_protection V hV Q
          (intrinsic_stage_native_history V Q hStage)
        have hsmaller : Multiset.IsDershowitzMannaLT
            (finiteHSProfiles (strictTransform n Q.proj V) G' hNew) s := by
          simpa [G', ← hs] using hDrop
        obtain ⟨D,R,hR,hROver,hEmpty⟩ := ih _ hsmaller B (strictTransform n Q.proj V) G'
          hGeo.2.2.2.1 (hNext V hV hPV Q hStage) hNew inter_subset_left rfl
        refine ⟨D,Q.append R,HironakaG8IntrinsicSingularBlockSchedule.intrinsic_stage_append V Q R hStage hR,?_,?_⟩
        · apply (centresOver_append_iff G Q R).mpr
          exact ⟨hOver,HironakaActualProcessedAllMasksDrop.centresOver_mono_local
            (show G' ⊆ Q.proj ⁻¹' G from inter_subset_right) R hROver⟩
        · have hStrict := StrictTransformComposition.strictTransform_comp Q.contMDiff_proj R.contMDiff_proj V
          rw [← BlowupTower.proj_append] at hStrict
          apply eq_empty_iff_forall_notMem.mpr
          intro z hz
          have hzSing : z ∈ singularSet (n := n) (strictTransform n R.proj (strictTransform n Q.proj V)) := by
            simpa only [hStrict] using hz.1
          have hzG : Q.proj (R.proj z) ∈ G := by
            simpa only [BlowupTower.proj_append,Set.mem_preimage,Function.comp_apply] using hz.2
          have hParent := (actual_singular_history_original_regular_protection
            (strictTransform n Q.proj V) hGeo.2.2.2.1 R
            (intrinsic_stage_native_history (strictTransform n Q.proj V) R hR)).2.2.2.2.2.1
          have : z ∈ singularSet (n := n) (strictTransform n R.proj (strictTransform n Q.proj V)) ∩ R.proj ⁻¹' G' :=
            ⟨hzSing,⟨hParent hzSing,hzG⟩⟩
          rw [hEmpty] at this
          exact this
      · refine ⟨A,.refl,trivial,trivial,?_⟩
        have hEmpty : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hNe
        simp [hEmpty]
  obtain ⟨Y,T,hStage,hOver,hEmpty⟩ := hall (finiteHSProfiles W F hF) X W F hW hP hF hFS rfl
  exact ⟨Y,T,hStage,hOver,hEmpty⟩

end
end Hironaka.HironakaG8HereditaryDiscreteFiniteService
