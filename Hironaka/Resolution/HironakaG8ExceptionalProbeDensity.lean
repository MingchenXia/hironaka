import Hironaka.Resolution.HironakaG8ExceptionalProbeFamily
import Hironaka.Resolution.HironakaG8TraceLocalSection

/-! Local density transport through the literal pointed exceptional probes.
Blueprint: `hironaka-g8-exceptional-probe-density.tex`. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold
universe u
namespace Hironaka.HironakaG8ExceptionalProbeDensity
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupStrictSubmanifold
  ResolutionInvariantSpec HironakaActualMixedTestPowerNormalization
  HironakaG8ExceptionalProbeFamily HironakaG8TraceLocalSection HironakaActualProjectionTestRecord

variable {n k m : ℕ} {X : CMfd.{u} n}

/-- Local frequency on the initial double trace survives every actual
ordinary exceptional probe, with the original base map retained. -/
theorem probeFamily_lift_frequently (hm : 0 < m) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (s : ProbeState M m) (A : Set X)
    (hs : ∃ᶠ v in 𝓝 s.point, v ∈ s.F.get s.old ∧ v ∈ s.F.get s.newest ∧ baseMap s.H v ∈ A)
    (q : ℕ) :
    let p := probeFamily hm M hM s q
    ∃ᶠ v in 𝓝 p.point, v ∈ p.F.get p.old ∧ v ∈ p.F.get p.newest ∧ baseMap p.H v ∈ A := by
  induction q with
  | zero => exact hs
  | succ q ih =>
    let p := probeFamily hm M hM s q
    let p' := probeFamily hm M hM s (q+1)
    let C := p.F.get p.old ∩ p.F.get p.newest
    change ∃ᶠ v in 𝓝 p.point, v ∈ p.F.get p.old ∧ v ∈ p.F.get p.newest ∧ baseMap p.H v ∈ A at ih
    change ∃ᶠ w in 𝓝 p'.point, w ∈ p'.F.get p'.old ∧ w ∈ p'.F.get p'.newest ∧ baseMap p'.H w ∈ A
    obtain ⟨π,hπ,hπp,hOld,hNew,hBase⟩ := probeFamily_succ_trace_dictionary hm M hM s q
    change π p'.point = p.point at hπp
    change p'.F.get p'.old = geoStrictTransform π C (p.F.get p.old) at hOld
    change p'.F.get p'.newest = π ⁻¹' C at hNew
    change ∀ z : p'.Y, baseMap p'.H z = baseMap p.H (π z) at hBase
    have hD := record_isInvDomain M hM p.H p.test
    have hP : IsClosedSubmanifold m (p.F.get p.old) :=
      MonomialPart.isClosedSubmanifold_get hm hD.isWellFormed.isSNCDivisor p.old
    have hpOld : p'.point ∈ geoStrictTransform π C (p.F.get p.old) := hOld ▸ p'.point_old
    have hpC : π p'.point ∈ C := by rw [hπp]; exact ⟨p.point_old,p.point_newest⟩
    apply Filter.frequently_iff.mpr
    intro U hU
    have hLift := actual_trace_projects_near_base hπ hP (inter_subset_left : C ⊆ p.F.get p.old) hpOld hpC U hU
    rw [hπp] at hLift
    obtain ⟨v,⟨hvOld,hvNew,hvA⟩,hvLift⟩ := (ih.and_eventually hLift).exists
    obtain ⟨w,hwU,hπw,hwOld⟩ := hvLift ⟨hvOld,hvNew⟩
    refine ⟨w,hwU,?_,?_,?_⟩
    · rw [hOld]; exact hwOld
    · rw [hNew]; change π w ∈ C; rw [hπw]; exact ⟨hvOld,hvNew⟩
    · rw [hBase,hπw]; exact hvA
/-- Every source set frequently met on the selected original member is
frequently met on every actual double trace of the pointed probe. -/
theorem original_probe_lift_frequently (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (i : Fin M.E.length) (x : X) (hx : x ∈ M.E.get i) (A : Set X)
    (hA : ∃ᶠ y in 𝓝 x, y ∈ M.E.get i ∧ y ∈ A) (q : ℕ) :
    let s := initialProbeState M i x hx
    let p := probeFamily (Nat.succ_pos n) M hM s q
    ∃ᶠ v in 𝓝 p.point, v ∈ p.F.get p.old ∧ v ∈ p.F.get p.newest ∧ baseMap p.H v ∈ A := by
  let s := initialProbeState M i x hx
  have hzero : Tendsto (fun y : X => ((y,0) : projectionAmbient X)) (𝓝 x)
      (𝓝 ((x,0) : projectionAmbient X)) := (continuous_id.prodMk continuous_const).continuousAt
  have hbase : ∃ᶠ v : projectionAmbient X in 𝓝 ((x,0) : projectionAmbient X),
      v.1 ∈ M.E.get i ∧ v.2 = 0 ∧ v.1 ∈ A :=
    hzero.frequently (hA.mono fun y hy => ⟨hy.1,rfl,hy.2⟩)
  have hs : ∃ᶠ v in 𝓝 s.point, v ∈ s.F.get s.old ∧ v ∈ s.F.get s.newest ∧ baseMap s.H v ∈ A := by
    apply hbase.mono
    intro v hv
    refine ⟨?_,?_,?_⟩
    · change v ∈ (M.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++
        [horizontal X]).get ⟨i.val,by simp⟩
      have hlt : i.val < (M.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·)).length := by
        simpa only [List.length_map] using i.isLt
      rw [List.get_eq_getElem, List.getElem_append_left hlt, List.getElem_map]
      exact hv.1
    · change v ∈ (M.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++
        [horizontal X]).get ⟨M.E.length,by simp⟩
      simpa [List.get_eq_getElem,horizontal] using hv.2.1
    · change v.1 ∈ A
      exact hv.2.2
  exact probeFamily_lift_frequently (Nat.succ_pos n) M hM s A hs q
end
end Hironaka.HironakaG8ExceptionalProbeDensity
