import Hironaka.Resolution.HironakaActualMixedTestPowerNormalization
import Hironaka.Invariant.BoundaryCount
import Hironaka.Invariant.BoundaryCountAlong
import Hironaka.Blowup.NormalCrossingsComparison
import Hironaka.Resolution.HironakaActualCartierTraceSuccessor

/-! The literal repeated ordinary-exceptional probe geometry. Blueprint:
`hironaka-g8-exceptional-probe-family.tex`. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold
universe u
namespace Hironaka.HironakaG8ExceptionalProbeFamily
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupStrictSubmanifold MarkedIdeals
  MarkedIdeals.MarkedIdeal ResolutionInvariantSpec BoundaryCount NormalCrossings
  HironakaActualMixedTestPowerNormalization HironakaActualProjectionTestRecord
  HironakaActualCartierTraceSuccessor BoundaryCountAlong NormalCrossingsComparison
  SimultaneousNormalCrossings DivisorExponentAlong

variable {n k m : ℕ} {X : CMfd.{u} n}

/-- A literal mixed prefix and the two different members used for the next
ordinary exceptional blowup. -/
structure ProbeState (M : MarkedIdeal n X) (m : ℕ) where
  Y : CMfd.{u} m
  F : List (Set Y)
  H : History X M.E Y F
  test : IsTest M H
  universal : ∀ B : MarkedIdeal n X, IsTest (⟨B.N,M.E,B.ideal,B.d⟩ : MarkedIdeal n X) H
  old : Fin F.length
  newest : Fin F.length
  distinct : old ≠ newest
  point : Y
  point_old : point ∈ F.get old
  point_newest : point ∈ F.get newest

private theorem centre_smooth (hm : 0 < m) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (s : ProbeState M m) :
    IsClosedSubmanifold m (s.F.get s.old ∩ s.F.get s.newest) := by
  have hD := record_isInvDomain M hM s.H s.test
  have h := isClosedSubmanifold_memberInter hm hD.isWellFormed.isSNCDivisor {s.old,s.newest}
  change IsClosedSubmanifold m (memberInter s.F {s.old,s.newest}) at h
  have heq : memberInter s.F {s.old,s.newest} = s.F.get s.old ∩ s.F.get s.newest := by
    ext x
    simp [memberInter]
  rw [heq] at h
  exact h

private structure ProbeStep {M : MarkedIdeal n X} (s : ProbeState M m) where
  Z : CMfd.{u} m
  π : Z → s.Y
  hπ : IsBlowupAlong m (s.F.get s.old ∩ s.F.get s.newest) π
  point : Z
  point_old : point ∈ geoStrictTransform π (s.F.get s.old ∩ s.F.get s.newest) (s.F.get s.old)
  point_newest : π point ∈ s.F.get s.old ∩ s.F.get s.newest
  point_map : π point = s.point

private def probeStep (hm : 0 < m) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (s : ProbeState M m) : ProbeStep s := Classical.choice (by
  have hD := record_isInvDomain M hM s.H s.test
  have hE : IsSNCDivisor m s.F := hD.isWellFormed.isSNCDivisor
  have hOld : IsClosedSubmanifold m (s.F.get s.old) :=
    MonomialPart.isClosedSubmanifold_get hm hE s.old
  have hSingle : IsSNCDivisor m [s.F.get s.newest] :=
    isSNCDivisor_of_sublist hE (List.singleton_sublist.mpr (List.get_mem _ _))
  have hT : IsTransverse m (s.F.get s.old) [s.F.get s.newest] := by
    have hh := isTransverse_inter_memberInter_of_forall hE (isTransverse_univ_of_isSNCDivisor hE)
      {s.old} (E' := [s.F.get s.newest]) (by
        intro H hH
        rw [List.mem_singleton] at hH
        subst H
        exact ⟨s.newest, by simpa using s.distinct.symm, rfl⟩)
    simpa only [memberInter_singleton, univ_inter] using hh
  obtain ⟨Z,π,hπ,z',_,_,_,_,hzOld,hmap,hzNew,_,_,_,_⟩ :=
    exists_pure_cartier_trace_successor hm (s.F.get s.old) [s.F.get s.newest]
      hOld hSingle hT ⟨0,by simp⟩ s.point ⟨s.point_old,s.point_newest⟩
  exact ⟨⟨Z,π,hπ,z',hzOld,hzNew,hmap⟩⟩)

/-- The next genuine blowup retains a point above the previous one at the
intersection of the strict old member and the newly born divisor. -/
private def nextState (hm : 0 < m) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (s : ProbeState M m) : ProbeState M m := by
  let d := probeStep hm M hM s
  let C := s.F.get s.old ∩ s.F.get s.newest
  let F' : List (Set d.Z) := s.F.map (geoStrictTransform d.π C) ++ [d.π ⁻¹' C]
  have hold : s.old.val < F'.length := by simp [F']
  have hnew : s.F.length < F'.length := by simp [F']
  refine ⟨d.Z,F',.exceptional s.H s.old s.newest s.distinct d.π d.hπ,s.test,
    s.universal,⟨s.old.val,hold⟩,⟨s.F.length,hnew⟩,?_,d.point,?_,?_⟩
  · intro heq
    exact (Nat.ne_of_lt s.old.isLt) (congrArg Fin.val heq)
  · simpa [F',C,List.get_eq_getElem,s.old.isLt] using d.point_old
  · simpa [F',C,List.get_eq_getElem] using d.point_newest

/-- The literal product test starts with the source member and the new
horizontal member as its distinct pair of boundary slots. -/
def initialProbeState (M : MarkedIdeal n X) (i : Fin M.E.length) (x : X)
    (hx : x ∈ M.E.get i) : ProbeState M (n+1) := by
  let F : List (Set (projectionAmbient X)) :=
    M.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]
  have hi : i.val < F.length := by simp [F]
  have hj : M.E.length < F.length := by simp [F]
  refine ⟨projectionAmbient X,F,.projection .refl,True.intro,fun _ => True.intro,
    ⟨i.val,hi⟩,⟨M.E.length,hj⟩,?_,(x,0),?_,?_⟩
  · intro h
    exact (Nat.ne_of_lt i.isLt) (congrArg Fin.val h)
  · simpa [F,List.get_eq_getElem,i.isLt] using hx
  · simp [F,List.get_eq_getElem,horizontal]

/-- Repeated legal exceptional tests preserve the selected original slot,
and at each step choose the member born at the previous step. -/
def probeFamily (hm : 0 < m) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (s : ProbeState M m) : ℕ → ProbeState M m :=
  Nat.rec s (fun _ a => nextState hm M hM a)

/-- The retained index is the very same original boundary slot at every step. -/
theorem probeFamily_old_index (hm : 0 < m) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (s : ProbeState M m) (q : ℕ) : (probeFamily hm M hM s q).old.val = s.old.val := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change (nextState hm M hM (probeFamily hm M hM s q)).old.val = s.old.val
    exact ih

/-- Each new distinguished member is literally the newly appended born slot. -/
theorem probeFamily_newest_index (hm : 0 < m) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (s : ProbeState M m) (q : ℕ) :
    (probeFamily hm M hM s (q+1)).newest.val = (probeFamily hm M hM s q).F.length := by
  rfl

/-- All selected points remain above the same original point. -/
theorem probeFamily_base_point (hm : 0 < m) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (s : ProbeState M m) (q : ℕ) :
    baseMap (probeFamily hm M hM s q).H (probeFamily hm M hM s q).point = baseMap s.H s.point := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change baseMap (probeFamily hm M hM s q).H
      ((probeStep hm M hM (probeFamily hm M hM s q)).π
        (probeStep hm M hM (probeFamily hm M hM s q)).point) = baseMap s.H s.point
    rw [(probeStep hm M hM (probeFamily hm M hM s q)).point_map]
    exact ih

/-- The chain has exactly one new exceptional action per step. -/
theorem probeFamily_history_length (hm : 0 < m) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (s : ProbeState M m) (q : ℕ) :
    length (probeFamily hm M hM s q).H = length s.H + q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change length (probeFamily hm M hM s q).H + 1 = length s.H + (q+1)
    omega

/-- Starting at a chosen point of the original boundary, all retained points
project to that exact original point. -/
theorem original_probe_base_point (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (i : Fin M.E.length) (x : X) (hx : x ∈ M.E.get i) (q : ℕ) :
    let s := initialProbeState M i x hx
    baseMap (probeFamily (Nat.succ_pos n) M hM s q).H
      (probeFamily (Nat.succ_pos n) M hM s q).point = x := by
  simpa [initialProbeState,baseMap] using probeFamily_base_point (Nat.succ_pos n) M hM
    (initialProbeState M i x hx) q

/-- Ordinary exceptional probes preserve the full ambient carrier. -/
theorem probeFamily_carrier_univ (hm : 0 < m) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (s : ProbeState M m) (hN : (record M s.H).N = univ) (q : ℕ) :
    (record M (probeFamily hm M hM s q).H).N = univ := by
  induction q with
  | zero => exact hN
  | succ q ih =>
    change geoStrictTransform (probeStep hm M hM (probeFamily hm M hM s q)).π
      ((probeFamily hm M hM s q).F.get (probeFamily hm M hM s q).old ∩
        (probeFamily hm M hM s q).F.get (probeFamily hm M hM s q).newest)
      (record M (probeFamily hm M hM s q).H).N = univ
    rw [ih, geoStrictTransform_univ (probeStep hm M hM (probeFamily hm M hM s q)).hπ]

/-- The actual original full-carrier records retain that carrier at every probe. -/
theorem original_probe_carrier_univ (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hN : M.N = univ) (i : Fin M.E.length) (x : X) (hx : x ∈ M.E.get i) (q : ℕ) :
    let s := initialProbeState M i x hx
    (record M (probeFamily (Nat.succ_pos n) M hM s q).H).N = univ := by
  apply probeFamily_carrier_univ
  change (Prod.fst : projectionAmbient X → X) ⁻¹' M.N = univ
  rw [hN, preimage_univ]

/-- The literal successor blowup, its full ordered boundary, its selected
point, and the whole ordinary pullback for every queried record. -/
theorem probeFamily_succ_dictionary (hm : 0 < m) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (s : ProbeState M m) (q : ℕ) :
    let p := probeFamily hm M hM s q
    let p' := probeFamily hm M hM s (q+1)
    let C := p.F.get p.old ∩ p.F.get p.newest
    ∃ (π : p'.Y → p.Y) (_hπ : IsBlowupAlong m C π),
      p'.F = p.F.map (geoStrictTransform π C) ++ [π ⁻¹' C] ∧
      π p'.point = p.point ∧
      ∀ B : MarkedIdeal n X,
        let B' : MarkedIdeal n X := ⟨B.N,M.E,B.ideal,B.d⟩
        (record B' p'.H).N = geoStrictTransform π C (record B' p.H).N ∧
        (record B' p'.H).ideal = GermIdeal.pullback (m := m) π (record B' p.H).ideal := by
  let p := probeFamily hm M hM s q
  let d := probeStep hm M hM p
  refine ⟨d.π,d.hπ,rfl,d.point_map,?_⟩
  intro B
  exact ⟨rfl,rfl⟩

/-- The actual successor map carries the entire old/newest trace and the
composite original map, not just the distinguished selected point. -/
theorem probeFamily_succ_trace_dictionary (hm : 0 < m) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (s : ProbeState M m) (q : ℕ) :
    let p := probeFamily hm M hM s q
    let p' := probeFamily hm M hM s (q+1)
    let C := p.F.get p.old ∩ p.F.get p.newest
    ∃ (π : p'.Y → p.Y) (_hπ : IsBlowupAlong m C π),
      π p'.point = p.point ∧
      p'.F.get p'.old = geoStrictTransform π C (p.F.get p.old) ∧
      p'.F.get p'.newest = π ⁻¹' C ∧
      ∀ z : p'.Y, baseMap p'.H z = baseMap p.H (π z) := by
  let p := probeFamily hm M hM s q
  let d := probeStep hm M hM p
  refine ⟨d.π,d.hπ,d.point_map,?_,?_,?_⟩
  · change (p.F.map (geoStrictTransform d.π (p.F.get p.old ∩ p.F.get p.newest)) ++
        [d.π ⁻¹' (p.F.get p.old ∩ p.F.get p.newest)]).get ⟨p.old.val,by simp⟩ = _
    simp [List.get_eq_getElem,p.old.isLt]; rfl
  · change (p.F.map (geoStrictTransform d.π (p.F.get p.old ∩ p.F.get p.newest)) ++
        [d.π ⁻¹' (p.F.get p.old ∩ p.F.get p.newest)]).get ⟨p.F.length,by simp⟩ = _
    simp [List.get_eq_getElem]; rfl
  · intro z
    rfl

/-- One actual successor map simultaneously supplies the full boundary,
the old/new trace, the original composite, and every ordinary pullback. -/
theorem probeFamily_succ_combined_dictionary (hm : 0 < m) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (s : ProbeState M m) (q : ℕ) :
    let p := probeFamily hm M hM s q
    let p' := probeFamily hm M hM s (q+1)
    let C := p.F.get p.old ∩ p.F.get p.newest
    ∃ (π : p'.Y → p.Y) (_hπ : IsBlowupAlong m C π),
      p'.F = p.F.map (geoStrictTransform π C) ++ [π ⁻¹' C] ∧
      π p'.point = p.point ∧
      p'.F.get p'.old = geoStrictTransform π C (p.F.get p.old) ∧
      p'.F.get p'.newest = π ⁻¹' C ∧
      (∀ z : p'.Y, baseMap p'.H z = baseMap p.H (π z)) ∧
      ∀ B : MarkedIdeal n X,
        let B' : MarkedIdeal n X := ⟨B.N,M.E,B.ideal,B.d⟩
        (record B' p'.H).N = geoStrictTransform π C (record B' p.H).N ∧
        (record B' p'.H).ideal = GermIdeal.pullback (m := m) π (record B' p.H).ideal := by
  let p := probeFamily hm M hM s q
  let d := probeStep hm M hM p
  refine ⟨d.π,d.hπ,rfl,d.point_map,?_,?_,?_,?_⟩
  · change (p.F.map (geoStrictTransform d.π (p.F.get p.old ∩ p.F.get p.newest)) ++
        [d.π ⁻¹' (p.F.get p.old ∩ p.F.get p.newest)]).get ⟨p.old.val,by simp⟩ = _
    simp [List.get_eq_getElem,p.old.isLt]; rfl
  · change (p.F.map (geoStrictTransform d.π (p.F.get p.old ∩ p.F.get p.newest)) ++
        [d.π ⁻¹' (p.F.get p.old ∩ p.F.get p.newest)]).get ⟨p.F.length,by simp⟩ = _
    simp [List.get_eq_getElem]; rfl
  · intro z
    rfl
  · intro B
    exact ⟨rfl,rfl⟩

end
end Hironaka.HironakaG8ExceptionalProbeFamily
