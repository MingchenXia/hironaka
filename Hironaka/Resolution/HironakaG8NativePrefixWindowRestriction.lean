import Hironaka.Resolution.HironakaOriginalTerminalOverlapComparison
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Invariant.ResolutionInvariantSeq

/-! Literal chart histories on a common actual prefix after shrinking
the original ambient open. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativePrefixWindowRestriction

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MaxLocusLocal ResolutionInvariantSpec BlowupTowerIsomorphism BlowupTowerIsoTail
  HironakaOriginalTerminalOverlapComparison

variable {n k : ℕ} {Λ : Type*} [LinearOrder Λ] {X Y : CMfd.{0} n}

/-- Restrict the same actual prefix to the new ambient open. The rebased
record on its inherited chart is canonical for the literal double
restriction, with the same cosupport and numerical values at each point. -/
theorem native_prefix_values_on_shrunk_ambient
    (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ) (U O : Opens X)
    (P : MarkedIdeal n (CMfd.of (n := n) U)) (hP : IsInvDomain k P)
    (T : BlowupTower X Y) (hT : IsCanonical P (R.inv P) (restrict U T)) :
    let L := O ⊓ U
    let V := nestedOpens U L
    let W := nestedOpens O L
    let e := overlapBaseEquiv (n := n) (show L ≤ O from inf_le_left) (show L ≤ U from inf_le_right)
    let Q := MarkedIdeal.pullback e (MarkedIdeal.pullback (Subtype.val : V → U) P)
    let TS := restrict W (restrict O T)
    IsInvDomain k Q ∧ IsCanonical Q (R.inv Q) TS ∧
    ∃ f : openPreimage (restrict O T) W → openPreimage T U,
      (∀ z, (f z).val = z.val.val) ∧
      ((geoTransformAlong Q TS).cosupp = f ⁻¹' (geoTransformAlong P (restrict U T)).cosupp) ∧
      ((geoTransformAlong Q TS).E = (geoTransformAlong P (restrict U T)).E.map (f ⁻¹' ·)) ∧
      ∀ z ∈ (geoTransformAlong Q TS).cosupp,
        R.inv Q TS z = R.inv P (restrict U T) (f z) := by
  let L := O ⊓ U
  let V := nestedOpens U L
  let W := nestedOpens O L
  let e := overlapBaseEquiv (n := n) (show L ≤ O from inf_le_left) (show L ≤ U from inf_le_right)
  let P₀ := MarkedIdeal.pullback (Subtype.val : V → U) P
  let Q := MarkedIdeal.pullback e P₀
  let TO := restrict O T
  let TU := restrict U T
  let S := restrict W TO
  let D := restrict V TU
  let a := nestedDiffeo (n := n) (openPreimage T O) (openPreimage TO W) (openPreimage T L)
    (mem_openPreimage_restrict_nestedOpens O L T) (openPreimage_mono T (show L ≤ O from inf_le_left))
  let b := nestedDiffeo (n := n) (openPreimage T U) (openPreimage TU V) (openPreimage T L)
    (mem_openPreimage_restrict_nestedOpens U L T) (openPreimage_mono T (show L ≤ U from inf_le_right))
  let χ := a.trans b.symm
  have hIso : IsTowerIso e S D χ :=
    (isTowerIso_restrict_nestedOpens (show L ≤ O from inf_le_left) T).trans
      (isTowerIso_restrict_nestedOpens (show L ≤ U from inf_le_right) T).symm
  have hP₀ : IsInvDomain k P₀ := InvDomainTowerAlong.isInvDomain_pullback_val V hP
  have hQ : IsInvDomain k Q := InvDomainTowerAlong.isInvDomain_pullback e hP₀
  have hCanD : IsCanonical P₀ (R.inv P₀) D :=
    Seq.ResolutionInvariantExt.isCanonical_restrict R hP V TU hT
  have hCanS : IsCanonical Q (R.inv Q) S :=
    Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R hP₀ e hIso hCanD
  have hTestTU := R.isInvValue.isGeoTestTower_of_isCanonical hP TU hT
  have hTestD := R.isInvValue.isGeoTestTower_of_isCanonical hP₀ D hCanD
  have hCosD : (geoTransformAlong P₀ D).cosupp =
      (Subtype.val : openPreimage TU V → openPreimage T U) ⁻¹' (geoTransformAlong P TU).cosupp :=
    ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hP.isWellFormed.isClosedSubmanifold_N
      hP.isWellFormed.isCoherent V TU hTestTU
  have hCosS : (geoTransformAlong Q S).cosupp = χ ⁻¹' (geoTransformAlong P₀ D).cosupp :=
    IsTowerIso.cosupp_geoTransformAlong e hP₀.isWellFormed.isClosedSubmanifold_N hP₀.isWellFormed.isCoherent hIso hTestD
  let f (z : openPreimage TO W) : openPreimage T U := (χ z).val
  have hPoint (z : openPreimage TO W) : (f z).val = z.val.val := rfl
  have hCos : (geoTransformAlong Q S).cosupp = f ⁻¹' (geoTransformAlong P TU).cosupp := by
    rw [hCosS, hCosD]
    rfl
  have hGeoS : geoTransformAlong Q S = MarkedIdeal.pullback χ (geoTransformAlong P₀ D) :=
    IsTowerIso.geoTransformAlong_eq e hP₀.isWellFormed.isClosedSubmanifold_N hP₀.isWellFormed.isCoherent hIso hTestD
  have hGeoD : geoTransformAlong P₀ D =
      MarkedIdeal.pullback (Subtype.val : openPreimage TU V → openPreimage T U) (geoTransformAlong P TU) :=
    MarkedIdealRestrictOpen.geoTransformAlong_restrict V
      hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent TU hTestTU
  have hE : (geoTransformAlong Q S).E = (geoTransformAlong P TU).E.map (f ⁻¹' ·) := by
    rw [hGeoS, hGeoD]
    change ((geoTransformAlong P TU).E.map ((Subtype.val : openPreimage TU V → openPreimage T U) ⁻¹' ·)).map
      (χ ⁻¹' ·) = _
    rw [List.map_map]
    rfl
  refine ⟨hQ, hCanS, f, hPoint, hCos, hE, ?_⟩
  intro z hz
  have hzD : χ z ∈ (geoTransformAlong P₀ D).cosupp := by
    change z ∈ χ ⁻¹' (geoTransformAlong P₀ D).cosupp
    rw [← hCosS]
    exact hz
  have hzTU : f z ∈ (geoTransformAlong P TU).cosupp := by
    change z ∈ f ⁻¹' (geoTransformAlong P TU).cosupp
    rw [← hCos]
    exact hz
  exact (R.isInvValue.towerIso e P₀ hP₀ S D χ hIso hCanD z hzD).trans
    (R.isInvValue.restrictOpen P hP V TU hT (χ z) hzTU)

end

end Hironaka.HironakaG8NativePrefixWindowRestriction

#print axioms Hironaka.HironakaG8NativePrefixWindowRestriction.native_prefix_values_on_shrunk_ambient
