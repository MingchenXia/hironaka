import Hironaka.Invariant.StepOneRestrictOpen
import Hironaka.Resolution.HironakaActualRawRecordPullbacks

/-! # O7a′, layer N1: the Step 1 data restrict along EVERY tower

Lane G3 (run 0080, round 1).  Blueprint: `hironaka-g3-r-raw-step-one-locality.tex`.
Plan: `work/hironaka-resume-20261111/G3/O7A-PRIME-PLAN.md` (§4, node N1, Step-1 layer).

`StepOneRestrictOpen.restrict_facts` (`StepOneRestrictOpen.lean:75`) and `ContactLowerValue.origMembers_restrict`
(`ContactLowerValue.lean:229`) assume that `T` is a GLOBAL multiple test blow-up of `J̄ = barMarked 𝔍`; their only use of
it is the restriction of the transform, which holds along every tower
(`HironakaActualRawRecordPullbacks.geoTransformAlong_restrict_of_hhol`).  Hence, for `𝔍` well formed with `d ≥ 1` and
EVERY tower `T` (no test, canonicity or domain hypothesis):

* `geoTransformAlong_barMarked_restrict_raw`: the marked ideal of Step 1 of `𝔍|_U` along `T|_U` is the restriction of that
  of `𝔍` along `T`;
* `origMembers_restrict_raw`, `restrict_facts_raw`: original members, cosupport, levels, special points and Step-1 regimes
  are the traces of those along `T`;
* **`regimeRun_stepRegime_restrict_raw`**: the runs of every point in the Step-1 regimes agree.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RRawStepOneLocality

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime
  Hironaka.StepOneValue Hironaka.StepOneLowerDomain
  Hironaka.StepOneValueMasked Hironaka.StepOneCanonicalTail
  Hironaka.HomogenizedIdealAlong Hironaka.CodimOneSupportAlong
  Hironaka.MarkedIdealRestrictOpen Hironaka.MemberInterLocusAlong
  Hironaka.BlowupTowerIsoTail Hironaka.MarkedIdealBiholomorphism
  Hironaka.HironakaActualRawRecordPullbacks

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (U : Opens X)

/-- **The marked ideal of Step 1 of `𝔍|_U` along `T|_U` is the restriction of that of `𝔍` along `T`**, for every tower. -/
theorem geoTransformAlong_barMarked_restrict_raw (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) :
    geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
        (restrict U T) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong (barMarked 𝔍) T) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  rw [show barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
      MarkedIdeal.pullback (Subtype.val : U → X) (barMarked 𝔍) from
    ContactStageKept.barMarked_pullback_val U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd]
  exact geoTransformAlong_restrict_of_hhol (barMarked 𝔍)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ.isCoherent hg) U T

/-- **Original members restrict**, for every tower. -/
theorem origMembers_restrict_raw (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    origMembers (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T₀) =
      (origMembers 𝔍 T₀).map ((Subtype.val : openPreimage T₀ U → Y₀) ⁻¹' ·) := by
  have hg := geoTransformAlong_barMarked_restrict_raw 𝔍 U h𝔍 hd T₀
  show (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T₀)).E.take (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).E.length = _
  rw [hg]
  show ((geoTransformAlong (barMarked 𝔍) T₀).E.map ((Subtype.val : openPreimage T₀ U → Y₀) ⁻¹' ·)).take
      (𝔍.E.map ((Subtype.val : U → X) ⁻¹' ·)).length = _
  rw [List.length_map, ← List.map_take]
  rfl

/-- **Cosupport, levels, special points and Step-1 regimes restrict**, for every tower. -/
theorem restrict_facts_raw (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
        (restrict U T)).cosupp = (Subtype.val : openPreimage T U → Y) ⁻¹' (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
      ∀ p : openPreimage T U,
        level (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p =
            level 𝔍 T p ∧
          (IsSpecial (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p ↔
            IsSpecial 𝔍 T p) ∧
          ∀ s, stepRegime (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) s (restrict U T) p ↔
            stepRegime 𝔍 s T p := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hholT := holomorphic_geoTransformAlong (barMarked 𝔍)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ.isCoherent hg) T
  have hg := geoTransformAlong_barMarked_restrict_raw 𝔍 U h𝔍 hd T
  have hc : (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T)).cosupp = (Subtype.val : openPreimage T U → Y) ⁻¹' (geoTransformAlong (barMarked 𝔍) T).cosupp := by
    rw [hg]
    exact cosupp_pullback_val _ hholT _
  have hO := origMembers_restrict_raw 𝔍 U h𝔍 hd T
  refine ⟨hc, fun p => ?_⟩
  have hl : level (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p =
      level 𝔍 T p := by
    unfold level
    rw [hO]
    exact CodimOnePartCanonical.boundaryCount_map_preimage _ _ p
  have hs : IsSpecial (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p ↔
      IsSpecial 𝔍 T p := by
    have hcod := CodimOnePartCanonical.codimOnePartAlong_pullback_val (openPreimage T U)
      (𝔞 := (geoTransformAlong (barMarked 𝔍) T).ideal) hholT
      (N := (geoTransformAlong (barMarked 𝔍) T).N) (geoTransformAlong (barMarked 𝔍) T).d
    have hmem := memberInterLocus_preimage (Subtype.val : openPreimage T U → Y)
      (fun z => (openPreimage T U).isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z)
      (geoTransformAlong (barMarked 𝔍) T).N (origMembers 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp
    unfold IsSpecial
    rw [hl, hO, hg]
    rw [← hc, hg] at hmem
    refine or_congr (and_congr_right fun _ => ?_) (and_congr_right fun _ => ?_)
    · rw [show codimOnePartAlong (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
          (geoTransformAlong (barMarked 𝔍) T)).N (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
          (geoTransformAlong (barMarked 𝔍) T)).ideal (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
          (geoTransformAlong (barMarked 𝔍) T)).d = _ from hcod]
      rfl
    · show p ∈ memberInterLocus ((Subtype.val : openPreimage T U → Y) ⁻¹' (geoTransformAlong (barMarked 𝔍) T).N)
          ((origMembers 𝔍 T).map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·))
          (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong (barMarked 𝔍) T)).cosupp ↔ _
      rw [hmem]
      rfl
  exact ⟨hl, hs, fun s => by unfold stepRegime; rw [hl, hs]⟩

/-- **The runs in the Step-1 regimes restrict**, for every tower. -/
theorem regimeRun_stepRegime_restrict_raw (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (s : ℕ) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (p : openPreimage T U) :
    regimeRun (stepRegime (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) s) (restrict U T) p =
      regimeRun (stepRegime 𝔍 s) T p :=
  NonmonomialOrderRegime.regimeRun_restrict_of U (stepRegime 𝔍 s) _ (fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun T _ p => ((restrict_facts_raw 𝔍 U h𝔍 hd T).2 p).2.2 s) T trivial p

end

end Hironaka.HironakaG3RRawStepOneLocality
