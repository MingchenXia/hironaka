import Hironaka.Resolution.HironakaActualRawOrderLocality
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.GeneralValue

/-! # O7a′, layer N1: the order regime and its runs restrict along EVERY tower

Lane G3 (run 0080, round 1).  Blueprint: `hironaka-g3-r-raw-regime-locality.tex`.
Plan: `work/hironaka-resume-20261111/G3/O7A-PRIME-PLAN.md` (§4, node N1).

The held restriction laws of the order regime (`NonmonomialOrderRegime.regimeRun_ordRegime_restrict`,
`NonmonomialOrderRegime.lean:165`) assume a GLOBAL multiple test blow-up of a marked ideal in the domain.  The window-local
law O7a′ needs them along towers that are canonical only over a window.  For a marked ideal whose members are holomorphic
and closed under holomorphic spans (e.g. a coherent ideal), the transform restricts along every tower
(`HironakaActualRawRecordPullbacks.geoTransformAlong_restrict_of_hhol`) and the order of the nonmonomial part is local
(`HironakaActualRawOrderLocality.nmOrd_pullback_of_local`); hence:

* `cosupp_restrict_raw`, `nmOrd_restrict_raw`: cosupport and order of `(𝔪|_U)` along `T|_U` are the traces of those of
  `𝔪` along `T`, for EVERY tower `T`;
* `ordRegime_restrict_iff_raw`, **`regimeRun_ordRegime_restrict_raw`**: the regimes `OrdRegime` and the runs of every
  point in them agree, for every tower;
* `genInv_fst_restrict_raw`: the first coordinate of the general value restricts, for every tower and every max-order value.

No test, canonicity or domain hypothesis on `T`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG3RRawRegimeLocality

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen
  StepOneRegime NonmonomialOrderLocal NonmonomialOrderRegime HironakaActualRawRecordPullbacks
  HironakaActualRawOrderLocality GeneralValue MarkedIdealBiholomorphism

variable {n : ℕ} {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)
  (hhol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x)
  (hcl : ∀ x g, IsInSpanAt (n := n) (𝔪.ideal.mem x) x g → 𝔪.ideal.mem x g) (U : Opens X)

include hhol in
/-- **The cosupport along a restricted tower is the trace of the cosupport**, for every tower. -/
theorem cosupp_restrict_raw {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).cosupp =
      (Subtype.val : openPreimage T U → Y) ⁻¹' (geoTransformAlong 𝔪 T).cosupp := by
  rw [geoTransformAlong_restrict_of_hhol 𝔪 hhol U T]
  exact cosupp_pullback_val _ (holomorphic_geoTransformAlong 𝔪 hhol T) _

include hhol hcl in
/-- **The order of the nonmonomial part along a restricted tower is the order along the tower**, for every tower. -/
theorem nmOrd_restrict_raw {Y : CMfd.{u} n} (T : BlowupTower X Y) (p : openPreimage T U) :
    nmOrd (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)) p =
      nmOrd (geoTransformAlong 𝔪 T) (p : Y) := by
  rw [geoTransformAlong_restrict_of_hhol 𝔪 hhol U T]
  exact nmOrd_pullback_of_local (X := Y) (Y := CMfd.of (n := n) (openPreimage T U)) contMDiff_subtype_val
    (fun q => ⟨DerivativeIdealAlongEtale.openInv (openPreimage T U) q,
      DerivativeIdealAlongEtale.isLocalInverseAt_val (openPreimage T U) q⟩)
    _ (holomorphic_geoTransformAlong 𝔪 hhol T) (span_closed_geoTransformAlong 𝔪 hcl T) p

include hhol hcl in
/-- **The order regimes restrict**, for every tower. -/
theorem ordRegime_restrict_iff_raw (o : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y) (p : openPreimage T U) :
    OrdRegime (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) o (restrict U T) p ↔
      OrdRegime 𝔪 o T p := by
  rw [ordRegime_iff, ordRegime_iff, cosupp_restrict_raw 𝔪 hhol U T, nmOrd_restrict_raw 𝔪 hhol hcl U T p]
  rfl

include hhol hcl in
/-- **The runs in the order regimes restrict**, for every tower (no test, canonicity or domain hypothesis). -/
theorem regimeRun_ordRegime_restrict_raw (o : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y) (p : openPreimage T U) :
    regimeRun (OrdRegime (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) o) (restrict U T) p =
      regimeRun (OrdRegime 𝔪 o) T p :=
  regimeRun_restrict_of U (OrdRegime 𝔪 o) _ (fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun T _ p => ordRegime_restrict_iff_raw 𝔪 hhol hcl U o T p) T trivial p

include hhol hcl in
/-- **The first coordinate of the general value restricts**, for every tower and every value function `M`. -/
theorem genInv_fst_restrict_raw {Λ : Type v} [LinearOrder Λ]
    (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (p : openPreimage T U) :
    (ofLex (genInv M (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T) p)).1 =
      (ofLex (genInv M 𝔪 T p)).1 := by
  rw [genInv_fst, genInv_fst]
  exact nmOrd_restrict_raw 𝔪 hhol hcl U T p

omit hhol hcl in
/-- **The runs restrict for every tower, for a coherent ideal.** -/
theorem regimeRun_ordRegime_restrict_of_isCoherent (h𝔞 : 𝔪.ideal.IsCoherent) (o : ℕ) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (p : openPreimage T U) :
    regimeRun (OrdRegime (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) o) (restrict U T) p =
      regimeRun (OrdRegime 𝔪 o) T p :=
  regimeRun_ordRegime_restrict_raw 𝔪
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg)
    (fun _ _ hf => Hironaka.HomogenizedIdeal.mem_of_isInSpanAt h𝔞 hf) U o T p

end

end Hironaka.HironakaG3RRawRegimeLocality
