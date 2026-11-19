import Hironaka.Resolution.HironakaG1CommonGraphRestrictionMaps
import Hironaka.Resolution.HironakaG1NativeCoordinateWindow
import Hironaka.Resolution.HironakaG1IteratedNormalBlockIdeal

/-! Independent original native records compared on their actual common graph. -/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1ActualCommonGraphNativeComparison

noncomputable section

open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec HironakaG11PresLineState HironakaG11PresLineStable HironakaG8LocalHistory
  HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
  HironakaActualIntrinsicIsoPairedWindows HironakaActualLocalCommonGraphModel
  HironakaG1NormalGraphFlags HironakaG1IteratedNormalBlockIdeal
  HironakaG1CommonGraphRestrictionMaps HironakaG1NativeCoordinateWindow
  HironakaG1IndependentFiniteNormalNative

variable {a b : ℕ} {U A : Opens (ComplexModel a)} {V B : Opens (ComplexModel b)}

private def reindexedAmbient {m d : ℕ} (X : CMfd.{0} m) (h : m = d) : CMfd.{0} d := by
  letI := chartedSpaceReindex (T := X) h
  letI := isComplexManifoldReindex (T := X) h
  exact CMfd.of (n := d) X

private def reindexedMarked {m d : ℕ} {X : CMfd.{0} m}
    (P : MarkedIdeal m X) (h : m = d) : MarkedIdeal d (reindexedAmbient X h) := by
  subst d
  exact P

private theorem reindexedMarked_d {m d : ℕ} {X : CMfd.{0} m}
    (P : MarkedIdeal m X) (h : m = d) : (reindexedMarked P h).d = P.d := by
  subst d
  rfl

private theorem reindexedMarked_E {m d : ℕ} {X : CMfd.{0} m}
    (P : MarkedIdeal m X) (h : m = d) : (reindexedMarked P h).E = P.E := by
  subst d
  rfl

private theorem nativeHSState_reindex {m d : ℕ} {X : CMfd.{0} m} {P : MarkedIdeal m X}
    {W : Set X} {H : ℕ → ℕ} (hP : NativeHSState P W H) (h : m = d) :
    NativeHSState (X := reindexedAmbient X h) (reindexedMarked P h) W H := by
  subst d
  exact hP

private abbrev common (A : Opens (ComplexModel a)) (B : Opens (ComplexModel b)) :=
  CMfd.of (n := a + b) (commonDomain A B)

/-- The first literal padded record restricted to the common ambient. -/
def commonGraphLeftMarked (P : MarkedIdeal (a + b) (blockOpen A b)) :
    MarkedIdeal (a + b) (common A B) :=
  MarkedIdeal.pullback (commonGraphFirstRestriction (B := B) (le_refl A)) P

/-- The second literal padded record restricted after the actual block
swap and the arithmetic identification of the ambient dimensions. -/
def commonGraphRightMarked (Q : MarkedIdeal (b + a) (blockOpen B a)) :
    MarkedIdeal (a + b) (common A B) :=
  MarkedIdeal.pullback (M := reindexedAmbient (CMfd.of (n := b + a) (blockOpen B a)) (Nat.add_comm b a))
    (M' := common A B) (commonGraphSecondRestriction (A := A) (le_refl B))
    (reindexedMarked (X := CMfd.of (n := b + a) (blockOpen B a)) Q (Nat.add_comm b a))

@[simp] theorem commonGraphLeftMarked_d (P : MarkedIdeal (a + b) (blockOpen A b)) :
    (commonGraphLeftMarked (B := B) P).d = P.d := rfl

@[simp] theorem commonGraphRightMarked_d (Q : MarkedIdeal (b + a) (blockOpen B a)) :
    (commonGraphRightMarked (A := A) Q).d = Q.d :=
  reindexedMarked_d (X := CMfd.of (n := b + a) (blockOpen B a)) Q (Nat.add_comm b a)

/-- The restriction of the first ordered boundary uses the literal first
ambient inclusion. -/
theorem commonGraphLeftMarked_E (P : MarkedIdeal (a + b) (blockOpen A b)) :
    (commonGraphLeftMarked (B := B) P).E =
      P.E.map (commonGraphFirstRestriction (B := B) (le_refl A) ⁻¹' ·) := rfl

/-- The restriction of the second ordered boundary uses the actual block
swap, with no change of slots in the dimension reindexing. -/
theorem commonGraphRightMarked_E (Q : MarkedIdeal (b + a) (blockOpen B a)) :
    (commonGraphRightMarked (A := A) Q).E =
      Q.E.map (commonGraphSecondRestriction (A := A) (le_refl B) ⁻¹' ·) := by
  change (reindexedMarked (X := CMfd.of (n := b + a) (blockOpen B a)) Q (Nat.add_comm b a)).E.map _ = _
  rw [reindexedMarked_E]
  rfl

private theorem contMDiff_coordinateWindow {m n : ℕ} {O : Opens (ComplexModel m)}
    {F : ComplexModel m → ComplexModel n} (hF : ContDiffOn ℂ ∞ F O) :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (fun x : O => F x.val) := by
  intro x
  exact contMDiffAt_subtype_iff.mpr ((hF.contDiffAt (O.isOpen.mem_nhds x.property)).contMDiffAt)

set_option maxHeartbeats 1300000 in
/-- An intrinsic isomorphism of two independent native originals supplies
the actual common normal graph chart and the two whole weighted records
there. Both records have the same intrinsic profile and carrier. With
equal transported ordered boundaries, they have identical local weak
tests. Their original marks are retained separately. -/
theorem exists_actual_commonGraph_native_comparison {C : Set U} {D : Set V}
    (P : MarkedIdeal a U) (Q : MarkedIdeal b V) (H : ℕ → ℕ)
    (hP : NativeHSState (X := CMfd.of (n := a) U) P C H) (hPD : IsInvDomain a P)
    (hQ : NativeHSState (X := CMfd.of (n := b) V) Q D H) (hQD : IsInvDomain b Q)
    (e : actualSubspaceLocallyRingedSpace (n := a) C ≅
      actualSubspaceLocallyRingedSpace (n := b) D)
    (he : e.hom ≫ subspacePointMap (n := b) D = subspacePointMap (n := a) C) (c : C) :
    ∃ (A : Opens (ComplexModel a)) (B : Opens (ComplexModel b))
      (F : ComplexModel a → ComplexModel b) (G : ComplexModel b → ComplexModel a)
      (hAU : A ≤ U) (hBV : B ≤ V),
      c.val.val ∈ A ∧ (e.hom.base c).val.val ∈ B ∧
      ContDiffOn ℂ ∞ F A ∧ ContDiffOn ℂ ∞ G B ∧
      let S := commonGraphSubset A B F (coordinateCarrier C ∩ (A : Set (ComplexModel a)))
      let P' := MarkedIdeal.pullback (Opens.inclusion hAU) P
      let Q' := MarkedIdeal.pullback (Opens.inclusion hBV) Q
      let L := commonGraphLeftMarked (B := B) (blockAmbientMarked (fun x : A => F x.val) P')
      let R := commonGraphRightMarked (A := A) (blockAmbientMarked (fun y : B => G y.val) Q')
      NativeHSState (X := common A B) L S H ∧ NativeHSState (X := common A B) R S H ∧
      L.d = P.d ∧ R.d = Q.d ∧ (R.E = L.E → LocWPEquiv (X := common A B) L R) := by
  obtain ⟨A, B, F, G, hAU, hBV, hcA, hdB, hF, hG, hGraphL, hGraphR⟩ :=
    exists_actual_commonBlockGraph_restrictions e he hP.2.1 hQ.2.1 c
  obtain ⟨hD₁, hS₁⟩ := nativeHSState_coordinateWindow hP hPD hAU
  obtain ⟨hD₂, hS₂⟩ := nativeHSState_coordinateWindow hQ hQD hBV
  rw [← coordinateWindow_preimage C hAU] at hS₁
  rw [← coordinateWindow_preimage D hBV] at hS₂
  let P' := MarkedIdeal.pullback (Opens.inclusion hAU) P
  let Q' := MarkedIdeal.pullback (Opens.inclusion hBV) Q
  let LP := blockAmbientMarked (fun x : A => F x.val) P'
  let RP := blockAmbientMarked (fun y : B => G y.val) Q'
  let Y₁ := CMfd.of (n := a + b) (blockOpen A b)
  let Y₂ := CMfd.of (n := b + a) (blockOpen B a)
  let Z := common A B
  have hL := (blockAmbientMarked_nativeHSState _ (contMDiff_coordinateWindow hF) P' H hS₁ hD₁).2
  have hR := (blockAmbientMarked_nativeHSState _ (contMDiff_coordinateWindow hG) Q' H hS₂ hD₂).2
  have hR' := nativeHSState_reindex (X := Y₂) (P := RP) hR (Nat.add_comm b a)
  let i₁ : Z → Y₁ := commonGraphFirstRestriction (B := B) (le_refl A)
  let i₂ : Z → reindexedAmbient Y₂ (Nat.add_comm b a) :=
    commonGraphSecondRestriction (A := A) (le_refl B)
  have h₁ := nativeHSState_pullback_openEmbedding (X := Y₁) (Z := Z) hL i₁
    (commonGraphFirstRestriction_isOpenHoloEmbedding (B := B) (le_refl A))
  have h₂ := nativeHSState_pullback_openEmbedding (X := reindexedAmbient Y₂ (Nat.add_comm b a))
    (Z := Z) hR' i₂ (commonGraphSecondRestriction_isOpenHoloEmbedding (A := A) (le_refl B))
  rw [show i₁ ⁻¹' blockGraph (fun x : A => F x.val) (Opens.inclusion hAU ⁻¹' C) = _ from hGraphL] at h₁
  rw [show i₂ ⁻¹' blockGraph (fun y : B => G y.val) (Opens.inclusion hBV ⁻¹' D) = _ from hGraphR] at h₂
  refine ⟨A, B, F, G, hAU, hBV, hcA, hdB, hF, hG, h₁, h₂, rfl, ?_, ?_⟩
  · exact commonGraphRightMarked_d RP
  · exact fun hE => locWPEquiv_native h₁ h₂ hE

end

end Hironaka.HironakaG1ActualCommonGraphNativeComparison
