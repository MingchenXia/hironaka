/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurvePaddedComparisonRestriction

/-! Genuine nested restriction of chosen comparisons, retaining all actual
history and identity-padding positions. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveNestedComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplitIso BlowupTowerIsoTail
  MaxLocusLocal HironakaSharpActualCurveComparisonRestriction
  HironakaSharpActualCurvePaddedComparisonRestriction HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveTerminalPaddingComparison
variable {n : ℕ} {X X' Y Y' Z Z' : CMfd.{u} n}


/-- Real membership of the actual smaller windows gives their exact inverse image. -/
theorem nested_window_preimage (W' : Opens X') (W : Opens X) (V' : Opens X') (V : Opens X)
    (Φ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) W)
    (hWindow : ∀ x : W',(Φ x : X) ∈ V ↔ (x : X') ∈ V') :
    (nestedOpens W' V' : Set (CMfd.of (n := n) W'))=
      Φ ⁻¹' (nestedOpens W V : Set (CMfd.of (n := n) W)) := by
  ext x
  exact (hWindow x).symm

/-- The actual smaller base biholomorphism is a genuine restriction between
matching windows followed by the two true nested-open flattenings. -/
def nestedBaseComparison (W' : Opens X') (W : Opens X) (V' : Opens X') (V : Opens X)
    (hV'W' : V'≤W') (hVW : V≤W)
    (Φ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) W)
    (hWindow : ∀ x : W',(Φ x : X) ∈ V ↔ (x : X') ∈ V') :
    CMfd.of (n := n) V' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V :=
  (nestedOpensDiffeo (n := n) hV'W').symm.trans
    ((openRestriction Φ (nestedOpens W' V') (nestedOpens W V)
      (nested_window_preimage W' W V' V Φ hWindow)).trans (nestedOpensDiffeo (n := n) hVW))

@[simp] theorem nestedBaseComparison_val
    (W' : Opens X') (W : Opens X) (V' : Opens X') (V : Opens X)
    (hV'W' : V'≤W') (hVW : V≤W)
    (Φ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) W)
    (hWindow : ∀ x : W',(Φ x : X) ∈ V ↔ (x : X') ∈ V') (x : V') :
    (nestedBaseComparison W' W V' V hV'W' hVW Φ hWindow x : X)=
      (Φ ⟨x.val,hV'W' x.property⟩ : X) := rfl


/-- Exact actual source opens may be named independently once their real
inverse-image equality has been proved. -/
private theorem exists_matching_open_restriction
    {A A' B B' : CMfd.{u} n}
    {Φ : A' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {T' : BlowupTower A' B'} {T : BlowupTower A B}
    {χ : B' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    (h : IsTowerIso Φ T' T χ) (U' : Opens A') (U : Opens A)
    (hU : (U' : Set A')=Φ ⁻¹' (U : Set A)) :
    ∃ e : CMfd.of (n := n) (openPreimage T' U')
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U),
      IsTowerIso (openRestriction Φ U' U hU) (restrict U' T') (restrict U T) e ∧
      ∀ z,(e z : B)=χ z.val := by
  have hEq : U'=preimageOpen Φ U := SetLike.coe_injective hU
  subst U'
  exact ⟨_,HironakaSharpActualCurveComparisonRestriction.IsTowerIso.open_restriction h U,fun _ => rfl⟩

/-- This is the existing genuine nested tower isomorphism with its actual
ambient point dictionary, not an assumed flattening certificate. -/
private theorem exists_actual_nested_flattening (T : BlowupTower X Y)
    {W V : Opens X} (hVW : V≤W) :
    ∃ e : CMfd.of (n := n) (openPreimage (restrict W T) (nestedOpens W V))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T V),
      IsTowerIso (nestedOpensDiffeo (n := n) hVW)
        (restrict (nestedOpens W V) (restrict W T)) (restrict V T) e ∧
      ∀ z,(e z : Y)=z.val.val :=
  ⟨_,isTowerIso_restrict_nestedOpens hVW T,fun _ => rfl⟩

/-- Restrict the actual chosen comparison first, then flatten both literal
double histories; the exact old point map is retained. -/
theorem exists_nested_tower_comparison
    (W' : Opens X') (W : Opens X) (V' : Opens X') (V : Opens X)
    (hV'W' : V'≤W') (hVW : V≤W)
    (Φ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) W)
    (hWindow : ∀ x : W',(Φ x : X) ∈ V ↔ (x : X') ∈ V')
    (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (χ : CMfd.of (n := n) (openPreimage T' W')
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T W))
    (h : IsTowerIso Φ (restrict W' T') (restrict W T) χ) :
    ∃ e : CMfd.of (n := n) (openPreimage T' V')
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T V),
      IsTowerIso (nestedBaseComparison W' W V' V hV'W' hVW Φ hWindow)
        (restrict V' T') (restrict V T) e ∧
      ∀ z,(e z : Y)=(χ ⟨z.val,openPreimage_mono T' hV'W' z.property⟩ : Y) := by
  obtain ⟨es,hs,hsPoint⟩ := exists_actual_nested_flattening T' hV'W'
  obtain ⟨et,ht,htPoint⟩ := exists_actual_nested_flattening T hVW
  obtain ⟨er,hr,hrPoint⟩ := exists_matching_open_restriction h
    (nestedOpens W' V') (nestedOpens W V) (nested_window_preimage W' W V' V Φ hWindow)
  let e := es.symm.trans (er.trans et)
  refine ⟨e,hs.symm.trans (hr.trans ht),?_⟩
  intro z
  have hInv : ((es.symm z).val : Y')=z.val := by
    calc
      ((es.symm z).val : Y')=(es (es.symm z) : Y') := (hsPoint (es.symm z)).symm
      _ = z.val := congrArg Subtype.val (es.apply_symm_apply z)
  have hIncluded : (es.symm z).val=
      (⟨z.val,openPreimage_mono T' hV'W' z.property⟩ : openPreimage T' W') := Subtype.ext hInv
  calc
    (e z : Y)=((er (es.symm z)).val : Y) := htPoint (er (es.symm z))
    _ = (χ (es.symm z).val : Y) := congrArg Subtype.val (hrPoint (es.symm z))
    _ = (χ ⟨z.val,openPreimage_mono T' hV'W' z.property⟩ : Y) :=
      congrArg (fun w : openPreimage T' W' => (χ w : Y)) hIncluded


/-- Conjugate the chosen real padded comparison to the raw whole histories,
restrict/flatten those genuine histories, then normalize both actual smaller
padded histories. All old endpoint maps are retained on underlying points. -/
theorem exists_nested_padded_comparison
    (W' : Opens X') (W : Opens X) (V' : Opens X') (V : Opens X)
    (hV'W' : V'≤W') (hVW : V≤W)
    (Φ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) W)
    (hWindow : ∀ x : W',(Φ x : X) ∈ V ↔ (x : X') ∈ V')
    (P' : BlowupTower X' Y') (P : BlowupTower X Y)
    (S' : BlowupTower Y' Z') (S : BlowupTower Y Z) (L : ℕ)
    (χ : CMfd.of (n := n) (openPreimage S' (openPreimage P' W'))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S (openPreimage P W)))
    (h : IsTowerIso Φ (paddedHistory (restrict W' P') (restrict (openPreimage P' W') S') L)
      (paddedHistory (restrict W P) (restrict (openPreimage P W) S) L) χ) :
    ∃ e : CMfd.of (n := n) (openPreimage S' (openPreimage P' V'))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S (openPreimage P V)),
      IsTowerIso (nestedBaseComparison W' W V' V hV'W' hVW Φ hWindow)
        (paddedHistory (restrict V' P') (restrict (openPreimage P' V') S') L)
        (paddedHistory (restrict V P) (restrict (openPreimage P V) S) L) e ∧
      ∀ z,(e z : Z)=(χ ⟨z.val,openPreimage_mono S' (openPreimage_mono P' hV'W') z.property⟩ : Z) := by
  obtain ⟨fsW,hfsW,hfsWPoint⟩ := exists_padded_history_open_flattening P' S' L W'
  obtain ⟨ftW,hftW,hftWPoint⟩ := exists_padded_history_open_flattening P S L W
  let χraw := fsW.trans (χ.trans ftW.symm)
  have hRaw : IsTowerIso Φ (restrict W' (paddedHistory P' S' L))
      (restrict W (paddedHistory P S L)) χraw :=
    BlowupTowerSplitIso.IsTowerIso.congr_base (hfsW.trans (h.trans hftW.symm)) (fun _ => rfl)
  obtain ⟨eN,hN,hNPoint⟩ := exists_nested_tower_comparison W' W V' V hV'W' hVW Φ hWindow
    (paddedHistory P' S' L) (paddedHistory P S L) χraw hRaw
  obtain ⟨fsV,hfsV,hfsVPoint⟩ := exists_padded_history_open_flattening P' S' L V'
  obtain ⟨ftV,hftV,hftVPoint⟩ := exists_padded_history_open_flattening P S L V
  let e := fsV.symm.trans (eN.trans ftV)
  refine ⟨e,BlowupTowerSplitIso.IsTowerIso.congr_base (hfsV.symm.trans (hN.trans hftV))
    (fun _ => rfl),?_⟩
  intro z
  have hInvSmall : (fsV.symm z : Z')=z.val := by
    calc
      (fsV.symm z : Z')=(fsV (fsV.symm z) : Z') := (hfsVPoint (fsV.symm z)).symm
      _ = z.val := congrArg Subtype.val (fsV.apply_symm_apply z)
  let yBig : openPreimage (paddedHistory P' S' L) W' :=
    ⟨(fsV.symm z).val,openPreimage_mono (paddedHistory P' S' L) hV'W' (fsV.symm z).property⟩
  have hBigSource : fsW yBig=
      (⟨z.val,openPreimage_mono S' (openPreimage_mono P' hV'W') z.property⟩ :
        openPreimage S' (openPreimage P' W')) :=
    Subtype.ext ((hfsWPoint yBig).trans hInvSmall)
  have hTargetBigInv (w : openPreimage S (openPreimage P W)) : (ftW.symm w : Z)=w.val := by
    calc
      (ftW.symm w : Z)=(ftW (ftW.symm w) : Z) := (hftWPoint (ftW.symm w)).symm
      _ = w.val := congrArg Subtype.val (ftW.apply_symm_apply w)
  calc
    (e z : Z)=(eN (fsV.symm z) : Z) := hftVPoint (eN (fsV.symm z))
    _ = (χraw yBig : Z) := hNPoint (fsV.symm z)
    _ = (χ (fsW yBig) : Z) := hTargetBigInv (χ (fsW yBig))
    _ = (χ ⟨z.val,openPreimage_mono S' (openPreimage_mono P' hV'W') z.property⟩ : Z) :=
      congrArg (fun w : openPreimage S' (openPreimage P' W') => (χ w : Z)) hBigSource

/-- A direct smaller-window comparison at ANY genuine bounded cut has
exactly the old chosen terminal point map, not a replacement witness. -/
theorem nested_padded_comparison_direct
    (W' : Opens X') (W : Opens X) (V' : Opens X') (V : Opens X)
    (hV'W' : V'≤W') (hVW : V≤W)
    (Φ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) W)
    (hWindow : ∀ x : W',(Φ x : X) ∈ V ↔ (x : X') ∈ V')
    (P' : BlowupTower X' Y') (P : BlowupTower X Y)
    (S' : BlowupTower Y' Z') (S : BlowupTower Y Z)
    (L K : ℕ) (hL' : S'.length≤L) (hL : S.length≤L)
    (hK' : S'.length≤K) (hK : S.length≤K)
    (χ : CMfd.of (n := n) (openPreimage S' (openPreimage P' W'))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S (openPreimage P W)))
    (h : IsTowerIso Φ (paddedHistory (restrict W' P') (restrict (openPreimage P' W') S') L)
      (paddedHistory (restrict W P) (restrict (openPreimage P W) S) L) χ)
    (e : CMfd.of (n := n) (openPreimage S' (openPreimage P' V'))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S (openPreimage P V)))
    (he : IsTowerIso (nestedBaseComparison W' W V' V hV'W' hVW Φ hWindow)
      (paddedHistory (restrict V' P') (restrict (openPreimage P' V') S') K)
      (paddedHistory (restrict V P) (restrict (openPreimage P V) S) K) e) :
    ∀ z,(e z : Z)=(χ ⟨z.val,openPreimage_mono S' (openPreimage_mono P' hV'W') z.property⟩ : Z) := by
  obtain ⟨eL,heL,hPoint⟩ := exists_nested_padded_comparison W' W V' V hV'W' hVW Φ hWindow P' P S' S L χ h
  have hEq := terminal_padding_comparison_independent
    (P' := restrict V' P') (P := restrict V P)
    (S' := restrict (openPreimage P' V') S') (S := restrict (openPreimage P V) S) L K
    (by simpa only [length_restrict] using hL') (by simpa only [length_restrict] using hL)
    (by simpa only [length_restrict] using hK') (by simpa only [length_restrict] using hK) heL he
  rw [←hEq]
  exact hPoint

end
end Hironaka.HironakaSharpActualCurveNestedComparison
