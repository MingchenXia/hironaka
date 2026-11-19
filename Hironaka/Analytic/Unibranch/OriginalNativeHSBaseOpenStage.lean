import Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenWindows
import Hironaka.Blowup.BlowupTowerIsoTail

/-! Derive actual new admissible overlaps and physical compatible stages over
an actual native base open. Blueprint FIRST: original-native-hs-base-open-stage.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenStage
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers HironakaG11CompatibleCanonicalTowers
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq
open ResolutionInvariantSpec (IsCanonical)

variable {X B : SourceReducedComplexSpace} {n : ℕ} {ι : Type*}
  (w : ι → DimEmbedding X n) (j : B ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
local notation "wN" => OriginalNativeHSBaseOpenWindows.window w j hj

private def coordinateImage (i : ι) (V : Opens (wN i).ambient) : Opens (ComplexModel n) :=
  ⟨(Subtype.val : (wN i).ambient → ComplexModel n) '' V,
    (wN i).ambient.isOpen.isOpenMap_subtype_val _ V.isOpen⟩

private theorem coordinateImage_subset (i : ι) (V : Opens (wN i).ambient) :
    coordinateImage w j hj i V ≤ (wN i).ambient := by
  rintro _ ⟨z, -, rfl⟩
  exact z.property

private theorem coordinateImage_old_subset (i : ι) (V : Opens (wN i).ambient) :
    coordinateImage w j hj i V ≤ (w i).ambient :=
  fun _ hx => OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset (w i).toLocalEmbedding j hj
    (coordinateImage_subset w j hj i V hx)

def overlapOpen (i : ι) (V : Opens (wN i).ambient) : Opens (w i).ambient :=
  MaxLocusLocal.nestedOpens (w i).ambient (coordinateImage w j hj i V)

theorem overlap_subset (i : ι) (V : Opens (wN i).ambient) :
    overlapOpen w j hj i V ≤ OriginalNativeHSBaseOpenWindows.traceOpen w j hj i := by
  rintro z ⟨u, hu, heq⟩
  have hz : (OriginalNativeHSBaseOpenWindows.baseEquiv w j hj i u).val = z := Subtype.ext heq
  exact hz ▸ (OriginalNativeHSBaseOpenWindows.baseEquiv w j hj i u).property

private theorem coordinateImage_dictionary (i : ι) (V : Opens (wN i).ambient) (z : (wN i).ambient) :
    z ∈ V ↔ z.val ∈ coordinateImage w j hj i V := by
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨u, hu, heq⟩
    exact (Subtype.ext heq : u = z) ▸ hu

def overlapEquiv (i : ι) (V : Opens (wN i).ambient) :
    CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (overlapOpen w j hj i V) :=
  (MaxLocusLocal.nestedDiffeo (wN i).ambient V (coordinateImage w j hj i V)
    (coordinateImage_dictionary w j hj i V) (coordinateImage_subset w j hj i V)).trans
    (MaxLocusLocal.nestedOpensDiffeo (coordinateImage_old_subset w j hj i V)).symm

private theorem overlap_carrier (i : ι) (V : Opens (wN i).ambient) (p : V) :
    (overlapEquiv w j hj i V p).val ∈ (w i).carrier ↔ p.val ∈ (wN i).carrier := Iff.rfl

private theorem overlap_point (i : ι) (V : Opens (wN i).ambient) (p : V)
    (hp : p.val ∈ (wN i).carrier) :
    (w i).toLocalEmbedding.toPoint ⟨(overlapEquiv w j hj i V p).val, hp⟩ =
      j.hom.left.base ((wN i).toLocalEmbedding.toPoint ⟨p.val, hp⟩) := by
  have h := congrArg (fun f => f.hom.left.base (⟨p.val, hp⟩ : (wN i).carrier))
    (OriginalNativeHSBaseOpenWindows.base_square w j hj i)
  exact ((w i).toLocalEmbedding.restrict_toPoint _
    (OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset (w i).toLocalEmbedding j hj)
    ⟨p.val, hp⟩).symm.trans h.symm

private def conjugate {n : ℕ} {A B A' B' : CMfd.{0} n}
    (eA : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (eB : B' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B)
    (Φ : B' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A') :
    B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A := eB.symm.trans (Φ.trans eA)

def oldOverlap (a b : ι) (U : Opens (wN a).ambient) (U' : Opens (wN b).ambient)
  (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U) : CMfd.of (n := n) (overlapOpen w j hj b U') ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
    CMfd.of (n := n) (overlapOpen w j hj a U) :=
  @conjugate n (CMfd.of (n := n) (overlapOpen w j hj a U))
    (CMfd.of (n := n) (overlapOpen w j hj b U')) (CMfd.of (n := n) U) (CMfd.of (n := n) U')
    (overlapEquiv w j hj a U) (overlapEquiv w j hj b U') Φ

include hj in
theorem old_admissible (a b : ι) (U : Opens (wN a).ambient) (U' : Opens (wN b).ambient)
  (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U) (hΦ : mapAdm wN a b U U' Φ) :
    mapAdm w a b (overlapOpen w j hj a U) (overlapOpen w j hj b U') (oldOverlap w j hj a b U U' Φ) := by
  constructor
  · intro p
    let z := (overlapEquiv w j hj b U').symm p
    have hz := overlap_carrier w j hj b U' z
    have heq := (overlapEquiv w j hj b U').apply_symm_apply p
    exact (overlap_carrier w j hj a U (Φ z)).trans ((hΦ.1 z).trans (by
      exact hz.symm.trans (by rw [heq])))
  · intro p hp hq
    let z := (overlapEquiv w j hj b U').symm p
    have heq := (overlapEquiv w j hj b U').apply_symm_apply p
    have hz : z.val ∈ (wN b).carrier := (overlap_carrier w j hj b U' z).mp (by
      change ((overlapEquiv w j hj b U') ((overlapEquiv w j hj b U').symm p)).val ∈ (w b).carrier
      exact congrArg Subtype.val heq |>.symm ▸ hp)
    have hq' : (Φ z).val ∈ (wN a).carrier := (hΦ.1 z).mpr hz
    have hBase := congrArg j.hom.left.base (hΦ.2 z hz hq')
    have hLeft := overlap_point w j hj a U (Φ z) hq'
    have hRight := overlap_point w j hj b U' z hz
    have hLast : (⟨(overlapEquiv w j hj b U' z).val,
        (overlap_carrier w j hj b U' z).mpr hz⟩ : (w b).carrier) = ⟨p.val, hp⟩ :=
      Subtype.ext (congrArg (Subtype.val : overlapOpen w j hj b U' → (w b).ambient) heq)
    exact hLeft.trans (hBase.trans (hRight.symm.trans (congrArg (w b).toLocalEmbedding.toPoint hLast)))

private theorem restrict_equal_opens {n : ℕ} {A Y : CMfd.{0} n} (V W : Opens A)
    (hVW : V = W) (T : BlowupTower A Y) :
    ∃ φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) W,
      (∀ z, (φ z).val = z.val) ∧
      ∃ χ, IsTowerIso φ (restrict V T) (restrict W T) χ := by
  subst W
  exact ⟨Diffeomorph.refl _ _ ∞, fun _ => rfl, _, IsTowerIso.refl_self (restrict V T)⟩

theorem overlap_history (i : ι) {Y : CMfd.{0} n} (T : BlowupTower (Amb w i) Y)
    (V : Opens (wN i).ambient) :
    ∃ χ, IsTowerIso (overlapEquiv w j hj i V)
      (restrict V (OriginalNativeHSBaseOpenWindows.history w j hj i T).tower)
      (restrict (overlapOpen w j hj i V) T) χ := by
  let O := OriginalNativeHSBaseOpenWindows.traceOpen w j hj i
  let W := overlapOpen w j hj i V
  let φ := OriginalNativeHSBaseOpenWindows.baseEquiv w j hj i
  let L := MaxLocusLocal.nestedOpens O W
  have hWO : W ≤ O := overlap_subset w j hj i V
  have hPre : OriginalNativeHSTowerIsoRestriction.basePreimage φ L = V := by
    ext z
    change (φ z).val.val ∈ coordinateImage w j hj i V ↔ z ∈ V
    change z.val ∈ coordinateImage w j hj i V ↔ z ∈ V
    exact (coordinateImage_dictionary w j hj i V z).symm
  obtain ⟨ψ, hψ, χ₀, h₀⟩ := restrict_equal_opens V _ hPre.symm
    (OriginalNativeHSBaseOpenWindows.history w j hj i T).tower
  have h₁ := OriginalNativeHSTowerIsoRestriction.isTowerIso L
    (OriginalNativeHSBaseOpenWindows.history_isTowerIso w j hj i T)
  have h₂ := MaxLocusLocal.isTowerIso_restrict_nestedOpens hWO T
  have hAll := h₀.trans (h₁.trans h₂)
  refine ⟨_, BlowupTowerSplitIso.IsTowerIso.congr_base hAll ?_⟩
  intro z
  apply Subtype.ext
  apply Subtype.ext
  exact (congrArg Subtype.val (hψ z)).symm

/-- Restrict and physically transport EVERY old stage tower; compatibility is derived. -/
def stage {H : ℕ → ℕ} (raw : ∀ i, MarkedIdeal n (Amb w i))
    (hRaw : ∀ i, HironakaG11PresReduction.IsNativeWindowRecord (w i) (raw i) H)
    (e : ι → ℕ) (he : ∀ i, 1 ≤ e i) {Λ : Type*} [LinearOrder Λ]
    (R : ResolutionInvariant.{0} n n Λ) {m : ℕ}
    (s : GStage R (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)) (mapAdm w) m) :
    GStage R (OriginalNativeHSBaseOpenWindows.record w j hj raw e) (mapAdm wN) m where
  T i := ⟨(OriginalNativeHSBaseOpenWindows.history w j hj i (s.T i).2).target,
    (OriginalNativeHSBaseOpenWindows.history w j hj i (s.T i).2).tower⟩
  length i := (OriginalNativeHSBaseOpenWindows.history_length w j hj i (s.T i).2).trans (s.length i)
  canonical i := OriginalNativeHSBaseOpenWindows.history_canonical w j hj raw hRaw e he R i
    (s.T i).2 (s.canonical i)
  compatible := by
    intro a b U U' Φ hΦ
    obtain ⟨χ, hχ⟩ := s.compatible a b (overlapOpen w j hj a U) (overlapOpen w j hj b U')
      (oldOverlap w j hj a b U U' Φ) (old_admissible w j hj a b U U' Φ hΦ)
    obtain ⟨χb, hb⟩ := overlap_history w j hj b (s.T b).2 U'
    obtain ⟨χa, ha⟩ := overlap_history w j hj a (s.T a).2 U
    have hAll := (hb.trans hχ).trans ha.symm
    refine ⟨_, BlowupTowerSplitIso.IsTowerIso.congr_base hAll ?_⟩
    intro z
    change Φ z = (overlapEquiv w j hj a U).symm
      ((overlapEquiv w j hj a U) (Φ ((overlapEquiv w j hj b U').symm (overlapEquiv w j hj b U' z))))
    exact ((overlapEquiv w j hj a U).symm_apply_apply _).symm.trans
      (congrArg (fun p => (overlapEquiv w j hj a U).symm ((overlapEquiv w j hj a U) (Φ p)))
        ((overlapEquiv w j hj b U').symm_apply_apply z).symm)

variable {H : ℕ → ℕ} (raw : ∀ i, MarkedIdeal n (Amb w i))
    (hRaw : ∀ i, HironakaG11PresReduction.IsNativeWindowRecord (w i) (raw i) H)
    (e : ι → ℕ) (he : ∀ i, 1 ≤ e i) {Λ : Type*} [LinearOrder Λ]
    (R : ResolutionInvariant.{0} n n Λ) {m : ℕ}
    (s : GStage R (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)) (mapAdm w) m)

theorem stage_length (i : ι) : ((stage w j hj raw hRaw e he R s).T i).2.length = m :=
  (stage w j hj raw hRaw e he R s).length i

theorem stage_canonical (i : ι) : IsCanonical (OriginalNativeHSBaseOpenWindows.record w j hj raw e i)
    (R.inv (OriginalNativeHSBaseOpenWindows.record w j hj raw e i)) ((stage w j hj raw hRaw e he R s).T i).2 :=
  (stage w j hj raw hRaw e he R s).canonical i

theorem stage_compatible : AdmCompatible (mapAdm wN) (stage w j hj raw hRaw e he R s).T :=
  (stage w j hj raw hRaw e he R s).compatible

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenStage
