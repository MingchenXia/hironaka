import Hironaka.Resolution.HironakaActualProcessedMaskFiniteBlock
import Hironaka.Resolution.HironakaG4ZeroMaskSameGammaHistory
import Hironaka.Resolution.HironakaG34MaskFoldEquivariance
import Hironaka.Invariant.ResolutionInvariantDriver

/-!
# Naturality of the processed mask sums; the equivariant K3 blocks (tenth brick of EQ_d)

Lane G34 (run 0080, round 10).  Blueprint: `hironaka-g34-resume-processed-mask-equivariance.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §1 (rows "K3 masks", "K3 zero mask"), §2(c)(iii).

The two primitive blocks of K3 (the processed-row cleanup of the sharp driver) are canonical towers of mark-one finite
SUMS of canonical old factors: the processed mask block
(`HironakaActualProcessedMaskFiniteBlock.exists_actual_processed_mask_finite_block`, a canonical `invFamily` tower of
`processedMaskMarked W E T P`) and the zero-mask Gamma history
(`HironakaG4ZeroMaskSameGammaHistory.exists_prepared_zero_mask_same_gamma_history`, a canonical segment of the monomial
invariant `towerInvAlong` of `⟨N, born, Σ_{i ∈ P} D_i, 1⟩`).  This module shows that these sums are NATURAL under open
holomorphic embeddings (index-free: the pullback is computed from the preimages of the carrier, of the members whose
factors are summed and of the born members), and deduces the equivariance of both blocks.

## Main results

* `maskSum`, **`pullback_maskSum`**: the ideal spanned by finitely many ideals pulls back to the ideal spanned by the
  pullbacks (any holomorphic map; members holomorphic);
* `maskSumMarked N H born P` (the mark-one sum of the canonical factors `factorOf N (H i) born`, `i ∈ P`);
  **`pullback_maskSumMarked`**, `pullback_maskSumMarked_eq_of_preimage_eq`, **`pullback_restrict_maskSumMarked`**;
* `processedMaskMarked_eq` (the processed mask marked ideal is such a sum, by definition);
* **`exists_actual_processed_mask_finite_block_equivariant`**: the held processed mask block, plus: an equivariant prefix
  stays equivariant;
* **`isEquivariant_zero_mask_segment`**, **`isEquivariant_zero_mask_history`**: the zero-mask Gamma history (a canonical
  segment of `towerInvAlong` of the sum) is equivariant for `(N, old ++ born)`.

New file; no existing statement changed; no named input.  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG34ProcessedMaskEquivariance

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerIsomorphism Hironaka.MarkedIdealBiholomorphism
  Hironaka.MonomialPartAlong Hironaka.RestrictedIdealExtension
  Hironaka.RelativePrincipalizationSpan Hironaka.InvertibleIdealQuotient
  Hironaka.NormalCrossings Hironaka.NormalCrossingsComparison
  Hironaka.HironakaG4PreparedCentreCoordinates Hironaka.DivisorExponentAlong
  Hironaka.HironakaSharpActualFiniteChronologicalHistory
  Hironaka.HironakaSharpOriginalProductTraceOrder
  Hironaka.HironakaSharpOriginalMultiBoundaryBadLocus
  Hironaka.HironakaG4MonomialFamilyInvariant
  Hironaka.HironakaG4CompactWholeMonomialMaskPhase
  Hironaka.HironakaActualProcessedMaskControlledSum
  Hironaka.HironakaActualProcessedMaskFiniteBlock
  Hironaka.HironakaG34CanonicalLocalEquivariance
  Hironaka.HironakaG34JointMaskEquivariance
  Hironaka.HironakaG34MaskFoldEquivariance
open Hironaka.HomogenizedGlueingTower (strictAlong)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Finite span sums of ideals -/

section Sum

variable {X Y : CMfd.{u} n}

/-- **The ideal spanned by the ideals `D i`, `i ∈ P`.** -/
def maskSum {ι : Type*} (D : ι → GermIdeal n X) (P : Finset ι) : GermIdeal n X :=
  ⟨fun x g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P, (D i).mem x f) x g⟩

/-- **The span of finitely many ideals pulls back to the span of the pullbacks** (any holomorphic map; the members of the
`D i` holomorphic). -/
theorem pullback_maskSum {f : Y → X} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {ι : Type*} (D : ι → GermIdeal n X) (hhol : ∀ i x g, (D i).mem x g → HolomorphicAt n g x) (P : Finset ι) :
    GermIdeal.pullback (m := n) f (maskSum D P) = maskSum (fun i => GermIdeal.pullback (m := n) f (D i)) P := by
  have hfat : ∀ y : Y, ∀ᶠ y' in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f y' :=
    fun _ => Eventually.of_forall fun _ => hf.contMDiffAt
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · change IsInSpanAt (n := n) (fun f' => ∃ i ∈ P, (GermIdeal.pullback (m := n) f (D i)).mem y f') y g
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro s ⟨a, ha, rfl⟩
    have hc := GermIdealPullbackCalculus.isInSpanAt_comp hf (y := y)
      (show IsInSpanAt (n := n) (fun f' => ∃ i ∈ P, (D i).mem (f y) f') (f y) a from ha)
    refine IsInSpanAt.mono ?_ hc
    rintro t ⟨b, ⟨i, hi, hb⟩, rfl⟩
    exact ⟨i, hi, GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨b, hb, rfl⟩ ((hhol i _ _ hb).comp_contMDiff (hfat y)))⟩
  · change IsInSpanAt (n := n) (fun f' => ∃ i ∈ P, (GermIdeal.pullback (m := n) f (D i)).mem y f') y g at hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ hg)
    rintro s ⟨i, hi, hs⟩
    refine IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hs)
    rintro t ⟨a, ha, rfl⟩
    exact ⟨a, isInSpanAt_self (S := fun f' => ∃ j ∈ P, (D j).mem (f y) f') ⟨i, hi, ha⟩ (hhol i _ _ ha), rfl⟩

end Sum

/-! ### Mark-one sums of canonical old factors -/

section Marked

variable {X Y : CMfd.{u} n}

/-- **The mark-one sum of the canonical factors** `factorOf N (H i) born` (monomial part along `born` of the trace of `H i`
on `N`), `i ∈ P`. -/
def maskSumMarked {ι : Type*} (N : Set X) (H : ι → Set X) (born : List (Set X)) (P : Finset ι) : MarkedIdeal n X :=
  ⟨N, born, maskSum (fun i => (factorOf N (H i) born).ideal) P, 1⟩

/-- A member of a simple-normal-crossings list has a coherent vanishing ideal. -/
theorem isCoherent_vanishingIdeal_of_mem (hn : 0 < n) {L : List (Set X)} (hL : IsSNCDivisor n L) {H : Set X}
    (hH : H ∈ L) : (vanishingIdeal (n := n) H).IsCoherent := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
  exact VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hL i)

/-- **The mark-one sum of canonical factors pulls back** along an open holomorphic embedding, with the preimages of the
carrier, of the summed members and of the born members. -/
theorem pullback_maskSumMarked {ι : Type*} {N : Set X} {H : ι → Set X} {born : List (Set X)} {f : Y → X}
    (hf : HironakaBaseChange.IsOpenHoloEmbedding n f) (hN : IsClosedSubmanifold n N)
    (hH : ∀ i, (vanishingIdeal (n := n) (H i)).IsCoherent) (P : Finset ι) :
    MarkedIdeal.pullback f (maskSumMarked N H born P) =
      maskSumMarked (f ⁻¹' N) (fun i => f ⁻¹' H i) (born.map (f ⁻¹' ·)) P := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) f (maskSum (fun i => (factorOf N (H i) born).ideal) P) =
    maskSum (fun i => (factorOf (f ⁻¹' N) (f ⁻¹' H i) (born.map (f ⁻¹' ·)) : MarkedIdeal n Y).ideal) P
  rw [pullback_maskSum (contMDiff_of_isOpenHoloEmbedding hf) (fun i => (factorOf N (H i) born).ideal)
    (fun _ _ _ hg => hg.1) P]
  congr 1
  funext i
  exact congrArg MarkedIdeal.ideal (pullback_factorOf hf born hN (hH i))

/-- **Two open holomorphic embeddings with the same preimages of the data pull a mark-one sum of canonical factors back to
the same marked ideal.** -/
theorem pullback_maskSumMarked_eq_of_preimage_eq {ι : Type*} {N : Set X} {H : ι → Set X} {born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hH : ∀ i, (vanishingIdeal (n := n) (H i)).IsCoherent) (P : Finset ι)
    {f₁ f₂ : Y → X} (hf₁ : HironakaBaseChange.IsOpenHoloEmbedding n f₁)
    (hf₂ : HironakaBaseChange.IsOpenHoloEmbedding n f₂) (hNN : f₁ ⁻¹' N = f₂ ⁻¹' N)
    (hHH : ∀ i, f₁ ⁻¹' H i = f₂ ⁻¹' H i) (hBB : ∀ B ∈ born, f₁ ⁻¹' B = f₂ ⁻¹' B) :
    MarkedIdeal.pullback f₁ (maskSumMarked N H born P) = MarkedIdeal.pullback f₂ (maskSumMarked N H born P) := by
  rw [pullback_maskSumMarked hf₁ hN hH P, pullback_maskSumMarked hf₂ hN hH P]
  have hborn : born.map (f₁ ⁻¹' ·) = born.map (f₂ ⁻¹' ·) := List.map_congr_left fun B hB => hBB B hB
  have hH' : (fun i => f₁ ⁻¹' H i) = (fun i => f₂ ⁻¹' H i) := funext hHH
  rw [hNN, hborn, hH']

/-- **The processed mask marked ideal is a mark-one sum of canonical factors** (by definition): carrier and born list of
the transform of `(W, [])` along `T`, summed members the strict transforms of the original members `E.get i`. -/
theorem processedMaskMarked_eq (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) (P : Finset (Fin E.length)) :
    processedMaskMarked W E T P = maskSumMarked (geoTransformAlong (geometricTemplate W []) T).N
      (fun i => strictAlong T (E.get i)) (geoTransformAlong (geometricTemplate W []) T).E P := rfl

end Marked

/-! ### Opens -/

section Opens

variable {X : CMfd.{u} n} {V V' : Opens X}
  (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')

/-- **Naturality of a mark-one sum of canonical factors** under a biholomorphism of opens preserving the carrier, every
summed member and every born member: `φ^*(M|_{V'}) = M|_V`. -/
theorem pullback_restrict_maskSumMarked {ι : Type*} {N : Set X} {H : ι → Set X} {born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hH : ∀ i, (vanishingIdeal (n := n) (H i)).IsCoherent) (P : Finset ι)
    (hc : (maskSumMarked N H born P).ideal.IsCoherent)
    (hφN : ∀ p : V, ((φ p : V') : X) ∈ N ↔ (p : X) ∈ N)
    (hφH : ∀ i, ∀ p : V, ((φ p : V') : X) ∈ H i ↔ (p : X) ∈ H i)
    (hφB : ∀ B ∈ born, ∀ p : V, ((φ p : V') : X) ∈ B ↔ (p : X) ∈ B) :
    MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V' → X) (maskSumMarked N H born P)) =
      MarkedIdeal.pullback (Subtype.val : V → X) (maskSumMarked N H born P) := by
  rw [StepOneTangentChange.pullback_pullback_of_comp hc contMDiff_subtype_val φ.contMDiff (fun _ => rfl)]
  have hf₁ : HironakaBaseChange.IsOpenHoloEmbedding n (fun p : V => ((φ p : V') : X)) := ⟨V', φ, fun _ => rfl⟩
  exact pullback_maskSumMarked_eq_of_preimage_eq hN hH P hf₁ (HironakaBaseChange.isOpenHoloEmbedding_val V)
    (Set.ext fun p => hφN p) (fun i => Set.ext fun p => hφH i p) (fun B hB => Set.ext fun p => hφB B hB p)

end Opens

/-! ### The processed mask block -/

section Processed

variable {X Y : CMfd.{u} n}

/-- **The processed mask marked ideal is natural along an equivariant prefix**: if `φ : U ≅ U'` preserves `W` and every
member of `E`, and `T` (multiple test blow-up of `(W, [])` and `(X, E)`) has `T|_U ≅ T|_{U'}` over `φ` with last-stage map
`χ`, then `χ` carries `processedMaskMarked W E T P` restricted to `T⁻¹U'` to its restriction to `T⁻¹U` (domain of the
canonical invariant assumed). -/
theorem pullback_restrict_processedMaskMarked (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) (P : Finset (Fin E.length))
    (hDom : IsInvDomain (n + 1) (processedMaskMarked W E T P)) {U U' : Opens X}
    (φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U')
    (hφW : ∀ p : U, ((φ p : U') : X) ∈ W ↔ (p : X) ∈ W)
    (hφE : ∀ H ∈ E, ∀ p : U, ((φ p : U') : X) ∈ H ↔ (p : X) ∈ H)
    {χ : CMfd.of (n := n) (openPreimage T U) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U')} (hχ : IsTowerIso φ (restrict U T) (restrict U' T) χ) :
    MarkedIdeal.pullback χ (MarkedIdeal.pullback (Subtype.val : openPreimage T U' → Y) (processedMaskMarked W E T P)) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (processedMaskMarked W E T P) := by
  have hFull' : IsGeoTestTower (geometricTemplate (univ : Set X) (E ++ [])) T := by
    rw [List.append_nil]
    exact hFull
  obtain ⟨hcN, hcH⟩ := HironakaG34MaskStepEquivariance.current_data_preserved φ (old := E) (born := []) hW hφW
    (fun H hH p => hφE H (by rwa [List.append_nil] at hH) p) T hT hFull' hχ
  have hRec := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hmem : ∀ i : Fin E.length, strictAlong T (E.get i) ∈
      E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E :=
    fun i => List.mem_append_left _ (List.mem_map_of_mem (List.get_mem E i))
  have hc : (processedMaskMarked W E T P).ideal.IsCoherent := hDom.isWellFormed.isCoherent
  rw [processedMaskMarked_eq] at hc ⊢
  exact pullback_restrict_maskSumMarked χ hRec.1 (fun i => isCoherent_vanishingIdeal_of_mem hn hRec.2.1 (hmem i)) P hc
    hcN (fun i p => hcH _ (hmem i) p) (fun B hB p => hcH B (List.mem_append_right _ hB) p)

/-- **The processed mask block, equivariant**: the conclusions of
`HironakaActualProcessedMaskFiniteBlock.exists_actual_processed_mask_finite_block`, plus: an equivariant prefix stays
equivariant (`IsEquivariant W E T → IsEquivariant W E (T.append R)`). -/
theorem exists_actual_processed_mask_finite_block_equivariant
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1)
    (hNC : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (hPrepared : let A := geoTransformAlong (geometricTemplate W []) T
      ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x)
    (P : Finset (Fin E.length)) (hP : 2 ≤ P.card)
    (hBound : let A := geoTransformAlong (geometricTemplate W []) T
      let D := fun i : Fin E.length => monomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
      ∀ x ∈ A.N,tauD (fun i j => divExpAlong n A.N (D i) (A.E.get j) x) ≤ P.card) :
    let M := processedMaskMarked W E T P
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      ResolutionInvariantSpec.IsCanonical M ((CanonicalCentres.invFamily hn (n+1)).inv M) R ∧
      IsGeoResolution M R ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let U := T.append Q
        let A := geoTransformAlong (geometricTemplate W []) U
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        RestrictEmptyTower.CentresOver
          (originalSharpBadLocus (n := n) W E) U ∧
        geoTransformAlong M Q=processedMaskMarked W E U P ∧
        (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal x ≤ 1) ∧
        (∀ i : Fin E.length,HasNormalCrossings n (residualSupport W E U i)
          ((E.map (strictAlong U)).eraseIdx i.val ++ A.E)) ∧
        (∀ i : Fin E.length,residualSupport W E U i ⊆ closure (residualSupport W E U i \
          ⋃ H ∈ (E.map (strictAlong U)).eraseIdx i.val ++ A.E,H)) ∧
        (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong U)) A.E x) ∧
        (∀ x ∈ A.N,tauD (factorMatrix W E U x) ≤ P.card) ∧
        (∀ i : Fin E.length,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal=
            vanishingIdeal (n := n) (Q.proj ⁻¹' residualSupport W E T i) ∧
          residualSupport W E U i=Q.proj ⁻¹' residualSupport W E T i) ∧
        (∀ S : Finset (Fin E.length),S.Nonempty →
          IsCompact (processedMaskMarked W E U S).cosupp) ∧
        ∀ z ∈ A.N,properRows (factorMatrix W E U z) ⊆
          properRows (factorMatrix W E T (Q.proj z))) ∧
      (∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        ¬P ⊆ properRows (factorMatrix W E (T.append R) z)) ∧
      (IsEquivariant W E T → IsEquivariant W E (T.append R)) := by
  obtain ⟨Z, R, hCan, hRes, hk, hEnd⟩ := exists_actual_processed_mask_finite_block hn hW hE hdense T hT hFull hSharp hK
    hOrd hNC hDenseS hPrepared P hP hBound
  refine ⟨Z, R, hCan, hRes, hk, hEnd, ?_⟩
  intro hEqT U U' φ hφW hφE
  obtain ⟨χ, hχ⟩ := hEqT U U' φ hφW hφE
  have hDom := (actual_processed_mask_controlled_record (Z := Y) hn hW hE hdense
    T hT hFull hOrd hNC hDenseS P hP hBound).1
  exact exists_isTowerIso_restrict_append_of_isCanonical φ (CanonicalCentres.invFamily hn (n + 1)) T hχ hDom
    (pullback_restrict_processedMaskMarked hn hW hE hdense T hT hFull P hDom φ hφW hφE hχ) R hCan

end Processed

/-! ### The zero-mask Gamma history -/

section ZeroMask

variable {X Y : CMfd.{u} n}

/-- **A canonical segment of the monomial invariant of a mark-one sum of canonical old factors is equivariant** for
`(N, old ++ born)` (from the empty prefix): every biholomorphism of opens preserving `N` and every member of `old ++ born`
carries the sum to itself (`pullback_restrict_maskSumMarked`), so the segment restricts to isomorphic towers
(`exists_isTowerIso_restrict_of_towerInvAlong`). -/
theorem isEquivariant_zero_mask_segment (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born)) (P : Finset (Fin old.length))
    (hc : (maskSumMarked N old.get born P : MarkedIdeal n X).ideal.IsCoherent)
    (T : BlowupTower X Y)
    (hT : ResolutionDriver.IsCanonicalSegment (maskSumMarked N old.get born P : MarkedIdeal n X)
      (fun {Y} Q => MonomialStepAlong.towerInvAlong (maskSumMarked N old.get born P : MarkedIdeal n X) (Y := Y) Q) T)
    (hTt : IsGeoTestTower (maskSumMarked N old.get born P : MarkedIdeal n X) T) :
    IsEquivariant N (old ++ born) T := by
  intro U U' φ hφN hφH
  have hold : ∀ i, (vanishingIdeal (n := n) (old.get i)).IsCoherent :=
    fun i => isCoherent_vanishingIdeal_of_mem hn hE (List.mem_append_left _ (List.get_mem old i))
  have hnat := pullback_restrict_maskSumMarked φ hN hold P hc hφN
    (fun i p => hφH _ (List.mem_append_left _ (List.get_mem old i)) p)
    (fun B hB p => hφH B (List.mem_append_right _ hB) p)
  exact exists_isTowerIso_restrict_of_towerInvAlong hN hc φ hnat T
    (ResolutionInvariantDriver.isCanonical_of_isCanonicalSegment _ T hT) hTt

/-- **The zero-mask Gamma history, equivariant**: the canonical segment and the resolution of
`HironakaG4ZeroResidualMonomialSum.actual_zero_residual_mask_sum_monomial` (the source of the tower of
`HironakaG4ZeroMaskSameGammaHistory.exists_prepared_zero_mask_same_gamma_history`), together with
`IsEquivariant N (old ++ born)` of the segment. -/
theorem isEquivariant_zero_mask_history (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) (P : Finset (Fin old.length)) (hP : P.Nonempty)
    (hTau : ∀ x ∈ N, tauD (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) ≤ P.card)
    (hNu : ∀ x ∈ N, tauD (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) = P.card →
      nuOne (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) = 0)
    (hK : IsCompact (maskSumMarked N old.get born P : MarkedIdeal n X).cosupp)
    (T : BlowupTower X Y)
    (hT : ResolutionDriver.IsCanonicalSegment (maskSumMarked N old.get born P : MarkedIdeal n X)
      (fun {Y} Q => MonomialStepAlong.towerInvAlong (maskSumMarked N old.get born P : MarkedIdeal n X) (Y := Y) Q) T)
    (hTt : IsGeoTestTower (maskSumMarked N old.get born P : MarkedIdeal n X) T) :
    IsEquivariant N (old ++ born) T := by
  have hc := (HironakaG4ZeroResidualMonomialSum.actual_zero_residual_mask_sum_monomial hn hN hE hTr hdense P hP
    hTau hNu hK).1
  exact isEquivariant_zero_mask_segment hn hN hE P hc T hT hTt

end ZeroMask

end

end Hironaka.HironakaG34ProcessedMaskEquivariance
