import Hironaka.Resolution.HironakaG34CanonicalLocalEquivariance
import Hironaka.Resolution.HironakaActualRetainedBoundaryMaskBlock
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal
import Hironaka.Invariant.StepOneTangentChange

/-!
# Equivariance of the joint mask block (second brick of EQ_d)

Lane G34 (run 0080, round 8).  Blueprint: `hironaka-g34-resume-joint-mask-equivariance.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §2(c)(i).

The innermost block of the carrier phase of the dimension-`d` driver is a canonical `invFamily` resolution of the joint
profile marked ideal `jointProfileMarked N old born q P` (`HironakaActualRetainedBoundaryMaskBlock`, its first conclusion).
This module shows that this marked ideal is NATURAL under open holomorphic embeddings, in an index-free form (its pullback
is computed from the preimages of `N` and of the members only), so that two embeddings with the same preimages of `N` and of
every member pull it back to the same marked ideal.  With `HironakaG34CanonicalLocalEquivariance` this gives the
equivariance of every canonical tower of the joint profile marked ideal under every biholomorphism `φ : V ≅ V'` of opens which
preserves `N` and every member of `old ++ born`.

## Main results

* `pullback_restrictOn_of_local`, `pullback_relativeIdealListProduct_of_local`: restriction to `N` and relative products
  commute with pullbacks along local biholomorphisms;
* `pullback_finiteSum`: finite marked sums commute with pullbacks along holomorphic maps (coherent ideals);
* `factorOf`: the canonical old factor of ONE member (`canonicalFactorMarked N old born i = factorOf N (old.get i) born`);
* `pullback_factorOf`, `pullback_canonicalProductMarked`, **`pullback_jointProfileMarked`**: the index-free pullback formulas
  along an open holomorphic embedding;
* **`pullback_jointProfileMarked_eq_of_preimage_eq`**: two open holomorphic embeddings with the same preimages of `N` and of
  every member pull the joint profile marked ideal back to the same marked ideal;
* **`pullback_restrict_jointProfileMarked`**: for `φ : V ≅ V'` preserving `N` and every member,
  `φ^*(J|_{V'}) = J|_V`;
* **`exists_isTowerIso_restrict_joint_mask_block`**: every canonical tower of `invFamily` for the joint profile marked
  ideal (in particular the block of `exists_actual_retained_boundary_joint_mask_block`) has `R|_V ≅ R|_{V'}` over `φ`.

New file; no existing statement changed; no named input.  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG34JointMaskEquivariance

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerIsomorphism Hironaka.MarkedIdealBiholomorphism
  Hironaka.MonomialPartAlong Hironaka.RestrictedIdealExtension
  Hironaka.RelativePrincipalizationSpan Hironaka.DerivativeIdealAlongEtale
  Hironaka.HironakaG4PreparedCentreCoordinates
  Hironaka.HironakaActualRetainedBoundaryJointStep
  Hironaka.HironakaActualFiniteMarkedSumHistories
  Hironaka.HironakaG34CanonicalLocalEquivariance
  Hironaka.HironakaSharpActualFiniteMemberProduct Hironaka.IdealWeightPowers
  Hironaka.NormalCrossings Hironaka.NormalCrossingsComparison
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Local biholomorphisms and open holomorphic embeddings -/

section Local

variable {M M' : CMfd.{u} n}

/-- An open holomorphic embedding has a local inverse at every point. -/
theorem exists_isLocalInverseAt_of_isOpenHoloEmbedding {f : M' → M}
    (hf : HironakaBaseChange.IsOpenHoloEmbedding n f) (z : M') : ∃ ψ : M → M', IsLocalInverseAt n f ψ z := by
  obtain ⟨U, e, he⟩ := hf
  have hfe : f = (Subtype.val : U → M) ∘ e := funext he
  subst hfe
  let ψ := e.symm ∘ openInv U (e z)
  have hInv := isLocalInverseAt_val (n := n) U (e z)
  refine ⟨ψ, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact Eventually.of_forall fun w =>
      ((contMDiff_subtype_val.comp e.contMDiff) w).mdifferentiableAt (by simp)
  · filter_upwards [hInv.mdiff_inv] with x hx
    exact ((e.symm.contMDiff _).mdifferentiableAt (by simp)).comp x hx
  · filter_upwards [e.contMDiff.continuous.continuousAt.eventually hInv.left_inv] with w hw
    change e.symm (openInv U (e z) ((e w).val)) = w
    rw [hw, e.symm_apply_apply]
  · filter_upwards [hInv.right_inv] with x hx
    change (e (e.symm (openInv U (e z) x))).val = x
    rw [e.apply_symm_apply]
    exact hx

/-- An open holomorphic embedding is holomorphic. -/
theorem contMDiff_of_isOpenHoloEmbedding {f : M' → M} (hf : HironakaBaseChange.IsOpenHoloEmbedding n f) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f := by
  obtain ⟨U, e, he⟩ := hf
  have hfe : f = (Subtype.val : U → M) ∘ e := funext he
  rw [hfe]
  exact contMDiff_subtype_val.comp e.contMDiff

variable {f : M' → M} (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n f ψ y)

include hloc in
/-- **Restriction to `W` commutes with pullbacks along local biholomorphisms** (coherent ideal, `W` a closed
submanifold). -/
theorem pullback_restrictOn_of_local {W : Set M} (hW : IsClosedSubmanifold n W) {𝔟 : GermIdeal n M}
    (h𝔟 : 𝔟.IsCoherent) :
    GermIdeal.pullback (m := n) f (restrictOn n W 𝔟) =
      restrictOn n (f ⁻¹' W) (GermIdeal.pullback (m := n) f 𝔟) := by
  have hr := isCoherent_restrictOn h𝔟 (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)
  refine GermIdeal.ext (funext fun y => funext fun F => propext ?_)
  obtain ⟨ψ, hψ⟩ := hloc y
  exact (MonomialPartEtale.mem_pullback_iff_of_local hr hψ).trans
    (MonomialPartEtale.mem_restrictOn_pullback_iff_of_local h𝔟 hψ).symm

theorem relative_product_coherent {N : Set M} (hN : IsClosedSubmanifold n N)
    (L : List (GermIdeal n M)) (hc : ∀ I ∈ L, I.IsCoherent) :
    (relativeIdealListProduct N L).IsCoherent := by
  induction L with
  | nil => exact isCoherent_unitIdeal
  | cons I L ih =>
    exact isCoherent_restrictOn (IdealWeightPowers.isCoherent_mul (hc I (by simp))
      (ih (fun J hJ => hc J (List.mem_cons_of_mem I hJ))))
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)

include hloc in
/-- **Relative products commute with pullbacks along local biholomorphisms.** -/
theorem pullback_relativeIdealListProduct_of_local
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {N : Set M} (hN : IsClosedSubmanifold n N)
    (L : List (GermIdeal n M)) (hc : ∀ I ∈ L, I.IsCoherent) :
    GermIdeal.pullback (m := n) f (relativeIdealListProduct N L) =
      relativeIdealListProduct (f ⁻¹' N) (L.map fun I => GermIdeal.pullback (m := n) f I) := by
  induction L with
  | nil => exact BlowupExceptionalDivisor.pullback_unitIdeal
  | cons I L ih =>
    have hI := hc I (by simp)
    have hL := fun J hJ => hc J (List.mem_cons_of_mem I hJ)
    have hP := relative_product_coherent hN L hL
    change GermIdeal.pullback (m := n) f (restrictOn n N (I.mul (relativeIdealListProduct N L))) =
      restrictOn n (f ⁻¹' N) ((GermIdeal.pullback (m := n) f I).mul
        (relativeIdealListProduct (f ⁻¹' N) (L.map fun J => GermIdeal.pullback (m := n) f J)))
    rw [pullback_restrictOn_of_local hloc hN (IdealWeightPowers.isCoherent_mul hI hP),
      GermIdealTotalTransform.pullback_mul hf hI hP, ih hL]

end Local

/-! ### Finite marked sums -/

section Sum

variable {X Y : CMfd.{u} n}

/-- Finite marked sums of coherent ideals are coherent. -/
theorem isCoherent_finiteSum : ∀ (A : MarkedIdeal n X) (L : List (MarkedIdeal n X)), A.ideal.IsCoherent →
    (∀ B ∈ L, B.ideal.IsCoherent) → (finiteSum A L).ideal.IsCoherent
  | _, [], hA, _ => hA
  | A, B :: L, hA, hL => by
      have hS := isCoherent_finiteSum B L (hL B (by simp)) fun C hC => hL C (List.mem_cons_of_mem B hC)
      change (sumIdeal (idealPow A.ideal (finiteSum B L).d) (idealPow (finiteSum B L).ideal A.d)).IsCoherent
      exact isCoherent_sumIdeal (GermIdealPullbackCalculus.isCoherent_idealPow hA _)
        (GermIdealPullbackCalculus.isCoherent_idealPow hS _)

/-- **Finite marked sums commute with pullbacks** along holomorphic maps (coherent ideals). -/
theorem pullback_finiteSum {f : Y → X} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) :
    ∀ (A : MarkedIdeal n X) (L : List (MarkedIdeal n X)), A.ideal.IsCoherent → (∀ B ∈ L, B.ideal.IsCoherent) →
      MarkedIdeal.pullback f (finiteSum A L) = finiteSum (MarkedIdeal.pullback f A) (L.map (MarkedIdeal.pullback f))
  | A, [], _, _ => rfl
  | A, B :: L, hA, hL => by
      have hB := hL B (by simp)
      have hL' : ∀ C ∈ L, C.ideal.IsCoherent := fun C hC => hL C (List.mem_cons_of_mem B hC)
      have hS := isCoherent_finiteSum B L hB hL'
      have ih := pullback_finiteSum hf B L hB hL'
      change MarkedIdeal.pullback f (MarkedIdealOperationsTransform.MarkedIdeal.add A (finiteSum B L)) =
        MarkedIdealOperationsTransform.MarkedIdeal.add (MarkedIdeal.pullback f A)
          (finiteSum (MarkedIdeal.pullback f B) (L.map (MarkedIdeal.pullback f)))
      rw [← ih]
      refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
      change GermIdeal.pullback (m := n) f
          (sumIdeal (idealPow A.ideal (finiteSum B L).d) (idealPow (finiteSum B L).ideal A.d)) =
        sumIdeal (idealPow (GermIdeal.pullback (m := n) f A.ideal) (finiteSum B L).d)
          (idealPow (GermIdeal.pullback (m := n) f (finiteSum B L).ideal) A.d)
      have hPA := GermIdealPullbackCalculus.isCoherent_idealPow hA (finiteSum B L).d
      have hPS := GermIdealPullbackCalculus.isCoherent_idealPow hS A.d
      rw [MarkedIdealOperationsTransform.pullback_sumIdeal hf
          (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hPA hg)
          (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hPS hg),
        BlowupExceptionalDivisor.pullback_idealPow hf hA, BlowupExceptionalDivisor.pullback_idealPow hf hS]

end Sum

/-! ### The canonical marked ideals of the joint profile -/

section Canonical

variable {X Y : CMfd.{u} n}

/-- **The canonical old factor of one member `H`**: the monomial part, along `born`, of the trace of `H` on `N`, mark one. -/
def factorOf (N H : Set X) (born : List (Set X)) : MarkedIdeal n X :=
  ⟨N, born, monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) born, 1⟩

theorem canonicalFactorMarked_eq_factorOf (N : Set X) (old born : List (Set X)) (i : Fin old.length) :
    canonicalFactorMarked N old born i = factorOf N (old.get i) born := rfl

/-- The joint profile marked ideal has a coherent ideal. -/
theorem isCoherent_jointProfileMarked (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) (q : ℕ) (P : Finset (Fin old.length)) :
    (jointProfileMarked N old born q P).ideal.IsCoherent := by
  refine isCoherent_finiteSum _ _ ?_ ?_
  · refine relative_product_coherent hN _ ?_
    intro I hI
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hI
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    exact (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.1
  · intro B hB
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hB
    exact (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1

variable {f : Y → X} (hf : HironakaBaseChange.IsOpenHoloEmbedding n f)

include hf in
/-- The trace of a member pulls back along an open holomorphic embedding. -/
theorem pullback_trace {N H : Set X} (hN : IsClosedSubmanifold n N) (hH : (vanishingIdeal (n := n) H).IsCoherent) :
    GermIdeal.pullback (m := n) f (restrictOn n N (vanishingIdeal (n := n) H)) =
      restrictOn n (f ⁻¹' N) (vanishingIdeal (n := n) (f ⁻¹' H)) := by
  rw [pullback_restrictOn_of_local (exists_isLocalInverseAt_of_isOpenHoloEmbedding hf) hN hH,
    HironakaActualOpenEmbeddingVanishingIdeal.pullback_vanishingIdeal_of_isOpenHoloEmbedding f hf H]

include hf in
/-- **The canonical factor of a member pulls back** along an open holomorphic embedding. -/
theorem pullback_factorOf {N H : Set X} (born : List (Set X)) (hN : IsClosedSubmanifold n N)
    (hH : (vanishingIdeal (n := n) H).IsCoherent) :
    MarkedIdeal.pullback f (factorOf N H born) = factorOf (f ⁻¹' N) (f ⁻¹' H) (born.map (f ⁻¹' ·)) := by
  have hTr := isCoherent_restrictOn hH (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) f (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) born) =
    monomialPartAlong n (f ⁻¹' N) (restrictOn n (f ⁻¹' N) (vanishingIdeal (n := n) (f ⁻¹' H))) (born.map (f ⁻¹' ·))
  rw [MonomialPartEtale.pullback_monomialPartAlong (exists_isLocalInverseAt_of_isOpenHoloEmbedding hf)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hTr hg), pullback_trace hf hN hH]

include hf in
/-- **The canonical residual of a member pulls back** along an open holomorphic embedding (geometry of the canonical
parts). -/
theorem pullback_residual (hn : 0 < n) {N : Set X} {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) (i : Fin old.length) :
    GermIdeal.pullback (m := n) f (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) (old.get i))) born) =
      nonmonomialPartAlong n (f ⁻¹' N) (restrictOn n (f ⁻¹' N) (vanishingIdeal (n := n) (f ⁻¹' old.get i)))
        (born.map (f ⁻¹' ·)) := by
  have hParts := actual_old_parts_geometry hn hN hE hTr hdense i
  have hH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn (isSNCDivisor_of_sublist hE (List.sublist_append_left _ _)) i)
  have h := MonomialPartEtale.pullback_nonmonomialPartAlong (exists_isLocalInverseAt_of_isOpenHoloEmbedding hf)
    hParts.1 hParts.2.2.2.2.1 hParts.2.2.1
  change GermIdeal.pullback (m := n) f (nonmonomialPartAlong n N (oldTraceIdeal N old i) born) = _
  rw [h]
  change nonmonomialPartAlong n (f ⁻¹' N) (GermIdeal.pullback (m := n) f
    (restrictOn n N (vanishingIdeal (n := n) (old.get i)))) (born.map (f ⁻¹' ·)) = _
  rw [pullback_trace hf hN hH]

/-- Compatible open embeddings give the same whole native residual
on their common comparison domain. The born list agrees positionwise. -/
theorem retained_residual_pullback_eq_of_compatible_open_embeddings
    (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born,D))
    (i : Fin old.length) {f₁ f₂ : Y → X}
    (hf₁ : HironakaBaseChange.IsOpenHoloEmbedding n f₁)
    (hf₂ : HironakaBaseChange.IsOpenHoloEmbedding n f₂)
    (hCarrier : f₁ ⁻¹' N = f₂ ⁻¹' N)
    (hSelected : f₁ ⁻¹' old.get i = f₂ ⁻¹' old.get i)
    (hBorn : born.map (f₁ ⁻¹' ·) = born.map (f₂ ⁻¹' ·)) :
    GermIdeal.pullback (m := n) f₁ (oldResidualPart N old born i) =
      GermIdeal.pullback (m := n) f₂ (oldResidualPart N old born i) := by
  have h₁ := pullback_residual hf₁ hn hN hFull hTr hDense i
  have h₂ := pullback_residual hf₂ hn hN hFull hTr hDense i
  rw [hCarrier,hSelected,hBorn,←h₂] at h₁
  exact h₁

/-- The actual native residual zero locus therefore agrees under those
same open embeddings. -/
theorem retained_residual_zeroLocus_preimage_eq_of_compatible_open_embeddings
    (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born,D))
    (i : Fin old.length) {f₁ f₂ : Y → X}
    (hf₁ : HironakaBaseChange.IsOpenHoloEmbedding n f₁)
    (hf₂ : HironakaBaseChange.IsOpenHoloEmbedding n f₂)
    (hCarrier : f₁ ⁻¹' N = f₂ ⁻¹' N)
    (hSelected : f₁ ⁻¹' old.get i = f₂ ⁻¹' old.get i)
    (hBorn : born.map (f₁ ⁻¹' ·) = born.map (f₂ ⁻¹' ·)) :
    f₁ ⁻¹' (oldResidualPart N old born i).zeroLocus =
      f₂ ⁻¹' (oldResidualPart N old born i).zeroLocus := by
  have hI := retained_residual_pullback_eq_of_compatible_open_embeddings hn hN hFull hTr hDense i
    hf₁ hf₂ hCarrier hSelected hBorn
  have hc := (actual_old_parts_geometry hn hN hFull hTr hDense i).2.2.1
  have hZero := congrArg GermIdeal.zeroLocus hI
  rwa [BlowupExceptionalDivisor.zeroLocus_pullback (contMDiff_of_isOpenHoloEmbedding hf₁) hc,
    BlowupExceptionalDivisor.zeroLocus_pullback (contMDiff_of_isOpenHoloEmbedding hf₂) hc] at hZero

include hf in
/-- **The canonical product pulls back** along an open holomorphic embedding, with the preimages of `N` and of the members. -/
theorem pullback_canonicalProductMarked (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) (q : ℕ) :
    MarkedIdeal.pullback f (canonicalProductMarked N old born q) =
      canonicalProductMarked (f ⁻¹' N) (old.map (f ⁻¹' ·)) (born.map (f ⁻¹' ·)) q := by
  have hCoh : ∀ I ∈ canonicalResidualFamily N old born, I.IsCoherent := by
    intro I hI
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hI
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    exact (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.1
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) f (relativeIdealListProduct N (canonicalResidualFamily N old born)) =
    relativeIdealListProduct (f ⁻¹' N) (canonicalResidualFamily (f ⁻¹' N) (old.map (f ⁻¹' ·)) (born.map (f ⁻¹' ·)))
  rw [pullback_relativeIdealListProduct_of_local (exists_isLocalInverseAt_of_isOpenHoloEmbedding hf)
    (contMDiff_of_isOpenHoloEmbedding hf) hN _ hCoh]
  congr 1
  simp only [canonicalResidualFamily, List.map_map]
  apply List.map_congr_left
  intro H hH
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
  exact pullback_residual hf hn hN hE hTr hdense i

include hf in
/-- **The joint profile marked ideal pulls back** along an open holomorphic embedding, in index-free form: the product of
the preimage data, followed by the factors of the preimages of the members `old.get i`, `i ∈ P`, in the order of `P`. -/
theorem pullback_jointProfileMarked (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) (q : ℕ) (P : Finset (Fin old.length)) :
    MarkedIdeal.pullback f (jointProfileMarked N old born q P) =
      finiteSum (canonicalProductMarked (f ⁻¹' N) (old.map (f ⁻¹' ·)) (born.map (f ⁻¹' ·)) q)
        (P.toList.map fun i => factorOf (f ⁻¹' N) (f ⁻¹' old.get i) (born.map (f ⁻¹' ·))) := by
  have hcP : (canonicalProductMarked N old born q).ideal.IsCoherent := by
    refine relative_product_coherent hN _ ?_
    intro I hI
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hI
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    exact (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.1
  have hcL : ∀ B ∈ P.toList.map (canonicalFactorMarked N old born), B.ideal.IsCoherent := by
    intro B hB
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hB
    exact (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1
  unfold jointProfileMarked
  rw [pullback_finiteSum (contMDiff_of_isOpenHoloEmbedding hf) _ _ hcP hcL,
    pullback_canonicalProductMarked hf hn hN hE hTr hdense q, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  have hH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn (isSNCDivisor_of_sublist hE (List.sublist_append_left _ _)) i)
  exact pullback_factorOf hf born hN hH

/-- **Two open holomorphic embeddings with the same preimages of `N` and of every member pull the joint profile marked ideal
back to the same marked ideal.** -/
theorem pullback_jointProfileMarked_eq_of_preimage_eq (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) (q : ℕ) (P : Finset (Fin old.length))
    {f₁ f₂ : Y → X} (hf₁ : HironakaBaseChange.IsOpenHoloEmbedding n f₁)
    (hf₂ : HironakaBaseChange.IsOpenHoloEmbedding n f₂) (hNN : f₁ ⁻¹' N = f₂ ⁻¹' N)
    (hHH : ∀ H ∈ old ++ born, f₁ ⁻¹' H = f₂ ⁻¹' H) :
    MarkedIdeal.pullback f₁ (jointProfileMarked N old born q P) =
      MarkedIdeal.pullback f₂ (jointProfileMarked N old born q P) := by
  rw [pullback_jointProfileMarked hf₁ hn hN hE hTr hdense q P, pullback_jointProfileMarked hf₂ hn hN hE hTr hdense q P]
  have hold : old.map (f₁ ⁻¹' ·) = old.map (f₂ ⁻¹' ·) :=
    List.map_congr_left fun H hH => hHH H (List.mem_append_left _ hH)
  have hborn : born.map (f₁ ⁻¹' ·) = born.map (f₂ ⁻¹' ·) :=
    List.map_congr_left fun H hH => hHH H (List.mem_append_right _ hH)
  rw [hNN, hold, hborn]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [hHH _ (List.mem_append_left _ (List.get_mem old i))]

end Canonical

/-! ### Opens and the joint mask block -/

section Block

variable {X : CMfd.{u} n} {V V' : Opens X}
  (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')

/-- **Naturality of the joint profile marked ideal under a biholomorphism of opens preserving the data**: if
`φ : V ≅ V'` maps `N ∩ V` onto `N ∩ V'` and every member `H ∩ V` of `old ++ born` onto `H ∩ V'`, then
`φ^*(J|_{V'}) = J|_V` for `J = jointProfileMarked N old born q P`. -/
theorem pullback_restrict_jointProfileMarked (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) (q : ℕ) (P : Finset (Fin old.length))
    (hφN : ∀ p : V, ((φ p : V') : X) ∈ N ↔ (p : X) ∈ N)
    (hφH : ∀ H ∈ old ++ born, ∀ p : V, ((φ p : V') : X) ∈ H ↔ (p : X) ∈ H) :
    MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V' → X) (jointProfileMarked N old born q P)) =
      MarkedIdeal.pullback (Subtype.val : V → X) (jointProfileMarked N old born q P) := by
  have hcJ := isCoherent_jointProfileMarked hn hN hE hTr hdense q P
  rw [StepOneTangentChange.pullback_pullback_of_comp hcJ contMDiff_subtype_val φ.contMDiff (fun _ => rfl)]
  have hf₁ : HironakaBaseChange.IsOpenHoloEmbedding n (fun p : V => ((φ p : V') : X)) := ⟨V', φ, fun _ => rfl⟩
  exact pullback_jointProfileMarked_eq_of_preimage_eq hn hN hE hTr hdense q P hf₁
    (HironakaBaseChange.isOpenHoloEmbedding_val V) (Set.ext fun p => hφN p)
    (fun H hH => Set.ext fun p => hφH H hH p)

/-- **Equivariance of the joint mask block**: if `φ : V ≅ V'` preserves `N` and every member of `old ++ born`, every tower
whose centres are empty or maximum loci of the canonical invariant `invFamily` of the joint profile marked ideal (in
particular the block of `HironakaActualRetainedBoundaryMaskBlock.exists_actual_retained_boundary_joint_mask_block`) has
`R|_V ≅ R|_{V'}` over `φ`, stage by stage. -/
theorem exists_isTowerIso_restrict_joint_mask_block (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) (q : ℕ) (P : Finset (Fin old.length))
    (hdom : IsInvDomain (n + 1) (jointProfileMarked N old born q P))
    (hφN : ∀ p : V, ((φ p : V') : X) ∈ N ↔ (p : X) ∈ N)
    (hφH : ∀ H ∈ old ++ born, ∀ p : V, ((φ p : V') : X) ∈ H ↔ (p : X) ∈ H)
    {Z : CMfd.{u} n} (R : BlowupTower X Z)
    (hR : IsCanonical (jointProfileMarked N old born q P)
      ((CanonicalCentres.invFamily hn (n + 1)).inv (jointProfileMarked N old born q P)) R) :
    ∃ χ : CMfd.of (n := n) (openPreimage R V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage R V'), IsTowerIso φ (restrict V R) (restrict V' R) χ :=
  exists_isTowerIso_restrict_of_isCanonical (CanonicalCentres.invFamily hn (n + 1)) hdom φ
    (pullback_restrict_jointProfileMarked φ hn hN hE hTr hdense q P hφN hφH) R hR

end Block

end

end Hironaka.HironakaG34JointMaskEquivariance
