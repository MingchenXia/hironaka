/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilInvariant
public import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
import Hironaka.Resolution.Algebraic.Balanced.GoingUpChain
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Parameters
import Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingDescent
import Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingHypersurface
import Hironaka.Resolution.Algebraic.Stage.Coherence
import Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems
import Hironaka.Resolution.Algebraic.Stage.DimZero
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCaseA
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCoreTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilSmooth
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Restrict
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.Snc.HasSncWith
import Hironaka.Scheme.Snc.RelativeDimension
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Scheme
import Hironaka.Resolution.Algebraic.Stage.Tower
public import Hironaka.Resolution.Algebraic.Tuning.Parameter
import Hironaka.Scheme.BlowUpSequence.Defs

/-!
# The core lemma of the smooth case, and the empty succession

**The core lemma** (`core_bmoOneRun : Core k`): for a marked triple `(X, I, 1, ∅)` whose `V(I)`
is regular stalkwise and with `I ≠ 𝒪_X`, the run of `BMO_1` starts with a blow-up whose centre
contains a generic point of `V(I)`. Proved for the tower of order reductions stage by stage
(`CoreAt n`, induction on the stage as for Kollár's Claim 71.2 in [Kol07, 108]), for `V(I)` smooth
over `k`:

* stage `0`: `I = 𝒪_X` (`Triple.I_eq_top_of_hasDimLE_zero`), nothing to prove;
* stage `n + 1`: `max-ord I = 1` (`maxOrd_eq_one_of_smooth_of_ne_top`); the local cover
  `g : X' → X` of [Kol07, Theorem 105] (`globalizationData_localClass`,
  `Triple.exists_isLocalCover`) carries a smooth hypersurface `H ⊇ V(I')` of maximal contact for
  `(I', 1)`, and `BMO_1` commutes with the smooth surjection `g` ([Kol07, Theorem 107 (2)]); on
  `X'`, either
  (A) some component of `H` lies in `V(I')` (`Z_{-1}(I', 1, H) ≠ 𝒪_{X'}`): `BMO_1 = BO_1` at the
  mark (Kollár's Claim 71.1, `tower_bmo_eq_bo_of_maxOrd`), `BO_1` on `X'` is Step 2 for `H`
  (`functor_seq_localClass`) whose first blow-up is `Z_{-1}` itself
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCaseA`) — a generic point of a selected component
  of `H` is a generic point of `V(I')` in the centre; or
  (B) `Z_{-1} = 𝒪_{X'}`: `I' = j_* (I'|_H)` with `I'|_H` nonzero on every component of `H`
  (`isNonzeroEverywhere_comap_subschemeι_of_Zminus1_eq_top`), so the hypersurface case of the
  descent along closed embeddings (`tower_bmo_one_eq_pushforward_of_isSmoothDivisor_ker`) brings
  the run down to `(H, I'|_H, 1, ∅)` at the stage `n` (coherence of the tower), where the induction
  hypothesis gives the centre; the generic point is carried back along `j`
  (`mem_genericPoints_support_map_iff`).
  Finally the centre and its generic point are carried back along the cover
  (`mem_genericPoints_of_openImmersionCoprods`).

**The empty succession** (`bed_eq_nil_of_smooth`): for a smooth reduced `Y` the embedded
desingularization sequence `BED(X, I_Y, ∅)` is the empty succession ([Wlo05, 4.6]), by
`bed_eq_nil_of_smooth_of_core` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilSmooth`) — the loop
on `(X, I_Y, ∅)` absorbs a component at stage `0` of every round and never blows up. The clauses of
the theorem do not need this statement; it records that the sequence does nothing on a smooth `Y`.
The general tools are in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCoreTools`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  Scheme Hironaka IdealSheafData BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence
  Hironaka.Local Hironaka.Stage Hironaka.BO Hironaka.BD

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- **The core lemma at the stage `n` of the tower** — for a marked triple of `BMOClass n 1` with
empty boundary, `V(I)` smooth over `k` and `I ≠ 𝒪_X`, the stage-`n` functor's run starts with a
blow-up whose centre contains a generic point of `V(I)`. -/
def CoreAt (k : Type u) [Field k] [CharZero k] (n : ℕ) : Prop :=
  ∀ (T : MarkedTriple k) (hT : T.BMOClass n 1), IsEmpty T.E.ι →
    Smooth (T.I.subschemeι ≫ (T.X.left ↘ Spec (CommRingCat.of k))) → T.I ≠ ⊤ →
    ∃ (D : T.X.left.IdealSheafData) (rest : BlowUpSequence D.blowUp),
      (((tower stage0 n).bmo 1).functor k).seq T hT = BlowUpSequence.cons T.X.left D rest ∧
        ∃ η ∈ T.I.support.genericPoints, η ∈ D.support

/-- Stage `0`: the ideal is the unit ideal (the base case of the tower), so there is nothing to
prove. -/
theorem coreAt_zero : CoreAt k 0 := by
  intro T hT _ _ hne
  exact absurd (Triple.I_eq_top_of_hasDimLE_zero T.toTriple hT.2.1) hne

omit [CharZero k] in
/-- A selected generic point of `H` lies in `Z_{-1}(I, 1, H)`. -/
theorem mem_support_Zminus1_of_mem {X : Scheme.{u}} (I H : X.IdealSheafData) {ξ : X}
    (hgen : ξ ∈ H.support.genericPoints) (hord : ((1 : ℕ) : ℕ∞) ≤ I.ord ξ) :
    ξ ∈ (Zminus1 I 1 H).support := by
  rw [Zminus1, Hironaka.Sequence.support_vanishingIdeal_eq]
  have hle : Closeds.closure {ξ} ≤
      ⨆ ζ : {ζ : X // ζ ∈ H.support.genericPoints ∧ ((1 : ℕ) : ℕ∞) ≤ I.ord ζ},
        Closeds.closure {(ζ : X)} :=
    le_iSup (fun ζ : {ζ : X // ζ ∈ H.support.genericPoints ∧ ((1 : ℕ) : ℕ∞) ≤ I.ord ζ} =>
      Closeds.closure {(ζ : X)}) ⟨ξ, hgen, hord⟩
  exact hle (by
    rw [← SetLike.mem_coe, Closeds.coe_closure]
    exact subset_closure (Set.mem_singleton _))

omit [CharZero k] in
/-- A sequence whose pullback starts with a blow-up starts with a blow-up, of the centre whose
pullback is the given one. -/
theorem exists_cons_of_pullback_eq_cons {X Y : Scheme.{u}} (S : BlowUpSequence X) (g : Y ⟶ X)
    {D' : Y.IdealSheafData} {rest' : BlowUpSequence D'.blowUp}
    (h : S.pullback g = BlowUpSequence.cons Y D' rest') :
    ∃ (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp),
      S = BlowUpSequence.cons X D rest ∧ D.comap g = D' := by
  cases S with
  | nil =>
    rw [pullback_nil] at h
    cases h
  | cons X D rest =>
    rw [pullback_cons] at h
    exact ⟨D, rest, rfl, (BlowUpSequence.cons.inj h).1⟩

/-- **The induction step** — Kollár's local chain (the cover of [Kol07, Theorem 105] with a
hypersurface of maximal contact), the absorbed-component case through the first blow-up of
[Kol07, Lemma 102], the other case through the hypersurface descent to the stage below. -/
theorem coreAt_succ (n : ℕ) (ih : CoreAt k n) : CoreAt k (n + 1) := by
  intro T₀ hT hE hsm hne
  obtain ⟨T, m⟩ := T₀
  obtain rfl : m = 1 := hT.2.2
  have hE₀ : IsEmpty T.E.ι := hE
  have hsm₀ : Smooth (T.I.subschemeι ≫ (T.X.left ↘ Spec (.of k))) := hsm
  have hne₀ : T.I ≠ ⊤ := hne
  have h1 : T.I.maxOrd = ((1 : ℕ) : ℕ∞) :=
    maxOrd_eq_one_of_smooth_of_ne_top (T.X.left ↘ Spec (.of k)) T.I T.isNonzeroEverywhere hne₀
  have hbo : Triple.BOClass (n + 1) 1 T := ⟨le_rfl, hT.2.1, h1.le⟩
  have : Nonempty T.X.left := by
    obtain ⟨x, -⟩ := exists_mem_support_of_ne_top T.I hne₀
    exact ⟨x⟩
  -- Theorem 105's local cover with a smooth hypersurface of maximal contact
  obtain ⟨T', g, -, hLT, hM, hsurj, hpb⟩ :=
    Triple.exists_isLocalCover (globalizationData_localClass (n + 1) 1) hbo
  obtain ⟨H, hH, hmaxc⟩ := hLT.2
  have hHle : H ≤ T'.I := by
    have h := hmaxc
    change H ≤ MC (T'.X.left ↘ Spec (.of k)) T'.I 1 at h
    rwa [MC_one] at h
  have hsmg : Smooth g := openImmersionCoprods.smooth hM
  have hI' : T'.I = T.I.comap g := hpb.2.1
  have hE' : IsEmpty T'.E.ι := by
    rw [hpb.2.2]
    exact hE₀
  have hsm' : Smooth (T'.I.subschemeι ≫ (T'.X.left ↘ Spec (.of k))) := by
    rw [hI', ← hpb.1]
    exact smooth_comap_subschemeι_comp (T.X.left ↘ Spec (.of k)) g T.I
  have hne' : T'.I ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_mem_support_of_ne_top T.I hne₀
    obtain ⟨y, rfl⟩ := hsurj x
    have hy : y ∈ T'.I.support := by
      rw [hI', mem_support_comap_iff_apply]
      exact hx
    rw [h, support_top, ← SetLike.mem_coe, Closeds.coe_bot] at hy
    exact hy
  have h1' : T'.I.maxOrd = ((1 : ℕ) : ℕ∞) := by
    rw [hI', Hironaka.BMO.maxOrd_comap_of_surjective T.I g hsurj]
    exact h1
  -- the marked triple of the cover and Theorem 107 (2) along `g`
  let TX' : MarkedTriple k := ⟨T', 1⟩
  have hTX' : TX'.BMOClass (n + 1) 1 := ⟨le_rfl, hLT.1.2.1, rfl⟩
  have hpbM : TX'.IsPullbackOf ⟨T, 1⟩ g := ⟨hpb, rfl⟩
  have hpull : (((tower stage0 (n + 1)).bmo 1).functor k).seq TX' hTX' =
      ((((tower stage0 (n + 1)).bmo 1).functor k).seq ⟨T, 1⟩ hT).pullback g :=
    (((tower stage0 (n + 1)).bmo 1).commutesWithSmooth k).1 ⟨T, 1⟩ TX' g hsurj hpbM hT hTX'
  suffices key : ∃ (D' : T'.X.left.IdealSheafData) (rest' : BlowUpSequence D'.blowUp),
      (((tower stage0 (n + 1)).bmo 1).functor k).seq TX' hTX' =
        BlowUpSequence.cons T'.X.left D' rest' ∧
        ∃ η' ∈ T'.I.support.genericPoints, η' ∈ D'.support by
    obtain ⟨D', rest', hseq', η', hη', hη'D⟩ := key
    rw [hpull] at hseq'
    obtain ⟨D, rest, hS, hD⟩ := exists_cons_of_pullback_eq_cons _ g hseq'
    refine ⟨D, rest, hS, g η', ?_, ?_⟩
    · rw [hI'] at hη'
      exact mem_genericPoints_of_openImmersionCoprods hM T.I hη'
    · rw [← hD, mem_support_comap_iff_apply] at hη'D
      exact hη'D
  by_cases hZ : Zminus1 T'.I 1 H = ⊤
  · -- Case B: the closed-embedding descent to `H`
    have hker : H.subschemeι.ker ≤ T'.I := by
      rw [ker_subschemeι]
      exact hHle
    have hIJ : T'.I = (T'.I.comap H.subschemeι).map H.subschemeι :=
      (map_comap_of_ker_le H.subschemeι T'.I hker).symm
    have hJnz : IsNonzeroEverywhere (T'.I.comap H.subschemeι) :=
      isNonzeroEverywhere_comap_subschemeι_of_Zminus1_eq_top T'.I H hZ
    obtain ⟨d, hdle, hd⟩ := hLT.1.2.1
    have hdi : SmoothOfRelativeDimension d (T'.X.left ↘ Spec (.of k)) := hd
    have hHdim : SmoothOfRelativeDimension (d - 1) (H.subschemeι ≫ (T'.X.left ↘ Spec (.of k))) :=
      smoothOfRelativeDimension_of_isSmoothDivisor (T'.X.left ↘ Spec (.of k)) d H hH
    have hHsm : Smooth (H.subschemeι ≫ (T'.X.left ↘ Spec (.of k))) :=
      SmoothOfRelativeDimension.smooth (d - 1) _
    have hEι : IsEmpty (T'.E.comap H.subschemeι).ι := hE'
    let TY : MarkedTriple k :=
      { X := .ofHom (H.subschemeι ≫ (T'.X.left ↘ Spec (.of k)))
          (inferInstanceAs (FiniteType (H.subschemeι ≫ (T'.X.left ↘ Spec (.of k)))))
          (inferInstanceAs (IsSeparated (H.subschemeι ≫ (T'.X.left ↘ Spec (.of k)))))
        smoothOfRelativeDimension := ⟨d - 1, hHdim⟩
        I := T'.I.comap H.subschemeι
        isNonzeroEverywhere := hJnz
        E := T'.E.comap H.subschemeι
        isSnc := Stage.isSnc_of_isEmpty (H.subschemeι ≫ (T'.X.left ↘ Spec (.of k))) _
        m := 1 }
    have hj : MarkedTriple.ClosedEmbedding TX' TY H.subschemeι := ⟨⟨rfl, hIJ, rfl⟩, rfl⟩
    have hHker : IsSmoothDivisor H.subschemeι.ker := by
      rw [ker_subschemeι]
      exact hH
    have hdesc := tower_bmo_one_eq_pushforward_of_isSmoothDivisor_ker stage0 TX' TY H.subschemeι
      hj hE' hTX' hHker
    have hTYn : TY.BMOClass n 1 := ⟨le_rfl, ⟨d - 1, by omega, hHdim⟩, rfl⟩
    rw [tower_bmo_coherent stage0 1 (Nat.le_succ n) TY (bmoClass_of_closedEmbedding hj hTX')
      hTYn] at hdesc
    have hsmJ : Smooth ((T'.I.comap H.subschemeι).subschemeι ≫ H.subschemeι ≫
        (T'.X.left ↘ Spec (.of k))) := by
      have : Smooth (((T'.I.comap H.subschemeι).map H.subschemeι).subschemeι ≫
          (T'.X.left ↘ Spec (.of k))) := by
        rw [← hIJ]
        exact hsm'
      exact smooth_subschemeι_comp_of_map (T'.X.left ↘ Spec (.of k)) H.subschemeι
        (T'.I.comap H.subschemeι)
    have hJne : TY.I ≠ ⊤ := by
      intro h
      change T'.I.comap H.subschemeι = ⊤ at h
      apply hne'
      rw [hIJ, h, Scheme.IdealSheafData.map_top]
    obtain ⟨D₀, rest₀, hseq₀, η₀, hη₀, hη₀D⟩ := ih TY hTYn hEι hsmJ hJne
    rw [hseq₀, pushforward_cons] at hdesc
    refine ⟨_, _, hdesc, H.subschemeι η₀, ?_, mem_support_map_of_mem H.subschemeι D₀ hη₀D⟩
    have hη₀' : η₀ ∈ (T'.I.comap H.subschemeι).support.genericPoints := hη₀
    have := (mem_genericPoints_support_map_iff H.subschemeι (T'.I.comap H.subschemeι)
      (H.subschemeι η₀)).mpr ⟨η₀, hη₀', rfl⟩
    rwa [← hIJ] at this
  · -- Case A: a component of `H` lies in `V(I')`; the first blow-up is `Z_{-1}`
    have hbo' : Triple.BOClass (n + 1) 1 T' := hLT.1
    have hBO : (((tower stage0 (n + 1)).bmo 1).functor k).seq TX' hTX' =
        (((tower stage0 (n + 1)).bo 1).functor k).seq T' hbo' :=
      tower_bmo_eq_bo_of_maxOrd stage0 1 (n + 1) T' hbo' hE' h1'
    rw [tower_succ_bo, boOfBMO_functor,
      Hironaka.BO.functor_seq_localClass (n + 1) 1 _ T' hbo' hH hmaxc] at hBO
    obtain ⟨D', rest', hmc', hDZ⟩ := maxContactCase_bdData_eq_cons_of_Zminus1_ne_top (n := n + 1)
      T' hH hmaxc hE' (amalgamDom n) (fun k _ _ => amalgam (tower stage0 n).bmo k)
      (fun m k _ _ T' hd hm => amalgamClass_of_tuningParam k m T' hd hm)
      (fun k _ _ T' hT' => amalgam_maxOrd_endTriple_lt (tower stage0 n).bmo k T' hT')
      (fun k _ _ => amalgam_commutesWithSmooth (tower stage0 n).bmo k)
      (fun k _ _ _ _ _ σ => amalgam_commutesWithBaseChange (tower stage0 n).bmo k σ) hbo' h1' hZ
    have hne_idx :
        Nonempty {ξ : T'.X.left // ξ ∈ H.support.genericPoints ∧ ((1 : ℕ) : ℕ∞) ≤ T'.I.ord ξ} := by
      by_contra hemp
      rw [not_nonempty_iff] at hemp
      apply hZ
      rw [Zminus1, iSup_of_empty, vanishingIdeal_bot]
    obtain ⟨⟨ξ, hξgen, hξord⟩⟩ := hne_idx
    have hξI : ξ ∈ T'.I.support := by
      rw [Nat.cast_one] at hξord
      exact (one_le_ord_iff T'.I ξ).mp hξord
    refine ⟨D', rest', hBO.trans hmc', ξ,
      ⟨hξI, fun x hx hxs => hξgen.2 (support_antitone hHle hx) hxs⟩, ?_⟩
    rw [hDZ]
    exact mem_support_Zminus1_of_mem T'.I H hξgen hξord

/-- The core lemma at every stage of the tower. -/
theorem coreAt (n : ℕ) : CoreAt k n := by
  induction n with
  | zero => exact coreAt_zero
  | succ n ih => exact coreAt_succ n ih

/-- **The core lemma of the smooth case** — for a marked triple `(X, I, 1, ∅)` whose `V(I)` is
regular stalkwise (hence smooth over `k`) and with `I ≠ 𝒪_X`, the run of `BMO_1` (`BMO_m 1 k`, the
tower at the stage `dim X`) starts with a blow-up whose centre contains a generic point of
`V(I)`. -/
theorem core_bmoOneRun : Core k := by
  intro T hm hE hreg hne
  have hPF : PerfectField k := PerfectField.ofCharZero
  have hsm : Smooth (T.I.subschemeι ≫ (T.X.left ↘ Spec (.of k))) :=
    (Scheme.smooth_iff_isRegular (T.I.subschemeι ≫ (T.X.left ↘ Spec (.of k)))).mpr
      (isRegular_subscheme_of_isRegularLocalRing_quotient T.I hreg)
  have hT : T.BMOClassFree 1 := ⟨le_rfl, hm⟩
  obtain ⟨D, rest, hseq, η, hη, hηD⟩ :=
    coreAt T.toTriple.dim T (MarkedTriple.bmoClass_of_bmoClassFree hT) hE hsm hne
  refine ⟨D, rest, ?_, η, hη, hηD⟩
  exact hseq

/-- **The empty succession for a smooth `Y`** — for a smooth reduced `Y` the embedded
desingularization sequence `BED(X, I_Y, ∅)` is the empty succession ([Wlo05, 4.6]). -/
theorem bed_eq_nil_of_smooth (TX : Triple k) (hE : IsEmpty TX.E.ι)
    (hY : Smooth (TX.I.subschemeι ≫ (TX.X.left ↘ Spec (CommRingCat.of k)))) :
    BED TX = BlowUpSequence.nil TX.X.left :=
  bed_eq_nil_of_smooth_of_core core_bmoOneRun TX hE hY

end Hironaka.Resolution
