/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.DerivativeIdealAlongTransform
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.HomogenizedEtale
import Hironaka.MarkedIdeal.HomogenizedEquivalence
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.MarkedIdeal.DerivativeIdealTower
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.MarkedIdeal.RestrictLe
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Homogenized and coefficient ideals along a submanifold, along multiple test blow-ups

The rest of step (4d) of item (4) of `hir:along-calculus`, on top of item (2) (`DerivativeIdealAlongTransform`).
Sources: Włodarczyk 2005, Lemma `le:inclusions` along multiple test blow-ups, Lemma `le:operations` (1) for `m`
summands, Lemma `le:coeff` (`𝓒(𝔪) ≃ 𝔪`) and the lemma after `le:hom` (`(𝓗(𝓘), μ) ≃ (𝓘, μ)`), all for a marked ideal
`(M, N, E, 𝔞, d)` on a closed submanifold `N` (Bierstone--Milman 2008, Definitions 2.1--2.2: the derivatives are
those of `𝔞|_N ⊆ 𝒪_N`), with the derivative, coefficient and homogenized ideals along `N` of
`HomogenizedIdealAlong`.

Along `N` the ideal of a marked ideal only matters through its restriction to `N`, so the statements hold up to
restricted equivalence (`MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv`), which has the same cosupports, the same
admissible centres and the same transforms.

* One admissible blowup (`π` along `C ⊆ N`, `N' = ` the strict transform): `restrictEquiv_geoTransform_of_pullback` (the
  transform is characterised by `Res_{N'} π^*𝔞 = Res_{N'} (π^*𝓘_C)^d 𝔞'`); `restrictLe_geoTransform_of_restrictLe`
  (transforms are monotone along `N`); `geoTransform_msum_restrictEquiv` (Włodarczyk's sum of `m` marked ideals on `N`);
  `geoTransform_homSum_restrictEquiv` (`σ(∑ᵢ Aᵢ Bⁱ, μ) ≃ ∑ᵢ σ(Aᵢ, μ - i) σ(B, 1)ⁱ` along `N`).
* Towers: `inclusions_tower_along` (`le:inclusions` along a multiple test blow-up along `N`:
  `[𝓓_N^j 𝔪]_T ⊆ 𝓓_{N_T}^j(𝔪_T)` on `N_T`); `geoTransformAlong_msum_along` (`le:operations` (1) for `m` summands along
  `N`); **`coeffAlong_wEquiv`: `𝓒_N(𝔪) ≃ 𝔪`**; `hom_tower_along` (`𝓗_N(𝔪)_T ≃ ∑ᵢ [𝓓_N^i 𝔪]_T [T_N(𝔪)]_Tⁱ`);
  **`homAlong_wEquiv`: `𝓗_N(𝔪) ≃ 𝔪`**; `coeff_homAlong_wEquiv`: `𝓒_N(𝓗_N(𝔪)) ≃ 𝔪`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedIdealAlongTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal IdealWeightPowers InvertibleIdealQuotient RestrictedIdealWeight RestrictedIdealQuotient RestrictedIdealExtension BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdeal HomogenizedEquivalence HomogenizedIdealAlong MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal GermIdealPullbackCalculus BlowupStrictSubmanifold HomogenizedGlueing DerivativeIdealAlong DerivativeIdealAlongCoherent

noncomputable section

/-! ### Restricted calculus of finite sums -/

section Algebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Restricted inclusions add up over finite sums.** -/
theorem restrictLe_finSumIdeal {W : Set M} {J J' : ℕ → GermIdeal n M} {m : ℕ}
    (hJ' : ∀ i < m, ∀ x g, (J' i).mem x g → HolomorphicAt n g x) (h : ∀ i < m, RestrictLe W (J i) (J' i)) :
    RestrictLe W (finSumIdeal J m) (finSumIdeal J' m) := by
  intro x hx g hg
  refine RelativePrincipalizationSpan.IsInSpanOnAt.trans ?_
    (RelativePrincipalizationSpan.IsInSpanAt.restrict
      (show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem x s) x g from hg))
  rintro s ⟨i, hi, hs⟩
  refine RelativePrincipalizationSpan.IsInSpanOnAt.mono (fun t ht => ?_) (h i hi x hx s hs)
  exact (isInSpanAt_self (S := fun s => ∃ i, i < m ∧ (J' i).mem x s) ⟨i, hi, ht⟩ (hJ' i hi x t ht) :
    IsInSpanAt (n := n) _ x t)

/-- Pullbacks commute with finite sums (`m ≥ 1`; only the members `i < m` are assumed coherent). -/
theorem pullback_finSumIdeal_of_lt {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
    [IsComplexManifold n M'] {f : M' → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {J : ℕ → GermIdeal n M} {m : ℕ} (hm : 1 ≤ m) (hJ : ∀ i < m, (J i).IsCoherent) :
    GermIdeal.pullback (m := n) f (finSumIdeal J m) =
      finSumIdeal (fun i => GermIdeal.pullback (m := n) f (J i)) m := by
  classical
  set J' : ℕ → GermIdeal n M := fun i => if i < m then J i else J 0 with hJ'def
  have hJ' : ∀ i, (J' i).IsCoherent := fun i => by
    by_cases hi : i < m
    · simp only [hJ'def, if_pos hi]; exact hJ i hi
    · simp only [hJ'def, if_neg hi]; exact hJ 0 hm
  have e1 : finSumIdeal J m = finSumIdeal J' m := finSumIdeal_congr fun i hi => by simp [hJ'def, hi]
  have e2 : finSumIdeal (fun i => GermIdeal.pullback (m := n) f (J i)) m =
      finSumIdeal (fun i => GermIdeal.pullback (m := n) f (J' i)) m :=
    finSumIdeal_congr fun i hi => by simp [hJ'def, hi]
  rw [e1, e2]
  exact HomogenizedEtale.pullback_finSumIdeal hf hJ' hm

/-- **`𝔩 ∑ᵢ 𝔎ᵢ = ∑ᵢ 𝔩 𝔎ᵢ`** (`m ≥ 1`, coherent ideals). -/
theorem mul_finSumIdeal {𝔩 : GermIdeal n M} (h𝔩 : 𝔩.IsCoherent) {K : ℕ → GermIdeal n M} :
    ∀ {m : ℕ}, 1 ≤ m → (∀ i < m, (K i).IsCoherent) →
      𝔩.mul (finSumIdeal K m) = finSumIdeal (fun i => 𝔩.mul (K i)) m
  | 0, h, _ => absurd h (by omega)
  | 1, _, hK => by
    rw [finSumIdeal_one (hK 0 Nat.one_pos),
      finSumIdeal_one (J := fun i => 𝔩.mul (K i)) (isCoherent_mul h𝔩 (hK 0 Nat.one_pos))]
  | m + 2, _, hK => by
    have hK' : ∀ i < m + 1, (K i).IsCoherent := fun i hi => hK i (by omega)
    rw [finSumIdeal_succ fun i hi => hK i (by omega),
      MarkedIdealOperationsTransform.mul_sumIdeal (hol_of_isCoherent h𝔩)
        (hol_of_isCoherent (isCoherent_finSumIdeal_of_lt hK')) (hol_of_isCoherent (hK (m + 1) (by omega))),
      mul_finSumIdeal h𝔩 (m := m + 1) (by omega) hK']
    exact (finSumIdeal_succ (J := fun i => 𝔩.mul (K i)) (μ := m + 1) fun i hi =>
      isCoherent_mul h𝔩 (hK i (by omega))).symm

/-- `(𝔞𝔟)(𝔠𝔡) = (𝔞𝔠)(𝔟𝔡)` for coherent ideals. -/
theorem mul_mul_mul_comm' {𝔞 𝔟 𝔠 𝔡 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (h𝔟 : 𝔟.IsCoherent)
    (h𝔠 : 𝔠.IsCoherent) (h𝔡 : 𝔡.IsCoherent) :
    (𝔞.mul 𝔟).mul (𝔠.mul 𝔡) = (𝔞.mul 𝔠).mul (𝔟.mul 𝔡) := by
  rw [GermIdealTotalTransform.mul_assoc h𝔞 h𝔟 (isCoherent_mul h𝔠 h𝔡),
    ← GermIdealTotalTransform.mul_assoc h𝔟 h𝔠 h𝔡, RestrictLeCalculus.mul_comm' 𝔟 𝔠,
    GermIdealTotalTransform.mul_assoc h𝔠 h𝔟 h𝔡, ← GermIdealTotalTransform.mul_assoc h𝔞 h𝔠 (isCoherent_mul h𝔟 h𝔡)]

end Algebra

/-! ### One admissible blowup -/

section OneStep

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  {C : Set M} {π : M' → M}

/-- **The transform along `N` is characterised by its defining equation**: if `Q` is coherent and
`Res_{N'} π^*𝔞 = Res_{N'} (π^*𝓘_C)^d Q`, then the transform of `𝔫 = (M, N, E, 𝔞, d)` is restricted-equivalent to
the transform with ideal replaced by `Q` (`N` a closed submanifold, `𝔞` coherent, `C` admissible; cancellation of the
exceptional ideal, invertible along `N'`). -/
theorem restrictEquiv_geoTransform_of_pullback {𝔫 : MarkedIdeal n M} (hN : IsClosedSubmanifold n 𝔫.N)
    (h𝔞 : 𝔫.ideal.IsCoherent) (hC : 𝔫.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) {Q : GermIdeal n M'}
    (hQ : Q.IsCoherent)
    (h₁ : RestrictLe (geoStrictTransform π C 𝔫.N) (GermIdeal.pullback (m := n) π 𝔫.ideal)
      ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 𝔫.d).mul Q))
    (h₂ : RestrictLe (geoStrictTransform π C 𝔫.N)
      ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 𝔫.d).mul Q)
      (GermIdeal.pullback (m := n) π 𝔫.ideal)) :
    RestrictEquiv (𝔫.geoTransform C π) { 𝔫.geoTransform C π with ideal := Q } := by
  obtain ⟨a1, a2⟩ := restrictLe_pullback_geoTransform hN h𝔞 hC hπ
  have h𝔞' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h𝔞 hC hπ
  have hinv := isInvertibleAlong_geoStrictTransform hπ 𝔫.N 𝔫.d
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · refine RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul h𝔞' hQ hinv ?_
    rw [RestrictLeCalculus.mul_comm' (𝔫.geoTransform C π).ideal, RestrictLeCalculus.mul_comm' Q]
    exact RestrictLeCalculus.RestrictLe.trans a2 h₁
  · refine RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul hQ h𝔞' hinv ?_
    rw [RestrictLeCalculus.mul_comm' (𝔫.geoTransform C π).ideal, RestrictLeCalculus.mul_comm' Q]
    exact RestrictLeCalculus.RestrictLe.trans h₂ a1

/-- **Transforms are monotone along `N`**: `Res_N 𝔞₁ ⊆ Res_N 𝔞₂` gives `Res_{N'} 𝔞₁' ⊆ Res_{N'} 𝔞₂'` for two marked ideals
on the same closed submanifold `N` with the same mark, coherent ideals and `C` admissible for both. -/
theorem restrictLe_geoTransform_of_restrictLe {𝔫₁ 𝔫₂ : MarkedIdeal n M} (hN : IsClosedSubmanifold n 𝔫₁.N)
    (hN₁₂ : 𝔫₁.N = 𝔫₂.N) (hd : 𝔫₁.d = 𝔫₂.d) (h₁ : 𝔫₁.ideal.IsCoherent) (h₂ : 𝔫₂.ideal.IsCoherent)
    (hC₁ : 𝔫₁.IsAdmissibleCentre C) (hC₂ : 𝔫₂.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π)
    (hle : RestrictLe 𝔫₁.N 𝔫₁.ideal 𝔫₂.ideal) :
    RestrictLe (𝔫₁.geoTransform C π).N (𝔫₁.geoTransform C π).ideal (𝔫₂.geoTransform C π).ideal := by
  have hN₂ : IsClosedSubmanifold n 𝔫₂.N := hN₁₂ ▸ hN
  obtain ⟨-, a2⟩ := restrictLe_pullback_geoTransform hN h₁ hC₁ hπ
  obtain ⟨b1, -⟩ := restrictLe_pullback_geoTransform hN₂ h₂ hC₂ hπ
  have hW : (𝔫₂.geoTransform C π).N = (𝔫₁.geoTransform C π).N := by
    rw [geoTransform_N, geoTransform_N, hN₁₂]
  rw [hW, ← hd] at b1
  have h𝔞₁' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h₁ hC₁ hπ
  have h𝔞₂' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN₂ h₂ hC₂ hπ
  have hpb : RestrictLe (𝔫₁.geoTransform C π).N (GermIdeal.pullback (m := n) π 𝔫₁.ideal)
      (GermIdeal.pullback (m := n) π 𝔫₂.ideal) :=
    RestrictLeCalculus.restrictLe_pullback hπ.contMDiff
      (fun _ hy => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy) h₂ hle
  refine RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul h𝔞₁' h𝔞₂'
    (isInvertibleAlong_geoStrictTransform hπ 𝔫₁.N 𝔫₁.d) ?_
  rw [RestrictLeCalculus.mul_comm' (𝔫₁.geoTransform C π).ideal,
    RestrictLeCalculus.mul_comm' (𝔫₂.geoTransform C π).ideal]
  exact RestrictLeCalculus.RestrictLe.trans (RestrictLeCalculus.RestrictLe.trans a2 hpb) b1

/-! #### Włodarczyk's sum of `m` marked ideals on `N` -/

/-- A family `𝔫 0, …, 𝔫 (m - 1)` of marked ideals on one closed submanifold `N`, with a common `E`, coherent ideals and
marks `≥ 1`. -/
structure IsSubmanifoldFamily (𝔫 : ℕ → MarkedIdeal n M) (m : ℕ) : Prop where
  N : ∀ i < m, (𝔫 i).N = (𝔫 0).N
  E : ∀ i < m, (𝔫 i).E = (𝔫 0).E
  closed : IsClosedSubmanifold n (𝔫 0).N
  coh : ∀ i < m, (𝔫 i).ideal.IsCoherent
  d : ∀ i < m, 1 ≤ (𝔫 i).d

theorem IsSubmanifoldFamily.isCoherent_msum {𝔫 : ℕ → MarkedIdeal n M} {m : ℕ} (h : IsSubmanifoldFamily 𝔫 m) :
    (msum 𝔫 m).ideal.IsCoherent :=
  isCoherent_finSumIdeal_of_lt fun i hi => isCoherent_idealPow (h.coh i hi) _

theorem IsSubmanifoldFamily.isClosedSubmanifold {𝔫 : ℕ → MarkedIdeal n M} {m : ℕ} (h : IsSubmanifoldFamily 𝔫 m)
    {i : ℕ} (hi : i < m) : IsClosedSubmanifold n (𝔫 i).N :=
  (h.N i hi).symm ▸ h.closed

/-- **The cosupport of a sum along `N`** is the intersection of the cosupports (marks `≥ 1`). -/
theorem cosupp_msum_along {𝔫 : ℕ → MarkedIdeal n M} {m : ℕ} (h : IsSubmanifoldFamily 𝔫 m) (hm : 1 ≤ m) :
    (msum 𝔫 m).cosupp = {x | ∀ i < m, x ∈ (𝔫 i).cosupp} := by
  ext x
  have hhol : ∀ i < m, ∀ y g,
      (idealPow (𝔫 i).ideal (sumExp (fun j => (𝔫 j).d) m i)).mem y g → HolomorphicAt n g y :=
    fun i _ y g hg => holomorphicAt_of_mem_idealPow hg
  have hpow : ∀ i < m, cosupport n (𝔫 0).N (idealPow (𝔫 i).ideal (sumExp (fun j => (𝔫 j).d) m i))
      ((Finset.range m).prod fun j => (𝔫 j).d) = (𝔫 i).cosupp := fun i hi => by
    have := cosupport_idealPow_mul_eq_along h.closed.2 (hol_of_isCoherent (h.coh i hi))
      (one_le_sumExp (d := fun j => (𝔫 j).d) h.d i) (𝔫 i).d
    rw [mul_sumExp (fun j => (𝔫 j).d) hi] at this
    rw [this, MarkedIdeals.MarkedIdeal.cosupp, h.N i hi]
  show x ∈ cosupport n (𝔫 0).N
    (finSumIdeal (fun i => idealPow (𝔫 i).ideal (sumExp (fun j => (𝔫 j).d) m i)) m)
    ((Finset.range m).prod fun j => (𝔫 j).d) ↔ _
  rw [mem_cosupport_finSumIdeal hhol]
  constructor
  · rintro ⟨-, hx⟩ i hi
    exact hpow i hi ▸ hx i hi
  · intro hx
    refine ⟨(hx 0 hm).1, fun i hi => ?_⟩
    rw [hpow i hi]
    exact hx i hi

/-- **A centre is admissible for a sum along `N` iff it is admissible for every summand.** -/
theorem isAdmissibleCentre_msum_along_iff {𝔫 : ℕ → MarkedIdeal n M} {m : ℕ} (h : IsSubmanifoldFamily 𝔫 m)
    (hm : 1 ≤ m) {C : Set M} : (msum 𝔫 m).IsAdmissibleCentre C ↔ ∀ i < m, (𝔫 i).IsAdmissibleCentre C := by
  rw [IsAdmissibleCentre, cosupp_msum_along h hm]
  constructor
  · rintro ⟨hC, hsub, hnc⟩ i hi
    exact ⟨hC, fun x hx => hsub hx i hi, by rw [h.E i hi]; exact hnc⟩
  · intro hall
    exact ⟨(hall 0 hm).1, fun x hx i hi => (hall i hi).2.1 hx, (hall 0 hm).2.2⟩

/-- **One step of `le:operations` (1) for `m` summands along `N`**: the transform of a sum along `N` is
restricted-equivalent to the sum of the transforms. -/
theorem geoTransform_msum_restrictEquiv {𝔫 : ℕ → MarkedIdeal n M} {m : ℕ} (h : IsSubmanifoldFamily 𝔫 m)
    (hm : 1 ≤ m) (hπ : IsBlowupAlong n C π) (hC : ∀ i < m, (𝔫 i).IsAdmissibleCentre C) :
    RestrictEquiv ((msum 𝔫 m).geoTransform C π) (msum (fun i => (𝔫 i).geoTransform C π) m) := by
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have h𝔩 : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsCoherent :=
    isCoherent_pullback hπ.contMDiff hIC
  have hcoh' : ∀ i < m, ((𝔫 i).geoTransform C π).ideal.IsCoherent := fun i hi =>
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (h.isClosedSubmanifold hi) (h.coh i hi)
      (hC i hi) hπ
  have hCS : (msum 𝔫 m).IsAdmissibleCentre C := (isAdmissibleCentre_msum_along_iff h hm).mpr hC
  have hQcoh : (msum (fun i => (𝔫 i).geoTransform C π) m).ideal.IsCoherent :=
    isCoherent_finSumIdeal_of_lt fun i hi => isCoherent_idealPow (hcoh' i hi) _
  have hW : ∀ i < m, ((𝔫 i).geoTransform C π).N = geoStrictTransform π C (𝔫 0).N := fun i hi => by
    rw [geoTransform_N, h.N i hi]
  have a : ∀ i < m, RestrictLe (geoStrictTransform π C (𝔫 0).N) (GermIdeal.pullback (m := n) π (𝔫 i).ideal)
        ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (𝔫 i).d).mul
          ((𝔫 i).geoTransform C π).ideal) ∧
      RestrictLe (geoStrictTransform π C (𝔫 0).N)
        ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (𝔫 i).d).mul
          ((𝔫 i).geoTransform C π).ideal) (GermIdeal.pullback (m := n) π (𝔫 i).ideal) := fun i hi => by
    have := restrictLe_pullback_geoTransform (h.isClosedSubmanifold hi) (h.coh i hi) (hC i hi) hπ
    rwa [hW i hi] at this
  have e1 : GermIdeal.pullback (m := n) π (msum 𝔫 m).ideal = finSumIdeal (fun i =>
      idealPow (GermIdeal.pullback (m := n) π (𝔫 i).ideal) (sumExp (fun j => (𝔫 j).d) m i)) m := by
    show GermIdeal.pullback (m := n) π
      (finSumIdeal (fun i => idealPow (𝔫 i).ideal (sumExp (fun j => (𝔫 j).d) m i)) m) = _
    rw [pullback_finSumIdeal_of_lt hπ.contMDiff hm (fun i hi => isCoherent_idealPow (h.coh i hi) _)]
    exact finSumIdeal_congr fun i hi => BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff (h.coh i hi) _
  have e2 : (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (msum 𝔫 m).d).mul
      (msum (fun i => (𝔫 i).geoTransform C π) m).ideal = finSumIdeal (fun i =>
        idealPow ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (𝔫 i).d).mul
          ((𝔫 i).geoTransform C π).ideal) (sumExp (fun j => (𝔫 j).d) m i)) m := by
    show (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C))
      ((Finset.range m).prod fun j => (𝔫 j).d)).mul
      (finSumIdeal (fun i => idealPow ((𝔫 i).geoTransform C π).ideal (sumExp (fun j => (𝔫 j).d) m i)) m) = _
    rw [mul_finSumIdeal (isCoherent_idealPow h𝔩 _) hm (fun i hi => isCoherent_idealPow (hcoh' i hi) _)]
    refine finSumIdeal_congr fun i hi => ?_
    rw [BlowupControlledTransform.idealPow_mul (isCoherent_idealPow h𝔩 _) (hcoh' i hi),
      MarkedIdealOperationsTransform.idealPow_idealPow h𝔩, mul_sumExp (fun j => (𝔫 j).d) hi]
  have hpowhol : ∀ (J : ℕ → GermIdeal n M'), ∀ i < m, ∀ x g,
      (idealPow (J i) (sumExp (fun j => (𝔫 j).d) m i)).mem x g → HolomorphicAt n g x :=
    fun _ _ _ _ _ hg => holomorphicAt_of_mem_idealPow hg
  refine restrictEquiv_geoTransform_of_pullback (𝔫 := msum 𝔫 m) h.closed h.isCoherent_msum hCS hπ hQcoh ?_ ?_
  · show RestrictLe (geoStrictTransform π C (msum 𝔫 m).N) (GermIdeal.pullback (m := n) π (msum 𝔫 m).ideal)
      ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (msum 𝔫 m).d).mul
        (msum (fun i => (𝔫 i).geoTransform C π) m).ideal)
    rw [e1, e2]
    exact restrictLe_finSumIdeal (hpowhol _) fun i hi =>
      restrictLe_idealPow (hol_of_isCoherent (isCoherent_mul (isCoherent_idealPow h𝔩 _) (hcoh' i hi)))
        (a i hi).1 _
  · show RestrictLe (geoStrictTransform π C (msum 𝔫 m).N)
      ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (msum 𝔫 m).d).mul
        (msum (fun i => (𝔫 i).geoTransform C π) m).ideal) (GermIdeal.pullback (m := n) π (msum 𝔫 m).ideal)
    rw [e1, e2]
    exact restrictLe_finSumIdeal (hpowhol _) fun i hi =>
      restrictLe_idealPow (hol_of_isCoherent (isCoherent_pullback hπ.contMDiff (h.coh i hi))) (a i hi).2 _

/-- One admissible step keeps a family on `N` a family on the strict transform `N'`. -/
theorem IsSubmanifoldFamily.geoTransform {𝔫 : ℕ → MarkedIdeal n M} {m : ℕ} (h : IsSubmanifoldFamily 𝔫 m)
    (hm : 1 ≤ m) (hπ : IsBlowupAlong n C π) (hC : ∀ i < m, (𝔫 i).IsAdmissibleCentre C) :
    IsSubmanifoldFamily (fun i => (𝔫 i).geoTransform C π) m where
  N i hi := by simp only [geoTransform_N, h.N i hi]
  E i hi := by simp only [geoTransform_E, h.E i hi]
  closed := isClosedSubmanifold_geoTransform_N h.closed (hC 0 hm) hπ
  coh i hi := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (h.isClosedSubmanifold hi)
    (h.coh i hi) (hC i hi) hπ
  d i hi := h.d i hi

/-! #### `∑ᵢ Aᵢ Bⁱ` along `N` -/

/-- Pullbacks commute with `∑ᵢ Aᵢ Bⁱ` (`μ ≥ 1`; only the `Aᵢ`, `i < μ`, are assumed coherent). -/
theorem pullback_homSum_of_lt {f : M' → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {A : ℕ → GermIdeal n M} {B : GermIdeal n M} {μ : ℕ} (hμ : 1 ≤ μ) (hA : ∀ i < μ, (A i).IsCoherent)
    (hB : B.IsCoherent) :
    GermIdeal.pullback (m := n) f (homSum A B μ) =
      homSum (fun i => GermIdeal.pullback (m := n) f (A i)) (GermIdeal.pullback (m := n) f B) μ := by
  unfold homSum
  rw [pullback_finSumIdeal_of_lt hf hμ (fun i hi => isCoherent_mul (hA i hi) (isCoherent_idealPow hB i))]
  refine finSumIdeal_congr fun i hi => ?_
  rw [GermIdealTotalTransform.pullback_mul hf (hA i hi) (isCoherent_idealPow hB i),
    BlowupExceptionalDivisor.pullback_idealPow hf hB]

/-- **Restricted inclusions pass to `∑ᵢ Aᵢ Bⁱ`.** -/
theorem restrictLe_homSum {W : Set M} {A A' : ℕ → GermIdeal n M} {B B' : GermIdeal n M} {μ : ℕ}
    (hA' : ∀ i < μ, ∀ x g, (A' i).mem x g → HolomorphicAt n g x) (hB' : ∀ x g, B'.mem x g → HolomorphicAt n g x)
    (hA : ∀ i < μ, RestrictLe W (A i) (A' i)) (hB : RestrictLe W B B') :
    RestrictLe W (homSum A B μ) (homSum A' B' μ) :=
  restrictLe_finSumIdeal (fun _ _ _ _ hg => (InvertibleIdealQuotient.mem_mul_iff.mp hg).1) fun i hi =>
    restrictLe_mul (hA' i hi) (fun _ _ hg => holomorphicAt_of_mem_idealPow hg) (hA i hi) (restrictLe_idealPow hB' hB i)

/-- **The transform of `∑ᵢ Aᵢ Bⁱ` along `N`** (one admissible blowup): let `𝔄ᵢ` (`i < μ`, mark `μ - i`) and `𝔅` (mark
`1`) be marked ideals on the closed submanifold `N` of `𝔥` with coherent ideals and `C` admissible for all of them,
and let `𝔥` have mark `μ`, ideal `∑ᵢ 𝔄ᵢ 𝔅ⁱ` and `C` admissible. Then `𝔥' ≃ ∑ᵢ 𝔄ᵢ' 𝔅'ⁱ` (restricted equivalence: on
`N'`, `σ(∑ᵢ Aᵢ Bⁱ, μ) = ∑ᵢ σ(Aᵢ, μ - i) σ(B, 1)ⁱ`). -/
theorem geoTransform_homSum_restrictEquiv {𝔄 : ℕ → MarkedIdeal n M} {𝔅 𝔥 : MarkedIdeal n M} {μ : ℕ} (hμ : 1 ≤ μ)
    (hN : IsClosedSubmanifold n 𝔥.N) (hNA : ∀ i < μ, (𝔄 i).N = 𝔥.N) (hNB : 𝔅.N = 𝔥.N)
    (hdA : ∀ i < μ, (𝔄 i).d = μ - i) (hdB : 𝔅.d = 1) (hdH : 𝔥.d = μ)
    (hA : ∀ i < μ, (𝔄 i).ideal.IsCoherent) (hB : 𝔅.ideal.IsCoherent)
    (hH : 𝔥.ideal = homSum (fun i => (𝔄 i).ideal) 𝔅.ideal μ)
    (hCA : ∀ i < μ, (𝔄 i).IsAdmissibleCentre C) (hCB : 𝔅.IsAdmissibleCentre C) (hCH : 𝔥.IsAdmissibleCentre C)
    (hπ : IsBlowupAlong n C π) :
    RestrictEquiv (𝔥.geoTransform C π)
      { 𝔥.geoTransform C π with
        ideal := homSum (fun i => ((𝔄 i).geoTransform C π).ideal) (𝔅.geoTransform C π).ideal μ } := by
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have h𝔩 : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsCoherent :=
    isCoherent_pullback hπ.contMDiff hIC
  set 𝔩 := GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) with h𝔩def
  have hNA' : ∀ i < μ, IsClosedSubmanifold n (𝔄 i).N := fun i hi => (hNA i hi).symm ▸ hN
  have hNB' : IsClosedSubmanifold n 𝔅.N := hNB.symm ▸ hN
  have hA' : ∀ i < μ, ((𝔄 i).geoTransform C π).ideal.IsCoherent := fun i hi =>
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (hNA' i hi) (hA i hi) (hCA i hi) hπ
  have hB' : (𝔅.geoTransform C π).ideal.IsCoherent :=
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNB' hB hCB hπ
  have hHcoh : 𝔥.ideal.IsCoherent := by rw [hH]; exact isCoherent_homSum hA hB
  have hQcoh := isCoherent_homSum hA' hB'
  have a : ∀ i < μ, RestrictLe (geoStrictTransform π C 𝔥.N) (GermIdeal.pullback (m := n) π (𝔄 i).ideal)
        ((idealPow 𝔩 (μ - i)).mul ((𝔄 i).geoTransform C π).ideal) ∧
      RestrictLe (geoStrictTransform π C 𝔥.N) ((idealPow 𝔩 (μ - i)).mul ((𝔄 i).geoTransform C π).ideal)
        (GermIdeal.pullback (m := n) π (𝔄 i).ideal) := fun i hi => by
    have := restrictLe_pullback_geoTransform (hNA' i hi) (hA i hi) (hCA i hi) hπ
    rwa [geoTransform_N, hNA i hi, hdA i hi] at this
  have b : RestrictLe (geoStrictTransform π C 𝔥.N) (GermIdeal.pullback (m := n) π 𝔅.ideal)
        ((idealPow 𝔩 1).mul (𝔅.geoTransform C π).ideal) ∧
      RestrictLe (geoStrictTransform π C 𝔥.N) ((idealPow 𝔩 1).mul (𝔅.geoTransform C π).ideal)
        (GermIdeal.pullback (m := n) π 𝔅.ideal) := by
    have := restrictLe_pullback_geoTransform hNB' hB hCB hπ
    rwa [geoTransform_N, hNB, hdB] at this
  have e1 : GermIdeal.pullback (m := n) π 𝔥.ideal =
      homSum (fun i => GermIdeal.pullback (m := n) π (𝔄 i).ideal) (GermIdeal.pullback (m := n) π 𝔅.ideal) μ := by
    rw [hH]; exact pullback_homSum_of_lt hπ.contMDiff hμ hA hB
  have e2 : (idealPow 𝔩 𝔥.d).mul (homSum (fun i => ((𝔄 i).geoTransform C π).ideal) (𝔅.geoTransform C π).ideal μ) =
      homSum (fun i => (idealPow 𝔩 (μ - i)).mul ((𝔄 i).geoTransform C π).ideal)
        ((idealPow 𝔩 1).mul (𝔅.geoTransform C π).ideal) μ := by
    rw [hdH]
    unfold homSum
    rw [mul_finSumIdeal (isCoherent_idealPow h𝔩 _) hμ
      (fun i hi => isCoherent_mul (hA' i hi) (isCoherent_idealPow hB' i))]
    refine finSumIdeal_congr fun i hi => ?_
    rw [BlowupControlledTransform.idealPow_mul (isCoherent_idealPow h𝔩 1) hB',
      MarkedIdealOperationsTransform.idealPow_idealPow h𝔩,
      mul_mul_mul_comm' (isCoherent_idealPow h𝔩 _) (hA' i hi) (isCoherent_idealPow h𝔩 _) (isCoherent_idealPow hB' i),
      ← RestrictLeCalculus.idealPow_add h𝔩, one_mul, Nat.sub_add_cancel hi.le]
  have hmulhol : ∀ (P : ℕ → GermIdeal n M'), ∀ i < μ, ∀ x g,
      ((idealPow 𝔩 (μ - i)).mul (P i)).mem x g → HolomorphicAt n g x :=
    fun _ _ _ _ _ hg => (InvertibleIdealQuotient.mem_mul_iff.mp hg).1
  refine restrictEquiv_geoTransform_of_pullback hN hHcoh hCH hπ hQcoh ?_ ?_
  · rw [e1, e2]
    exact restrictLe_homSum (hmulhol _) (fun _ _ hg => (InvertibleIdealQuotient.mem_mul_iff.mp hg).1)
      (fun i hi => (a i hi).1) b.1
  · rw [e1, e2]
    exact restrictLe_homSum (fun i hi => hol_of_isCoherent (isCoherent_pullback hπ.contMDiff (hA i hi)))
      (hol_of_isCoherent (isCoherent_pullback hπ.contMDiff hB)) (fun i hi => (a i hi).2) b.2

end OneStep

/-! ### Along multiple test blow-ups -/

section Tower

open MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal

variable {n : ℕ} {X : CMfd.{u} n}

/-- `𝓓_N^0(𝔪) = 𝔪`. -/
theorem derivMarkedAlong_zero {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    (𝔪 : MarkedIdeal n M) : derivMarkedAlong 𝔪 0 = 𝔪 := by
  cases 𝔪; rfl

/-- **`le:inclusions` along a multiple test blow-up, along `N`** (Włodarczyk 2005, Lemma `le:inclusions`, iterated; for
the ideal `𝔞|_N ⊆ 𝒪_N`): for `𝔪 = (X, N, E, 𝔞, d)` with `N` a closed submanifold, `𝔞` coherent and `j ≤ d`, every multiple
test blow-up `T` of `𝔪` is one of `𝓓_N^j(𝔪)`, the transforms keep the same `N` and `E`, `N_T` is a closed submanifold,
both transforms are coherent, and on `N_T`

  `[𝓓_N^j(𝔪)]_T ⊆ 𝓓_{N_T}^j(𝔪_T)`.

Induction on `T`: the centre is admissible for `[𝓓_N^j 𝔪]_T` (Giraud along `N_T`, then the inclusion), the transform
is monotone along `N` (`restrictLe_geoTransform_of_restrictLe`), and one step is item (2)
(`DerivativeIdealAlongTransform.restrictLe_geoTransform_derivMarkedAlong`). -/
theorem inclusions_tower_along (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    {j : ℕ} (hj : j ≤ 𝔪.d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      IsGeoTestTower (derivMarkedAlong 𝔪 j) T ∧
      (geoTransformAlong (derivMarkedAlong 𝔪 j) T).N = (geoTransformAlong 𝔪 T).N ∧
      (geoTransformAlong (derivMarkedAlong 𝔪 j) T).E = (geoTransformAlong 𝔪 T).E ∧
      IsClosedSubmanifold n (geoTransformAlong 𝔪 T).N ∧
      (geoTransformAlong 𝔪 T).ideal.IsCoherent ∧
      (geoTransformAlong (derivMarkedAlong 𝔪 j) T).ideal.IsCoherent ∧
      RestrictLe (geoTransformAlong 𝔪 T).N (geoTransformAlong (derivMarkedAlong 𝔪 j) T).ideal
        (iterDerivIdealAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal j)
  | _, .refl => fun _ => ⟨trivial, rfl, rfl, hN, h𝔞, isCoherent_iterDerivIdealAlong h𝔞 hN j,
      RestrictLeCalculus.restrictLe_refl (isCoherent_iterDerivIdealAlong h𝔞 hN j)⟩
  | _, .step T C π hπ => fun hT => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hD, hNeq, hE, hNT, hcoh, hcohD, hle⟩ := inclusions_tower_along 𝔪 hN h𝔞 hj T hT0
      have hd : (geoTransformAlong 𝔪 T).d = 𝔪.d := d_geoTransformAlong 𝔪 T
      have hdD : (geoTransformAlong (derivMarkedAlong 𝔪 j) T).d = 𝔪.d - j := d_geoTransformAlong _ T
      -- Giraud along `N_T`: `cosupp 𝔪_T ⊆ cosupp(𝓓_{N_T}^j 𝔪_T, d - j)`
      have hgir : (geoTransformAlong 𝔪 T).cosupp ⊆ cosupport n (geoTransformAlong 𝔪 T).N
          (iterDerivIdealAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal j) (𝔪.d - j) := by
        intro y hy
        have h1 : y ∈ cosupport n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal ((𝔪.d - j) + j) := by
          rw [Nat.sub_add_cancel hj, ← hd]; exact hy
        exact TangentDirectionAlong.cosupport_add_subset_cosupport_iterDerivIdealAlong (hol_of_isCoherent hcoh)
          (𝔪.d - j) j h1
      -- the centre is admissible for `[𝓓_N^j 𝔪]_T` and for `𝓓_{N_T}^j(𝔪_T)`
      have hCD : (geoTransformAlong (derivMarkedAlong 𝔪 j) T).IsAdmissibleCentre C := by
        refine ⟨hC.1, fun y hy => ?_, by rw [hE]; exact hC.2.2⟩
        show y ∈ cosupport n (geoTransformAlong (derivMarkedAlong 𝔪 j) T).N
          (geoTransformAlong (derivMarkedAlong 𝔪 j) T).ideal (geoTransformAlong (derivMarkedAlong 𝔪 j) T).d
        rw [hNeq, hdD]
        exact cosupport_subset_of_restrictLe hle _ (hgir (hC.2.1 hy))
      have hCD' : (derivMarkedAlong (geoTransformAlong 𝔪 T) j).IsAdmissibleCentre C := by
        refine ⟨hC.1, fun y hy => ?_, hC.2.2⟩
        show y ∈ cosupport n (geoTransformAlong 𝔪 T).N
          (iterDerivIdealAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal j)
          ((geoTransformAlong 𝔪 T).d - j)
        rw [hd]
        exact hgir (hC.2.1 hy)
      have hcohD' := isCoherent_iterDerivIdealAlong hcoh hNT j
      -- monotonicity of the transform along `N_T`, then item (2)
      have h1 := restrictLe_geoTransform_of_restrictLe (𝔫₁ := geoTransformAlong (derivMarkedAlong 𝔪 j) T)
        (𝔫₂ := derivMarkedAlong (geoTransformAlong 𝔪 T) j) (hNeq ▸ hNT) hNeq
        (by rw [hdD, derivMarkedAlong_d, hd]) hcohD hcohD' hCD hCD' hπ (by rw [hNeq]; exact hle)
      have h2 := DerivativeIdealAlongTransform.restrictLe_geoTransform_derivMarkedAlong (geoTransformAlong 𝔪 T)
        hNT hcoh hC hπ (j := j) (by rw [hd]; exact hj)
      have hW : ((geoTransformAlong (derivMarkedAlong 𝔪 j) T).geoTransform C π).N =
          geoStrictTransform π C (geoTransformAlong 𝔪 T).N := by
        rw [geoTransform_N, hNeq]
      rw [hW] at h1
      refine ⟨(isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hD, hCD⟩, ?_, ?_,
        isClosedSubmanifold_geoTransform_N hNT hC hπ,
        HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT hcoh hC hπ,
        HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (hNeq ▸ hNT) hcohD hCD hπ,
        RestrictLeCalculus.RestrictLe.trans h1 h2⟩
      · show geoStrictTransform π C (geoTransformAlong (derivMarkedAlong 𝔪 j) T).N =
          geoStrictTransform π C (geoTransformAlong 𝔪 T).N
        rw [hNeq]
      · show ((geoTransformAlong (derivMarkedAlong 𝔪 j) T).geoTransform C π).E =
          ((geoTransformAlong 𝔪 T).geoTransform C π).E
        rw [geoTransform_E, geoTransform_E, hE]

/-- Along a multiple test blow-up of `𝔪`, the cosupport of `𝔪_T` lies in that of `[𝓓_N^i 𝔪]_T` (mark `d - i`). -/
theorem mem_cosupp_derivMarkedAlong_tower (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {Y : CMfd.{u} n} {T : BlowupTower X Y} (hT : IsGeoTestTower 𝔪 T) {i : ℕ}
    (hi : i ≤ 𝔪.d) {x : Y} (hx : x ∈ (geoTransformAlong 𝔪 T).cosupp) :
    x ∈ (geoTransformAlong (derivMarkedAlong 𝔪 i) T).cosupp := by
  obtain ⟨-, hNeq, -, -, hcoh, -, hle⟩ := inclusions_tower_along 𝔪 hN h𝔞 hi T hT
  show x ∈ cosupport n (geoTransformAlong (derivMarkedAlong 𝔪 i) T).N
    (geoTransformAlong (derivMarkedAlong 𝔪 i) T).ideal (geoTransformAlong (derivMarkedAlong 𝔪 i) T).d
  rw [hNeq, d_geoTransformAlong, derivMarkedAlong_d]
  refine cosupport_subset_of_restrictLe hle _ ?_
  have h1 : x ∈ cosupport n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal ((𝔪.d - i) + i) := by
    rw [Nat.sub_add_cancel hi, ← d_geoTransformAlong 𝔪 T]; exact hx
  exact TangentDirectionAlong.cosupport_add_subset_cosupport_iterDerivIdealAlong (hol_of_isCoherent hcoh) _ i h1

/-! #### Włodarczyk's sum of `m` marked ideals on `N`, along towers -/

/-- **Włodarczyk `le:operations` (1) for `m ≥ 1` summands along `N`** (one closed submanifold `N`, common `E`, coherent
ideals, marks `≥ 1`): the multiple test blow-ups of `𝔫 0 + … + 𝔫 (m - 1)` are exactly the simultaneous multiple test
blow-ups of the `𝔫 i`, and along them the transform of the sum is restricted-equivalent to the sum of the
transforms. -/
theorem geoTransformAlong_msum_along (𝔫 : ℕ → MarkedIdeal n X) {m : ℕ} (hm : 1 ≤ m)
    (h : IsSubmanifoldFamily 𝔫 m) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (IsGeoTestTower (msum 𝔫 m) T ↔ ∀ i < m, IsGeoTestTower (𝔫 i) T) ∧
      ((∀ i < m, IsGeoTestTower (𝔫 i) T) →
        RestrictEquiv (geoTransformAlong (msum 𝔫 m) T) (msum (fun i => geoTransformAlong (𝔫 i) T) m) ∧
        (geoTransformAlong (msum 𝔫 m) T).ideal.IsCoherent ∧
        IsSubmanifoldFamily (fun i => geoTransformAlong (𝔫 i) T) m)
  | _, .refl => ⟨by simp [IsGeoTestTower], fun _ => ⟨RestrictEquiv.refl h.isCoherent_msum, h.isCoherent_msum, h⟩⟩
  | _, .step T C π hπ => by
      obtain ⟨ihT, ihE⟩ := geoTransformAlong_msum_along 𝔫 hm h T
      refine ⟨?_, fun hall => ?_⟩
      · simp only [isGeoTestTower_step_iff]
        constructor
        · rintro ⟨hT, hC⟩
          have hTi := ihT.mp hT
          obtain ⟨heq, -, hfam⟩ := ihE hTi
          rw [heq.isAdmissibleCentre_iff, isAdmissibleCentre_msum_along_iff hfam hm] at hC
          exact fun i hi => ⟨hTi i hi, hC i hi⟩
        · intro hall
          have hTi : ∀ i < m, IsGeoTestTower (𝔫 i) T := fun i hi => (hall i hi).1
          obtain ⟨heq, -, hfam⟩ := ihE hTi
          refine ⟨ihT.mpr hTi, ?_⟩
          rw [heq.isAdmissibleCentre_iff, isAdmissibleCentre_msum_along_iff hfam hm]
          exact fun i hi => (hall i hi).2
      · have hTi : ∀ i < m, IsGeoTestTower (𝔫 i) T := fun i hi =>
          ((isGeoTestTower_step_iff (𝔫 i) T C π hπ).mp (hall i hi)).1
        have hCi : ∀ i < m, (geoTransformAlong (𝔫 i) T).IsAdmissibleCentre C := fun i hi =>
          ((isGeoTestTower_step_iff (𝔫 i) T C π hπ).mp (hall i hi)).2
        obtain ⟨heq, hcoh, hfam⟩ := ihE hTi
        have hCS : (msum (fun i => geoTransformAlong (𝔫 i) T) m).IsAdmissibleCentre C :=
          (isAdmissibleCentre_msum_along_iff hfam hm).mpr hCi
        have hNT : IsClosed (geoTransformAlong (msum 𝔫 m) T).N := by
          rw [heq.N_eq]; exact hfam.closed.1
        have hstep : geoTransformAlong (msum 𝔫 m) (.step T C π hπ) =
            (msum (fun i => geoTransformAlong (𝔫 i) T) m).geoTransform C π := by
          rw [geoTransformAlong_step]
          exact heq.geoTransform_eq hNT hcoh hfam.isCoherent_msum hπ.contMDiff
        refine ⟨?_, ?_, hfam.geoTransform hm hπ hCi⟩
        · rw [hstep]; exact geoTransform_msum_restrictEquiv hfam hm hπ hCi
        · rw [hstep]
          exact HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hfam.closed
            hfam.isCoherent_msum hCS hπ

/-! #### The coefficient ideal along `N` -/

/-- The derivatives along `N`, `𝓓_N^i(𝔪)` (`i < d`), form a family on `N`. -/
theorem isSubmanifoldFamily_derivMarkedAlong {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {𝔪 : MarkedIdeal n M} (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) :
    IsSubmanifoldFamily (fun i => derivMarkedAlong 𝔪 i) 𝔪.d where
  N _ _ := rfl
  E _ _ := rfl
  closed := hN
  coh i _ := isCoherent_iterDerivIdealAlong h𝔞 hN i
  d i hi := by simp only [derivMarkedAlong_d]; omega

/-- **Włodarczyk, Lemma `le:coeff`, along `N`** (`N` a closed submanifold, `𝔞` coherent, `d ≥ 1`): a tower is a multiple
test blow-up of `𝓒_N(𝔪)` iff it is one of `𝔪`, and along it the cosupports of the transforms agree. -/
theorem coeffAlong_tower (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (IsGeoTestTower (coeffMarkedAlong 𝔪) T ↔ IsGeoTestTower 𝔪 T) ∧
      (IsGeoTestTower 𝔪 T →
        (geoTransformAlong (coeffMarkedAlong 𝔪) T).cosupp = (geoTransformAlong 𝔪 T).cosupp) := by
  have hfam := isSubmanifoldFamily_derivMarkedAlong hN h𝔞
  obtain ⟨hiff, heq⟩ := geoTransformAlong_msum_along (fun i => derivMarkedAlong 𝔪 i) hd hfam T
  have hall : IsGeoTestTower 𝔪 T → ∀ i < 𝔪.d, IsGeoTestTower (derivMarkedAlong 𝔪 i) T :=
    fun hT i hi => (inclusions_tower_along 𝔪 hN h𝔞 hi.le T hT).1
  refine ⟨⟨fun hC => ?_, fun hT => (show IsGeoTestTower (msum _ _) T from hiff.mpr (hall hT))⟩, fun hT => ?_⟩
  · have := hiff.mp hC 0 hd
    rwa [derivMarkedAlong_zero] at this
  · obtain ⟨he, -, hfamT⟩ := heq (hall hT)
    rw [show coeffMarkedAlong 𝔪 = msum (fun i => derivMarkedAlong 𝔪 i) 𝔪.d from rfl, he.cosupp_eq,
      cosupp_msum_along hfamT hd]
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hx
      have := hx 0 hd
      rwa [derivMarkedAlong_zero] at this
    · intro hx i hi
      exact mem_cosupp_derivMarkedAlong_tower 𝔪 hN h𝔞 hT hi.le hx

/-- **Włodarczyk `le:coeff` as an equivalence, along `N`: `𝓒_N(𝔪) ≃ 𝔪`** (`MarkedIdealEquivalence.WEquiv`; `N` a closed
submanifold, `𝔞` coherent, `d ≥ 1`). -/
theorem coeffAlong_wEquiv (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) : WEquiv (coeffMarkedAlong 𝔪) 𝔪 :=
  ⟨rfl, fun T => ⟨(coeffAlong_tower 𝔪 hN h𝔞 hd T).1,
    fun hT => (coeffAlong_tower 𝔪 hN h𝔞 hd T).2 ((coeffAlong_tower 𝔪 hN h𝔞 hd T).1.mp hT)⟩⟩

/-! #### The homogenized ideal along `N` -/

/-- **The expected transform of `𝓗_N(𝔪)` along `T`**: the transform `𝔪_T` with ideal
`∑_{i<d} [𝓓_N^i 𝔪]_T · [T_N(𝔪)]_Tⁱ`, `T_N(𝔪) = 𝓓_N^{d-1}(𝔪)`. -/
def homTower (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) : MarkedIdeal n Y :=
  { geoTransformAlong 𝔪 T with
    ideal := homSum (fun i => (geoTransformAlong (derivMarkedAlong 𝔪 i) T).ideal)
      (geoTransformAlong (derivMarkedAlong 𝔪 (𝔪.d - 1)) T).ideal 𝔪.d }

/-- **Along a multiple test blow-up of `𝔪`, the expected transform of `𝓗_N(𝔪)` has the cosupport of `𝔪_T`**: the term
`i = 0` is `𝔪_T`, and on `cosupp 𝔪_T` the order of `[𝓓_N^i 𝔪]_T` along `N_T` is `≥ d - i`
(`mem_cosupp_derivMarkedAlong_tower`), so that of the sum is `≥ d` (`HomogenizedEquivalence.orderGE_homSum`). -/
theorem cosupp_homTower (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} {T : BlowupTower X Y} (hT : IsGeoTestTower 𝔪 T) :
    (homTower 𝔪 T).cosupp = (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨-, -, -, -, -, hcoh0, -⟩ := inclusions_tower_along 𝔪 hN h𝔞 (Nat.zero_le 𝔪.d) T hT
  have h0 : geoTransformAlong (derivMarkedAlong 𝔪 0) T = geoTransformAlong 𝔪 T := by
    rw [derivMarkedAlong_zero]
  have hord : ∀ i ≤ 𝔪.d, ∀ x ∈ (geoTransformAlong 𝔪 T).cosupp,
      OrderGE n (geoTransformAlong 𝔪 T).N (geoTransformAlong (derivMarkedAlong 𝔪 i) T).ideal x (𝔪.d - i) := by
    intro i hi x hx
    obtain ⟨-, hNeq, -⟩ := inclusions_tower_along 𝔪 hN h𝔞 hi T hT
    have h := mem_cosupp_derivMarkedAlong_tower 𝔪 hN h𝔞 hT hi hx
    have h' : x ∈ cosupport n (geoTransformAlong 𝔪 T).N (geoTransformAlong (derivMarkedAlong 𝔪 i) T).ideal
        (𝔪.d - i) := by
      have := h
      unfold MarkedIdeals.MarkedIdeal.cosupp at this
      rwa [hNeq, d_geoTransformAlong, derivMarkedAlong_d] at this
    exact h'.2
  refine Subset.antisymm ?_ ?_
  · intro x hx
    have hle : (geoTransformAlong (derivMarkedAlong 𝔪 0) T).ideal.Le (homTower 𝔪 T).ideal :=
      le_homSum (A := fun i => (geoTransformAlong (derivMarkedAlong 𝔪 i) T).ideal)
        (B := (geoTransformAlong (derivMarkedAlong 𝔪 (𝔪.d - 1)) T).ideal) hd (hol_of_isCoherent hcoh0)
    rw [h0] at hle
    exact DerivativeIdealTower.cosupport_subset_of_le hle _ hx
  · intro x hx
    refine ⟨hx.1, ?_⟩
    show OrderGE n (geoTransformAlong 𝔪 T).N (homTower 𝔪 T).ideal x (geoTransformAlong 𝔪 T).d
    rw [d_geoTransformAlong]
    refine orderGE_homSum (fun i hi => hord i hi.le x hx) ?_
    have := hord (𝔪.d - 1) (by omega) x hx
    rwa [show 𝔪.d - (𝔪.d - 1) = 1 by omega] at this

/-- **The transform of the homogenized ideal along `N` along a multiple test blow-up** (`N` a closed submanifold, `𝔞`
coherent, `d ≥ 1`): every multiple test blow-up `T` of `𝔪` is one of `𝓗_N(𝔪)`, `𝓗_N(𝔪)_T` is coherent, and

  `𝓗_N(𝔪)_T ≃ (𝔪_T with ideal ∑_{i<d} [𝓓_N^i 𝔪]_T · [T_N(𝔪)]_Tⁱ)` (restricted equivalence, `homTower`).
-/
theorem hom_tower_along (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      IsGeoTestTower (homMarkedAlong 𝔪) T ∧ (geoTransformAlong (homMarkedAlong 𝔪) T).ideal.IsCoherent ∧
      RestrictEquiv (geoTransformAlong (homMarkedAlong 𝔪) T) (homTower 𝔪 T)
  | _, .refl => fun _ => ⟨trivial, isCoherent_homMarkedAlong h𝔞 hN,
      RestrictEquiv.refl (isCoherent_homMarkedAlong h𝔞 hN)⟩
  | _, .step T C π hπ => fun hT => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hHT, hcohH, hEq⟩ := hom_tower_along 𝔪 hN h𝔞 hd T hT0
      have hDi : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarkedAlong 𝔪 i) T).N = (geoTransformAlong 𝔪 T).N ∧
          (geoTransformAlong (derivMarkedAlong 𝔪 i) T).ideal.IsCoherent ∧
          (geoTransformAlong (derivMarkedAlong 𝔪 i) T).IsAdmissibleCentre C := fun i hi => by
        obtain ⟨hDstep, -⟩ := inclusions_tower_along 𝔪 hN h𝔞 hi (.step T C π hπ) hT
        obtain ⟨-, hCD⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hDstep
        obtain ⟨-, hNeq, -, -, -, hcohD, -⟩ := inclusions_tower_along 𝔪 hN h𝔞 hi T hT0
        exact ⟨hNeq, hcohD, hCD⟩
      obtain ⟨-, -, -, hNT, -, -, -⟩ := inclusions_tower_along 𝔪 hN h𝔞 (Nat.zero_le 𝔪.d) T hT0
      have hXcoh : (homTower 𝔪 T).ideal.IsCoherent :=
        isCoherent_homSum (fun i hi => (hDi i hi.le).2.1) (hDi (𝔪.d - 1) (by omega)).2.1
      have hCX : (homTower 𝔪 T).IsAdmissibleCentre C := by
        refine ⟨hC.1, ?_, hC.2.2⟩
        rw [cosupp_homTower 𝔪 hN h𝔞 hd hT0]
        exact hC.2.1
      have hCH : (geoTransformAlong (homMarkedAlong 𝔪) T).IsAdmissibleCentre C :=
        hEq.isAdmissibleCentre_iff.mpr hCX
      have hNX : IsClosed (geoTransformAlong (homMarkedAlong 𝔪) T).N := by
        rw [hEq.N_eq]; exact hNT.1
      have hstep : geoTransformAlong (homMarkedAlong 𝔪) (.step T C π hπ) = (homTower 𝔪 T).geoTransform C π := by
        rw [geoTransformAlong_step]
        exact hEq.geoTransform_eq hNX hcohH hXcoh hπ.contMDiff
      refine ⟨(isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hHT, hCH⟩, ?_, ?_⟩
      · rw [hstep]
        exact HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT hXcoh hCX hπ
      · rw [hstep]
        exact geoTransform_homSum_restrictEquiv (𝔄 := fun i => geoTransformAlong (derivMarkedAlong 𝔪 i) T)
          (𝔅 := geoTransformAlong (derivMarkedAlong 𝔪 (𝔪.d - 1)) T) (𝔥 := homTower 𝔪 T) hd hNT
          (fun i hi => (hDi i hi.le).1) (hDi (𝔪.d - 1) (by omega)).1
          (fun i _ => by simp only [d_geoTransformAlong, derivMarkedAlong_d])
          (by simp only [d_geoTransformAlong, derivMarkedAlong_d]; omega) (d_geoTransformAlong 𝔪 T)
          (fun i hi => (hDi i hi.le).2.1) (hDi (𝔪.d - 1) (by omega)).2.1 rfl
          (fun i hi => (hDi i hi.le).2.2) (hDi (𝔪.d - 1) (by omega)).2.2 hCX hπ

/-- A multiple test blow-up of `𝓗_N(𝔪)` is one of `𝔪`. -/
theorem isGeoTestTower_of_homAlong (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower (homMarkedAlong 𝔪) T → IsGeoTestTower 𝔪 T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
      have hTm := isGeoTestTower_of_homAlong 𝔪 hN h𝔞 hd T hT0
      obtain ⟨-, -, hEq⟩ := hom_tower_along 𝔪 hN h𝔞 hd T hTm
      have hCX := hEq.isAdmissibleCentre_iff.mp hC
      refine (isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hTm, hCX.1, ?_, hCX.2.2⟩
      rw [← cosupp_homTower 𝔪 hN h𝔞 hd hTm]
      exact hCX.2.1

/-- **Włodarczyk: `(𝓗(𝓘), μ) ≃ (𝓘, μ)` along `N`** (the lemma after `le:hom`, for `𝓗_N`; `N` a closed submanifold, `𝔞`
coherent, `d ≥ 1`): `𝓗_N(𝔪) ≃ 𝔪` (`MarkedIdealEquivalence.WEquiv`). -/
theorem homAlong_wEquiv (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) : WEquiv (homMarkedAlong 𝔪) 𝔪 := by
  refine ⟨rfl, fun T => ⟨⟨isGeoTestTower_of_homAlong 𝔪 hN h𝔞 hd T,
    fun hT => (hom_tower_along 𝔪 hN h𝔞 hd T hT).1⟩, fun hTH => ?_⟩⟩
  have hT := isGeoTestTower_of_homAlong 𝔪 hN h𝔞 hd T hTH
  obtain ⟨-, -, hEq⟩ := hom_tower_along 𝔪 hN h𝔞 hd T hT
  rw [hEq.cosupp_eq, cosupp_homTower 𝔪 hN h𝔞 hd hT]

/-- **`𝓒_N(𝓗_N(𝔪)) ≃ 𝔪`** (`N` a closed submanifold, `𝔞` coherent, `d ≥ 1`). -/
theorem coeff_homAlong_wEquiv (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) : WEquiv (coeffMarkedAlong (homMarkedAlong 𝔪)) 𝔪 :=
  (coeffAlong_wEquiv (homMarkedAlong 𝔪) hN (isCoherent_homMarkedAlong h𝔞 hN) hd).trans
    (homAlong_wEquiv 𝔪 hN h𝔞 hd)

end Tower

end

end Hironaka.HomogenizedIdealAlongTower
