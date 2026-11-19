import Hironaka.Resolution.HironakaG8MixedSum
import Hironaka.Resolution.HironakaG8ProjEquiv
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The coefficient ideal of a marked ideal with empty boundary is equivalent to it (G8 lane, run 0080, round 3; (B') port P3)

Blueprint: `hironaka-g8-resume-coefficient-class.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2, P3
("BM08 Cor 3.11 / §8.1 for `E = []`: `𝔪 ≈ coeffMarkedAlong 𝔪` when `𝔪.E = []` (standard = logarithmic derivatives for
empty boundary; G8's `mixedEquiv_logClosure` with `rawLogMarked` should specialize)").

BM08 Theorem 3.10 / Corollary 3.11: a marked ideal is equivalent to its logarithmic coefficient ideal; for an empty
boundary the logarithmic derivatives are the ordinary ones (BM08 §8.1).  In Lean:

* `logDerivIdealAlong_nil`: `𝒟_{N,[]}(A) = 𝒟_N(A)` (the logarithmic tangent fields for an empty boundary are the tangent
  fields of the carrier), `rawIter_nil`, `rawLogMarked_eq_derivMarkedAlong`;
* `le_iterDerivIdealAlong`, `isInvDomain_derivMarkedAlong`: the derivative marked ideals `(𝒟_N^j 𝔞, d - j)`, `j < d`, are
  in the native domain;
* `bmCommonMark_powerFam`, **`bmFiniteSum_powerFam_eq_msum`**: Włodarczyk's sum `msum` (product of the marks) is the
  common-mark sum (`bmFiniteSum`, lcm of the marks) of the powers `Q_i^{∏_{j≠i} d_j}`;
* **`mixedEquiv_bmFiniteSum_msum`**: the two sum conventions give mixed-test equivalent marked ideals;
* **`mixedEquiv_coeffMarkedAlong_of_nil`**: for `𝔪` in the native domain with `𝔪.E = []`, `𝔪 ~ coeffMarkedAlong 𝔪`
  (mixed-test equivalence: admissible blowups, products with a line, exceptional blowups), hence
  `projEquiv_coeffMarkedAlong_of_nil` (BM's `s(i,ii)`, the plan's `WPEquiv`) and Włodarczyk's equivalence.

Not here: the LOCAL form (`HironakaG8LocalHistory.LocWPEquiv`) — it needs the log-closure inclusions of
`HironakaG8LogClosureHistory` along local histories (restriction steps).  Sorry-free.  Universe `0`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CoeffClass

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  RelativePrincipalizationSpan DerivativeIdealAlong DerivativeIdealAlongCoherent
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.IdealWeightPowers (idealPow)
open Hironaka.HomogenizedGlueing (finSumIdeal)
open Hironaka.CoefficientIdeal (msum sumExp mul_sumExp)
open Hironaka.HomogenizedIdealAlong (coeffMarkedAlong derivMarkedAlong)
open Hironaka.HironakaActualIntrinsicLogDerivativeFrame (logDerivIdealAlong)
open Hironaka.HironakaActualIteratedLogMarkedFamily (rawIter rawLogMarked bmCommonMark bmFiniteSum)
open Hironaka.HironakaActualPowerBoundaryExponents (powerMarked powerMarked_isInvDomain)
open Hironaka.HironakaG8MixedEquiv (MixedEquiv mixedEquiv_powerMarked mixedEquiv_logClosure)
open Hironaka.HironakaG8MixedSum (fam MixedEquiv.finSum mixedEquiv_of_restrictEquiv)
open Hironaka.HironakaG8ProjEquiv (ProjEquiv MixedEquiv.projEquiv)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)

noncomputable section

variable {n : ℕ}

/-! ### Logarithmic derivatives for an empty boundary -/

section Nil

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **For an empty boundary the logarithmic derivative ideal is the derivative ideal along the carrier.** -/
theorem logDerivIdealAlong_nil (N : Set M) (A : GermIdeal n M) : logDerivIdealAlong N [] A = derivIdealAlong N A := by
  refine GermIdeal.ext (funext fun x => funext fun f => propext ⟨fun h => ?_, fun h => ?_⟩)
  · refine IsInSpanAt.mono ?_ h
    rintro s (hs | hs | ⟨e, ξ, g, hξ, hg, rfl⟩)
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr ⟨e, ξ, g, hξ.1, hg, rfl⟩)
  · refine IsInSpanAt.mono ?_ h
    rintro s (hs | hs | ⟨e, ξ, g, hξ, hg, rfl⟩)
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr ⟨e, ξ, g, ⟨hξ, fun H hH => absurd hH List.not_mem_nil⟩, hg, rfl⟩)

/-- **The ideal grows under derivatives**: `𝔞 ⊆ 𝒟_N^j 𝔞` (coherent `𝔞`, closed submanifold `N`). -/
theorem le_iterDerivIdealAlong {N : Set M} {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) :
    ∀ j, 𝔞.Le (iterDerivIdealAlong N 𝔞 j)
  | 0 => fun _ _ hg => hg
  | j + 1 => fun x g hg =>
    le_derivIdealAlong (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem
      (isCoherent_iterDerivIdealAlong h𝔞 hN j) hf) x g (le_iterDerivIdealAlong h𝔞 hN j x g hg)

end Nil

section Family

variable {X : CMfd.{0} n}

theorem rawIter_nil (N : Set X) (A : GermIdeal n X) : ∀ r, rawIter N [] A r = iterDerivIdealAlong N A r
  | 0 => rfl
  | r + 1 => by
    show ((logDerivIdealAlong N [])^[r+1]) A = derivIdealAlong N (iterDerivIdealAlong N A r)
    rw [Function.iterate_succ_apply']
    change logDerivIdealAlong N [] (rawIter N [] A r) = _
    rw [rawIter_nil N A r, logDerivIdealAlong_nil]

/-- **For an empty boundary the logarithmic derivative marked ideals are the derivative marked ideals.** -/
theorem rawLogMarked_eq_derivMarkedAlong (M : MarkedIdeal n X) (hE : M.E = []) (j : ℕ) :
    rawLogMarked M j = derivMarkedAlong M j := by
  obtain ⟨N, E, I, d⟩ := M
  change E = [] at hE
  subst hE
  show (⟨N, [], rawIter N [] I j, d - j⟩ : MarkedIdeal n X) = ⟨N, [], iterDerivIdealAlong N I j, d - j⟩
  rw [rawIter_nil]

/-- **The derivative marked ideals `(𝒟_N^j 𝔞, d - j)`, `j < d`, are in the native domain.** -/
theorem isInvDomain_derivMarkedAlong {r : ℕ} {M : MarkedIdeal n X} (hM : IsInvDomain r M) {j : ℕ} (hj : j < M.d) :
    IsInvDomain r (derivMarkedAlong M j) where
  isWellFormed :=
    { isClosedSubmanifold_N := hM.isWellFormed.isClosedSubmanifold_N
      isCoherent := isCoherent_iterDerivIdealAlong hM.isWellFormed.isCoherent hM.isWellFormed.isClosedSubmanifold_N j
      isSNCDivisor := hM.isWellFormed.isSNCDivisor
      isTransverse := hM.isWellFormed.isTransverse }
  dimLE := hM.dimLE
  one_le_d := by
    show 1 ≤ M.d - j
    omega
  isNonzeroAlongAt := fun y hy => by
    obtain ⟨g, hg, hfr⟩ := hM.isNonzeroAlongAt y hy
    exact ⟨g, le_iterDerivIdealAlong hM.isWellFormed.isCoherent hM.isWellFormed.isClosedSubmanifold_N j y g hg, hfr⟩

/-! ### Włodarczyk's sum and the common-mark sum -/

/-- The powers `Q_i^{∏_{j ≠ i} d_j}` of a family: all of mark `∏_j d_j`. -/
def powerFam (N : Set X) (E : List (Set X)) (A : ℕ → GermIdeal n X) (d : ℕ → ℕ) (m : ℕ) (i : ℕ) : MarkedIdeal n X :=
  powerMarked (fam N E A d i) (sumExp d m i)

theorem bmCommonMark_powerFam {N : Set X} {E : List (Set X)} {A : ℕ → GermIdeal n X} {d : ℕ → ℕ} {m : ℕ}
    (hm : 0 < m) : bmCommonMark (powerFam N E A d m) m = (Finset.range m).prod d := by
  have hval : ∀ i ∈ Finset.range m, (powerFam N E A d m i).d = (Finset.range m).prod d := fun i hi =>
    mul_sumExp d (Finset.mem_range.mp hi)
  apply Nat.dvd_antisymm
  · exact Finset.lcm_dvd fun i hi => (hval i hi).symm ▸ dvd_refl _
  · have h0 := Finset.dvd_lcm (f := fun i => (powerFam N E A d m i).d) (Finset.mem_range.mpr hm)
    rw [hval 0 (Finset.mem_range.mpr hm)] at h0
    exact h0

/-- `𝔞^1 = 𝔞` for a coherent ideal. -/
theorem idealPow_one_eq {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) : idealPow 𝔞 1 = 𝔞 := by
  rw [IdealWeightPowers.idealPow_succ, IdealWeightPowers.idealPow_zero, BlowupControlledTransform.unitIdeal_mul h𝔞]

/-- **Włodarczyk's sum is the common-mark sum of the powers `Q_i^{∏_{j≠i} d_j}`.** -/
theorem bmFiniteSum_powerFam_eq_msum {N : Set X} {E : List (Set X)} {A : ℕ → GermIdeal n X} {d : ℕ → ℕ} {m : ℕ}
    (hm : 0 < m) (hd : ∀ i < m, 0 < d i) (hA : ∀ i < m, (A i).IsCoherent) :
    bmFiniteSum (powerFam N E A d m) m = msum (fam N E A d) m := by
  have hL := bmCommonMark_powerFam (N := N) (E := E) (A := A) (d := d) hm
  have hP : 0 < (Finset.range m).prod d := Finset.prod_pos fun i hi => hd i (Finset.mem_range.mp hi)
  have hideal : finSumIdeal (fun i => idealPow (powerFam N E A d m i).ideal
      (bmCommonMark (powerFam N E A d m) m / (powerFam N E A d m i).d)) m =
      finSumIdeal (fun i => idealPow (fam N E A d i).ideal (sumExp (fun j => (fam N E A d j).d) m i)) m := by
    refine HironakaG8LogFiniteSumTransform.finSumIdeal_congr fun i hi => ?_
    have hdi : (powerFam N E A d m i).d = (Finset.range m).prod d := mul_sumExp d hi
    have hdiv : bmCommonMark (powerFam N E A d m) m / (powerFam N E A d m i).d = 1 := by
      rw [hL, hdi, Nat.div_self hP]
    rw [hdiv]
    exact idealPow_one_eq (GermIdealPullbackCalculus.isCoherent_idealPow (hA i hi) _)
  show (⟨N, E, finSumIdeal (fun i => idealPow (powerFam N E A d m i).ideal
      (bmCommonMark (powerFam N E A d m) m / (powerFam N E A d m i).d)) m, bmCommonMark (powerFam N E A d m) m⟩ :
      MarkedIdeal n X) =
    ⟨N, E, finSumIdeal (fun i => idealPow (fam N E A d i).ideal (sumExp (fun j => (fam N E A d j).d) m i)) m,
      (Finset.range m).prod d⟩
  rw [hideal, hL]

/-- **The two sum conventions are equivalent**: for a family in the native domain on one carrier, Włodarczyk's sum
(`msum`, product of the marks) and the common-mark sum (`bmFiniteSum`, lcm of the marks) are mixed-test equivalent. -/
theorem mixedEquiv_bmFiniteSum_msum {N : Set X} {E : List (Set X)} {A : ℕ → GermIdeal n X} {d : ℕ → ℕ} {m r : ℕ}
    (hm : 0 < m) (hQ : ∀ i < m, IsInvDomain r (fam N E A d i)) (hA : ∀ i, (A i).IsCoherent) :
    MixedEquiv (bmFiniteSum (fam N E A d) m) (msum (fam N E A d) m) := by
  have hd : ∀ i < m, 0 < d i := fun i hi => (hQ i hi).one_le_d
  have hs : ∀ i < m, 1 ≤ sumExp d m i := fun i hi =>
    Finset.prod_pos fun j hj => hd j (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))
  have hhol : ∀ i x g, (A i).mem x g → HolomorphicAt n g x := fun i x g hg =>
    GermIdeal.IsCoherent.holomorphicAt_mem (hA i) hg
  have hhol' : ∀ i x g, (idealPow (A i) (sumExp d m i)).mem x g → HolomorphicAt n g x := fun i x g hg =>
    GermIdeal.IsCoherent.holomorphicAt_mem (GermIdealPullbackCalculus.isCoherent_idealPow (hA i) _) hg
  have h1 : MixedEquiv (bmFiniteSum (fam N E A d) m)
      (bmFiniteSum (fam N E (fun i => idealPow (A i) (sumExp d m i)) (fun i => d i * sumExp d m i)) m) :=
    MixedEquiv.finSum hm hQ (fun i hi => powerMarked_isInvDomain (fam N E A d i) (hQ i hi) (hs i hi)) hhol hhol'
      fun i hi => mixedEquiv_powerMarked (fam N E A d i) (hQ i hi) (hs i hi)
  have h2 : bmFiniteSum (fam N E (fun i => idealPow (A i) (sumExp d m i)) (fun i => d i * sumExp d m i)) m =
      msum (fam N E A d) m :=
    bmFiniteSum_powerFam_eq_msum hm hd fun i _ => hA i
  rw [h2] at h1
  exact h1

/-! ### The coefficient ideal -/

/-- **BM08 Corollary 3.11 for an empty boundary**: a marked ideal in the native domain with `E = []` is mixed-test
equivalent to its coefficient ideal along the carrier `𝓒_N(𝔪) = (𝔞, d) + (𝒟_N 𝔞, d - 1) + ⋯ + (𝒟_N^{d-1} 𝔞, 1)`. -/
theorem mixedEquiv_coeffMarkedAlong_of_nil {r : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain r M) (hE : M.E = []) :
    MixedEquiv M (coeffMarkedAlong M) := by
  have hd := hM.one_le_d
  have hcoh := hM.isWellFormed.isCoherent
  have hN := hM.isWellFormed.isClosedSubmanifold_N
  have h1 := mixedEquiv_logClosure M hM (k := M.d - 1) (by omega)
  rw [show M.d - 1 + 1 = M.d by omega] at h1
  have hfam : rawLogMarked M = fam M.N M.E (fun i => iterDerivIdealAlong M.N M.ideal i) (fun i => M.d - i) :=
    funext fun j => rawLogMarked_eq_derivMarkedAlong M hE j
  rw [hfam] at h1
  have h2 := mixedEquiv_bmFiniteSum_msum (N := M.N) (E := M.E) (A := fun i => iterDerivIdealAlong M.N M.ideal i)
    (d := fun i => M.d - i) (m := M.d) (r := r) (by omega) (fun i hi => isInvDomain_derivMarkedAlong hM hi)
    (fun i => isCoherent_iterDerivIdealAlong hcoh hN i)
  exact h1.trans h2

/-- **The same for BM's `s(i,ii)`** (the relation `WPEquiv` of the (B') plan). -/
theorem projEquiv_coeffMarkedAlong_of_nil {r : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain r M) (hE : M.E = []) :
    ProjEquiv M (coeffMarkedAlong M) :=
  HironakaG8ProjEquiv.MixedEquiv.projEquiv (mixedEquiv_coeffMarkedAlong_of_nil M hM hE)

/-- **The same for Włodarczyk's equivalence.** -/
theorem wEquiv_coeffMarkedAlong_of_nil {r : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain r M) (hE : M.E = []) :
    WEquiv M (coeffMarkedAlong M) :=
  HironakaG8MixedEquiv.MixedEquiv.wEquiv (mixedEquiv_coeffMarkedAlong_of_nil M hM hE)

end Family

end

end Hironaka.HironakaG8CoeffClass
