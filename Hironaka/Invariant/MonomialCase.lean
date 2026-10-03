/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MonomialPart
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Manifold.LocalHolomorphicInverse
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Invariant.BoundaryCount
import Hironaka.Invariant.CompanionReduction
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Analytic.GermOrderProduct
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.Invariant.MemberPullback
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.OrderTaylor
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The invariant of a monomial marked ideal at one stage

* `card_memberIdx_le`: at most `n` members pass through a point;
* `inv_congr`: the invariant only depends on the exponents of the members through the point;
* The generator `∏ u_H^{e_H}` of the monomial part has order `∑ e_H` (coordinates have order one, orders add).
-/

open Set Filter Finset
open scoped Topology Manifold

namespace Hironaka.MonomialCase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder Hironaka.DerivativeIdeal Hironaka.OrderTaylor Hironaka.BlowupFlatCoordinates Hironaka.GiraudAlong Hironaka.DivisorExponent Hironaka.GermOrderProduct Hironaka.MemberPullback Hironaka.MonomialPart Hironaka.NormalCrossings Hironaka.MonomialInvariant Hironaka.BoundaryCount Hironaka.RegularPointDimension Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal

noncomputable section

/-! ### The invariant only depends on the exponents of the members through the point -/

section Congr

variable {n d : ℕ} {S : Finset ℕ} {a a' : ℕ → ℕ}

theorem feasible_congr (h : ∀ i ∈ S, a i = a' i) : feasible S a d = feasible S a' d := by
  ext K
  simp only [mem_feasible]
  constructor
  · rintro ⟨hKS, hK⟩
    exact ⟨hKS, by rwa [← Finset.sum_congr rfl fun i hi => h i (hKS hi)]⟩
  · rintro ⟨hKS, hK⟩
    exact ⟨hKS, by rwa [Finset.sum_congr rfl fun i hi => h i (hKS hi)]⟩

/-- `MonomialInvariant.inv` only depends on the exponents of the members in `S`. -/
theorem inv_congr (h : ∀ i ∈ S, a i = a' i) : inv n S a d = inv n S a' d := by
  unfold inv
  rw [feasible_congr h]
  congr 1
  refine Finset.image_congr fun K hK => ?_
  have hKS := (mem_feasible.mp (Finset.mem_coe.mp hK)).1
  simp only [key, Finset.sum_congr rfl fun i hi => h i (hKS hi)]

end Congr

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Members through a point -/

section Members

variable (E : List (Set M))

open Classical in
/-- The indices (in `E`) of the members through `x`. -/
def memberIdx (x : M) : Finset ℕ :=
  (Finset.univ.filter fun i : Fin E.length => x ∈ E.get i).map Fin.valEmbedding

theorem mem_memberIdx {x : M} {i : ℕ} : i ∈ memberIdx E x ↔ ∃ h : i < E.length, x ∈ E.get ⟨i, h⟩ := by
  classical
  simp only [memberIdx, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.2, hj⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨i, h⟩, hx, rfl⟩

/-- **At most `n` members pass through a point** of a simple normal crossings divisor (they are distinct coordinate
hyperplanes). -/
theorem card_memberIdx_le (hE : IsSNCDivisor n E) (x : M) : #(memberIdx E x) ≤ n := by
  classical
  obtain ⟨S, -, hcard, hinj⟩ := hE.2 x
  rw [memberIdx, Finset.card_map]
  have hσ : ∀ i ∈ Finset.univ.filter (fun i : Fin E.length => x ∈ E.get i),
      ∃ a : Fin n, S i = {a} := fun i hi =>
    Finset.card_eq_one.mp (hcard i (Finset.mem_filter.mp hi).2)
  rcases (Finset.univ.filter fun i : Fin E.length => x ∈ E.get i).eq_empty_or_nonempty with h | ⟨i₀, hi₀⟩
  · rw [h, Finset.card_empty]
    exact Nat.zero_le n
  have : Nonempty (Fin n) := ⟨(hσ i₀ hi₀).choose⟩
  choose! σ hσ using hσ
  calc #(Finset.univ.filter fun i : Fin E.length => x ∈ E.get i)
      ≤ #(Finset.univ : Finset (Fin n)) := by
        refine Finset.card_le_card_of_injOn σ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
        intro i hi j hj hij
        refine hinj (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 ?_
        rw [hσ i hi, hσ j hj, hij]
    _ = n := by simp

/-- Near `x` the members through `y` are among those through `x` (the members are closed). -/
theorem eventually_memberIdx_subset (hE : ∀ H ∈ E, IsClosed H) (x : M) :
    ∀ᶠ y in 𝓝 x, memberIdx E y ⊆ memberIdx E x := by
  have h : ∀ᶠ y in 𝓝 x, ∀ i : Fin E.length, y ∈ E.get i → x ∈ E.get i := by
    refine eventually_all.mpr fun i => ?_
    by_cases hxi : x ∈ E.get i
    · exact Eventually.of_forall fun _ _ => hxi
    · filter_upwards [(hE _ (List.get_mem E i)).isOpen_compl.mem_nhds hxi] with y hy hyi
      exact absurd hyi hy
  filter_upwards [h] with y hy i hi
  obtain ⟨hlt, hyi⟩ := (mem_memberIdx E).mp hi
  exact (mem_memberIdx E).mpr ⟨hlt, hy ⟨i, hlt⟩ hyi⟩

end Members

/-! ### The cosupport of a monomial ideal -/

section Cosupport

variable {𝔞 : GermIdeal n M} {E : List (Set M)}

/-- A coordinate of a flat chart has order at most one at every point of the flat domain. -/
theorem flatCoord_notMem_idealPow_two {x : M} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (t : Fin n) {y : M} (hy : y ∈ flatDomain Φ) : ¬ (idealPow (pointIdeal n y) 2).mem y (flatCoord Φ t) := by
  intro h
  obtain ⟨v, hv⟩ := exists_chartDeriv_flatCoord_ne_zero Φ t hy
  have h0 := iterChartDeriv_eq_zero_of_mem_idealPow (e := complexChartAt (n := n) x) hy.1 h [v] (by simp)
  exact hv (by simpa using h0)

/-- **The order of a monomial in flat coordinates** at a point `y` on all its hyperplanes: `∏_T u_i^{a_i}` lies in
`𝔪_y^{∑ a_i}` and not in `𝔪_y^{∑ a_i + 1}`. -/
theorem prod_flatCoord_pow_order {x : M} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    {ι : Type*} [DecidableEq ι] (σ : ι → Fin n) (a : ι → ℕ) {y : M} (hy : y ∈ flatDomain Φ) :
    ∀ T : Finset ι, (∀ i ∈ T, flatCoord Φ (σ i) y = 0) →
      (idealPow (pointIdeal n y) (∑ i ∈ T, a i)).mem y (fun z => ∏ i ∈ T, flatCoord Φ (σ i) z ^ a i) ∧
      ¬ (idealPow (pointIdeal n y) (∑ i ∈ T, a i + 1)).mem y (fun z => ∏ i ∈ T, flatCoord Φ (σ i) z ^ a i) := by
  have hpt : ∀ y' g, (pointIdeal n y).mem y' g → HolomorphicAt n g y' := fun _ _ hg => hg.1
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨?_, fun h => ?_⟩
    · show HolomorphicAt n (fun z => ∏ i ∈ (∅ : Finset ι), flatCoord Φ (σ i) z ^ a i) y
      simpa using holomorphicAt_const (n := n) (x := y) (1 : ℂ)
    have := apply_eq_zero_of_mem_idealPow_pointIdeal (le_refl 1) (by simpa using h)
    simp at this
  | insert j T hj ih =>
    intro h0
    obtain ⟨h1, h2⟩ := ih fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have huh : HolomorphicAt n (flatCoord Φ (σ j)) y := holomorphicAt_flatCoord Φ (σ j) hy
    have hu : (pointIdeal n y).mem y (flatCoord Φ (σ j)) :=
      mem_pointIdeal_of_apply_eq_zero huh (h0 j (Finset.mem_insert_self j T))
    have hpow := pow_mem_idealPow hu huh (a j)
    have hnot : ¬ (idealPow (pointIdeal n y) (a j * 1 + 1)).mem y (fun z => flatCoord Φ (σ j) z ^ a j) :=
      CompanionReduction.pow_notMem_idealPow huh (flatCoord_notMem_idealPow_two Φ (σ j) hy) (a j)
    have hT : HolomorphicAt n (fun z => ∏ i ∈ T, flatCoord Φ (σ i) z ^ a i) y :=
      holomorphicAt_finset_prod T fun i _ =>
        CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ i) hy) (a i)
    have hfun : (fun z => ∏ i ∈ insert j T, flatCoord Φ (σ i) z ^ a i) =
        fun z => flatCoord Φ (σ j) z ^ a j * ∏ i ∈ T, flatCoord Φ (σ i) z ^ a i := by
      funext z
      rw [Finset.prod_insert hj]
    rw [hfun, Finset.sum_insert hj]
    refine ⟨mul_mem_idealPow_add hpt hpow h1, ?_⟩
    have := mul_notMem_idealPow (CompanionReduction.holomorphicAt_pow_of huh (a j)) hT
      (by simpa using hnot) h2
    simpa [add_assoc] using this

open Classical in
/-- **Simple normal crossings coordinates at a point**: a centred flat chart and an index map `σ`, injective on the
members through `x`, in which each member through `x` is the coordinate hyperplane `{w_{σ i} = 0}`. -/
theorem exists_snc_chart (hn : 0 < n) (hE : IsSNCDivisor n E) (x : M) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (σ : Fin E.length → Fin n),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧ Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      Set.InjOn σ (Finset.univ.filter fun i => x ∈ E.get i) ∧
      ∀ i, x ∈ E.get i → ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
          (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i) = 0) := by
  classical
  obtain ⟨S, ⟨Φ, hΦsrc, hΦx, hcoord⟩, hcard, hinj⟩ := hE.2 x
  set σ : Fin E.length → Fin n := fun i => if h : (S i).Nonempty then (S i).min' h else ⟨0, hn⟩
  have hSσ : ∀ i, x ∈ E.get i → S i = {σ i} := by
    intro i hxi
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hcard i hxi)
    simp [σ, ha]
  refine ⟨Φ, σ, hΦsrc, hΦx, fun i hi j hj hij => ?_, fun i hxi y hy1 hy2 => ?_⟩
  · apply hinj (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    rw [hSσ i (Finset.mem_filter.mp hi).2, hSσ j (Finset.mem_filter.mp hj).2, hij]
  · rw [hcoord i hxi hy1 hy2, hSσ i hxi]
    simp only [coordSubspace, Finset.mem_singleton, forall_eq, Set.mem_ofPred_eq]
    rfl

end Cosupport

/-! ### The maximum locus -/

section MaxLocus

variable {𝔞 : GermIdeal n M} {E : List (Set M)} {d : ℕ}

/-- The set recorded in the third entry of a value of the invariant (the top set, `MonomialInvariant.exists_top`). -/
def topSet (v : Val) : Finset ℕ := ofColex (ofLex (ofLex v).2).2

@[simp] theorem topSet_key (a : ℕ → ℕ) (K : Finset ℕ) : topSet (key n a K) = K := rfl

open Classical in
/-- The indices in `E` of the members of the top set of a value. -/
def topIdx (E : List (Set M)) (v : Val) : Finset (Fin E.length) :=
  Finset.univ.filter fun i => (i : ℕ) ∈ topSet v

/-- Lying on the members of `topIdx E v` is containing the top set among the members through the point. -/
theorem mem_memberInter_topIdx_iff {v : Val} (hlt : ∀ i ∈ topSet v, i < E.length) {y : M} :
    y ∈ memberInter E (topIdx E v) ↔ topSet v ⊆ memberIdx E y := by
  classical
  constructor
  · intro h i hi
    exact (mem_memberIdx E).mpr ⟨hlt i hi, h ⟨i, hlt i hi⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)⟩
  · intro h j hj
    obtain ⟨hlt', hy⟩ := (mem_memberIdx E).mp (h (Finset.mem_filter.mp hj).2)
    exact hy

/-- Coordinate families are local: families agreeing on an open neighbourhood of `x` have the same adapted
coordinates at `x`. -/
theorem isCoordinateFamilyAt_of_inter_eq {ι : Type*} {A B : ι → Set M} {S : ι → Finset (Fin n)} {x : M}
    {W : Set M} (hW : IsOpen W) (hxW : x ∈ W) (hAB : ∀ i, A i ∩ W = B i ∩ W)
    (h : IsCoordinateFamilyAt n A S x) : IsCoordinateFamilyAt n B S x := by
  obtain ⟨Φ, hsub, hzero, hflat⟩ := h
  have hxs : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
  have hs : IsOpen ((complexChartAt (n := n) x).val.target ∩ (complexChartAt (n := n) x).val.symm ⁻¹' W) :=
    (complexChartAt (n := n) x).val.continuousOn_symm.isOpen_inter_preimage
      (complexChartAt (n := n) x).val.open_target hW
  have hq : (complexChartAt (n := n) x).val x ∈
      Φ.source ∩ ((complexChartAt (n := n) x).val.target ∩ (complexChartAt (n := n) x).val.symm ⁻¹' W) :=
    ⟨Φ.center_mem_source, (complexChartAt (n := n) x).val.map_source hxs, by
      simpa [Set.mem_preimage, (complexChartAt (n := n) x).val.left_inv hxs] using hxW⟩
  refine ⟨Φ.restrict _ hs _ hq, fun z hz => hsub hz.1, hzero, fun i hxi y hy hyΦ => ?_⟩
  have hyW : y ∈ W := by
    have h' : (complexChartAt (n := n) x).val.symm ((complexChartAt (n := n) x).val y) ∈ W := hyΦ.2.2
    rwa [(complexChartAt (n := n) x).val.left_inv hy] at h'
  have hxA : x ∈ A i := by
    have h' : x ∈ B i ∩ W := ⟨hxi, hxW⟩
    rw [← hAB i] at h'
    exact h'.1
  have hiff : y ∈ B i ↔ y ∈ A i := by
    constructor
    · intro hb
      have h' : y ∈ B i ∩ W := ⟨hb, hyW⟩
      rw [← hAB i] at h'
      exact h'.1
    · intro ha
      have h' : y ∈ A i ∩ W := ⟨ha, hyW⟩
      rw [hAB i] at h'
      exact h'.1
  rw [hiff]
  exact hflat i hxA hy hyΦ.1

/-- **A member of a simple normal crossings divisor has empty interior** (in coordinates it is a coordinate
hyperplane). -/
theorem interior_get_eq_empty (hn : 0 < n) (hE : IsSNCDivisor n E) (i : Fin E.length) :
    interior (E.get i) = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨Φ, σ, -, -, -, hA⟩ := exists_snc_chart hn hE x
  have hxi : x ∈ E.get i := interior_subset hx
  have hxd : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hev : (fun _ => (0 : ℂ)) =ᶠ[𝓝 x] flatCoord Φ (σ i) := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxd, isOpen_interior.mem_nhds hx] with z hz hzi
    exact ((hA i hxi hz.1 hz.2).mp (interior_subset hzi)).symm
  exact flatCoord_notMem_idealPow_two Φ (σ i) hxd (mem_idealPow_congr (zero_mem_idealPow _ x 2) hev)

end MaxLocus

/-! ### Principal monomial ideals in simple normal crossings coordinates -/

section Principal

open Hironaka.IdealOrderArithmetic

variable {𝔞 : GermIdeal n M} {E : List (Set M)} {x : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
  (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
  {σ : Fin E.length → Fin n} {T : Finset (Fin E.length)}
  (hσ : Set.InjOn σ T)
  (hA : ∀ i ∈ T, ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
    chartAt (ComplexModel n) x y ∈ Φ.source → (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i) = 0))
  (a : Fin E.length → ℕ)
  (hgen : ∀ᶠ y in 𝓝 x, ∀ g, 𝔞.mem y g ↔
    IsInSpanAt (n := n) (· = fun z => ∏ i ∈ T, flatCoord Φ (σ i) z ^ a i) y g)

include hA in
/-- The monomial lies in `𝓘_{E_i}^{a_i}` at `x` for `i ∈ T`. -/
theorem flatMonomial_mem_idealPow_vanishingIdeal {i : Fin E.length} (hi : i ∈ T) :
    (idealPow (vanishingIdeal (n := n) (E.get i)) (a i)).mem x (fun z => ∏ i ∈ T, flatCoord Φ (σ i) z ^ a i) := by
  have hx : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hu : (vanishingIdeal (n := n) (E.get i)).mem x (flatCoord Φ (σ i)) := by
    refine ⟨holomorphicAt_flatCoord Φ (σ i) hx, ?_⟩
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hx] with z hz hzi
    exact (hA i hi hz.1 hz.2).mp hzi
  have hpow := pow_mem_idealPow hu (holomorphicAt_flatCoord Φ (σ i) hx) (a i)
  have hrest : HolomorphicAt n (fun z => ∏ j ∈ T.erase i, flatCoord Φ (σ j) z ^ a j) x :=
    holomorphicAt_finset_prod _ fun j _ =>
      CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ j) hx) (a j)
  refine mem_idealPow_congr (mul_mem_idealPow hrest hpow) (Eventually.of_forall fun z => ?_)
  change (∏ j ∈ T.erase i, flatCoord Φ (σ j) z ^ a j) * flatCoord Φ (σ i) z ^ a i = _
  rw [mul_comm, Finset.mul_prod_erase T (fun j => flatCoord Φ (σ j) z ^ a j) hi]

end Principal

end

end Hironaka.MonomialCase
