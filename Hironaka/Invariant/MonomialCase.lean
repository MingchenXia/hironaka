import Hironaka.Invariant.MonomialPart
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.ResolutionDriver

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The invariant of a monomial marked ideal at one stage

Blueprint `hir:monomial-invariant-geometry` (`blueprint/src/hironaka.tex`, Hironaka phase H4, part (1) of
`hir:monomial-case`, `N = M`).  Sources: Włodarczyk 2005, Step 2b; Bierstone--Milman 2008, §5 (the invariant of a monomial
marked ideal).

For an ideal `𝔞` and a simple normal crossings divisor `E` the members through `x` are recorded by the finite set
`memberIdx E x ⊆ ℕ` of their indices in `E`, and the exponents by `expData 𝔞 E x i = divExp 𝔞 (E i) x`; the invariant is
`gamma 𝔞 E d x = MonomialInvariant.inv n (memberIdx E x) (expData 𝔞 E x) d`.

* `card_memberIdx_le`: at most `n` members pass through a point;
* `inv_congr`: the invariant only depends on the exponents of the members through the point;
* `eventually_gamma_le` (**upper semicontinuity**): near `x`, the members through `y` are among those through `x`, with the
  same exponents (local constancy of `divExp`, `DivisorExponent`), so `gamma y ≤ gamma x`;
* `mem_cosupport_iff_of_monomial` (**the cosupport of a monomial ideal**): if `𝓜(𝔞) ⊆ 𝔞`, then
  `x ∈ cosupp(𝔞, d) ↔ d ≤ ∑_{H ∋ x} e_H(x)`; hence `gamma_eq_bot_iff_of_monomial`: `gamma = ⊥` exactly off the cosupport.
  The generator `∏ u_H^{e_H}` of the monomial part has order `∑ e_H` (coordinates have order one, orders add).
* `eventually_gamma_eq_iff` (**the maximum locus near a point**): near `x`, `gamma y = gamma x` iff `y` lies on every
  member of the top set of `x`;
* `isAdmissibleCentre_gamma_eq`, `isAdmissibleCentre_maxLocus_gamma` (**the maximum locus is an admissible centre**): for a
  monomial marked ideal `(M, M, E, 𝔞, d)` the maximum locus of `gamma` on the cosupport (`ResolutionDriver.maxLocus`) is a
  closed submanifold inside the cosupport with only normal crossings with `E` -- near each of its points the intersection
  of the members of the top set (`BoundaryCount.isClosedSubmanifold_memberInter`, `hasNormalCrossings_memberInter`, made
  local by `RegularPointDimension.regularAtDim_of_inter_eq` and `isCoordinateFamilyAt_of_inter_eq`) -- with empty
  interior when `d ≥ 1` (`interior_get_eq_empty`); `isInvUSCOn_gamma` is upper semicontinuity in the driver's form.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter Finset
open scoped Topology Manifold

namespace Hironaka.MonomialCase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.DerivativeIdeal Hironaka.OrderTaylor
  Hironaka.BlowupFlatCoordinates Hironaka.GiraudAlong
  Hironaka.DivisorExponent Hironaka.GermOrderProduct
  Hironaka.MemberPullback Hironaka.MonomialPart
  Hironaka.NormalCrossings Hironaka.MonomialInvariant
  Hironaka.BoundaryCount Hironaka.RegularPointDimension
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal

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

/-! ### Exponent data and the invariant -/

section Gamma

variable (n) in
/-- The exponents of `𝔞` along the members of `E` at `x` (`0` beyond the length of `E`). -/
def expData (𝔞 : GermIdeal n M) (E : List (Set M)) (x : M) (i : ℕ) : ℕ :=
  if h : i < E.length then divExp n 𝔞 (E.get ⟨i, h⟩) x else 0

variable (n) in
/-- **The invariant of a monomial marked ideal** at `x`. -/
def gamma (𝔞 : GermIdeal n M) (E : List (Set M)) (d : ℕ) (x : M) : WithBot Val :=
  inv n (memberIdx E x) (expData n 𝔞 E x) d

variable {𝔞 : GermIdeal n M} {E : List (Set M)}

/-- **Near `x`, the members through `y` carry the exponents they have at `x`.** -/
theorem eventually_expData_eq (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent)
    (h0 : ∀ y, IsNonzeroAt 𝔞 y) (x : M) :
    ∀ᶠ y in 𝓝 x, ∀ i ∈ memberIdx E y, expData n 𝔞 E y i = expData n 𝔞 E x i := by
  have h : ∀ᶠ y in 𝓝 x, ∀ i : Fin E.length, y ∈ E.get i →
      divExp n 𝔞 (E.get i) y = divExp n 𝔞 (E.get i) x := by
    refine eventually_all.mpr fun i => ?_
    by_cases hxi : x ∈ E.get i
    · obtain ⟨k, hk⟩ := (isClosedSubmanifold_get hn hE i).2 x hxi
      exact eventually_divExp_eq h𝔞 hk (Eventually.of_forall h0)
    · filter_upwards [(hE.1 _ (List.get_mem E i)).isOpen_compl.mem_nhds hxi] with y hy hyi
      exact absurd hyi hy
  filter_upwards [h] with y hy i hi
  obtain ⟨hlt, hyi⟩ := (mem_memberIdx E).mp hi
  simp only [expData, dif_pos hlt]
  exact hy ⟨i, hlt⟩ hyi

/-- **Upper semicontinuity of the invariant** (`hir:monomial-case` (1)). -/
theorem eventually_gamma_le (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent)
    (h0 : ∀ y, IsNonzeroAt 𝔞 y) (d : ℕ) (x : M) :
    ∀ᶠ y in 𝓝 x, gamma n 𝔞 E d y ≤ gamma n 𝔞 E d x := by
  filter_upwards [eventually_memberIdx_subset E hE.1 x, eventually_expData_eq hn hE h𝔞 h0 x] with y hsub hexp
  unfold gamma
  rw [inv_congr hexp]
  exact inv_mono hsub

/-- **The maximum locus near a point** (`hir:monomial-case` (1)): near `x`, a point has the invariant of `x` iff it lies on
every member of the top set of `x` (`MonomialInvariant.exists_top`). -/
theorem eventually_gamma_eq_iff (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent)
    (h0 : ∀ y, IsNonzeroAt 𝔞 y) {d : ℕ} (x : M) {I : Finset ℕ}
    (hI : I ∈ feasible (memberIdx E x) (expData n 𝔞 E x) d)
    (htop : ∀ K ∈ feasible (memberIdx E x) (expData n 𝔞 E x) d,
      key n (expData n 𝔞 E x) K ≤ key n (expData n 𝔞 E x) I) :
    ∀ᶠ y in 𝓝 x, (gamma n 𝔞 E d y = gamma n 𝔞 E d x ↔ I ⊆ memberIdx E y) := by
  filter_upwards [eventually_memberIdx_subset E hE.1 x, eventually_expData_eq hn hE h𝔞 h0 x] with y hsub hexp
  unfold gamma
  rw [inv_congr hexp]
  exact inv_eq_iff_subset hsub hI htop

end Gamma

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

/-- **The cosupport of a monomial ideal** (`hir:monomial-case` (1)): if `𝓜(𝔞) ⊆ 𝔞` (so `𝔞 = 𝓜(𝔞)`), then
`x ∈ cosupp(𝔞, d)` iff the exponents of the members through `x` add up to at least `d`. -/
theorem mem_cosupport_iff_of_monomial (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent)
    (hmono : (monomialPart n 𝔞 E).Le 𝔞) (d : ℕ) (x : M) :
    x ∈ cosupport n univ 𝔞 d ↔ d ≤ ∑ i ∈ memberIdx E x, expData n 𝔞 E x i := by
  classical
  obtain ⟨Φ, σ, hΦsrc, hΦx, hσ, hA⟩ := exists_snc_chart hn hE x
  set T : Finset (Fin E.length) := Finset.univ.filter fun i => x ∈ E.get i with hT_def
  set e : Fin E.length → ℕ := fun i => divExp n 𝔞 (E.get i) x
  have hx : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hsum : ∑ i ∈ memberIdx E x, expData n 𝔞 E x i = ∑ i ∈ T, e i := by
    rw [memberIdx, Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.valEmbedding_apply, expData, dif_pos i.2, Fin.eta]
    rfl
  rw [hsum]
  have hzero : ∀ i ∈ T, flatCoord Φ (σ i) x = 0 := fun i hi =>
    (hA i (Finset.mem_filter.mp hi).2 hx.1 hx.2).mp (Finset.mem_filter.mp hi).2
  obtain ⟨hmem, hnotmem⟩ := prod_flatCoord_pow_order Φ σ e hx T hzero
  constructor
  · intro hxc
    by_contra hlt
    push Not at hlt
    -- the generator `∏ u_i^{e_i}` of the monomial part lies in `𝔞`
    have hmM : (monomialPart n 𝔞 E).mem x (fun z => ∏ i ∈ T, flatCoord Φ (σ i) z ^ e i) := by
      refine ⟨holomorphicAt_finset_prod T fun i _ =>
        CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ i) hx) (e i), fun i hxi => ?_⟩
      have hi : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩
      have hu : (vanishingIdeal (n := n) (E.get i)).mem x (flatCoord Φ (σ i)) := by
        refine ⟨holomorphicAt_flatCoord Φ (σ i) hx, ?_⟩
        filter_upwards [(isOpen_flatDomain Φ).mem_nhds hx] with z hz hzi
        exact (hA i hxi hz.1 hz.2).mp hzi
      have hpow := pow_mem_idealPow hu (holomorphicAt_flatCoord Φ (σ i) hx) (e i)
      have hrest : HolomorphicAt n (fun z => ∏ j ∈ T.erase i, flatCoord Φ (σ j) z ^ e j) x :=
        holomorphicAt_finset_prod _ fun j _ =>
          CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ j) hx) (e j)
      refine mem_idealPow_congr (mul_mem_idealPow hrest hpow) (Eventually.of_forall fun z => ?_)
      change (∏ j ∈ T.erase i, flatCoord Φ (σ j) z ^ e j) * flatCoord Φ (σ i) z ^ e i = _
      rw [mul_comm, Finset.mul_prod_erase T (fun j => flatCoord Φ (σ j) z ^ e j) hi]
    have hm𝔞 := hmono x _ hmM
    have hd := mem_idealPow_of_vanishesToOrderOn_univ (hxc.2 _ hm𝔞)
    exact hnotmem (idealPow_le_of_le (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg) (by omega) x _ hd)
  · intro hle
    refine ⟨mem_univ x, fun g hg => vanishesToOrderOn_of_mem ?_⟩
    have hgM := le_monomialPart hn hE h𝔞 x g hg
    have hdiv : ∀ i ∈ T, ∃ c, HolomorphicAt n c x ∧ g =ᶠ[𝓝 x] fun z => c z * flatMap Φ z (σ i) ^ e i := by
      intro i hi
      have hxi : x ∈ E.get i := (Finset.mem_filter.mp hi).2
      exact exists_eq_mul_pow_of_mem_idealPow
        (fun g hg => (vanishingIdeal_mem_iff_flatCoord Φ (hA i hxi) hx g).mp hg) (hgM.2 i hxi)
    obtain ⟨c, hc, hgc⟩ := exists_eq_mul_prod_of_forall hΦsrc (A := fun i => E.get i) e hx T
      (fun i hi _ hy1 hy2 => hA i (Finset.mem_filter.mp hi).2 hy1 hy2)
      (fun i _ y hy => (isClosedSubmanifold_get hn hE i).2 y hy) hσ hgM.1 hdiv
    have hcm := mul_mem_idealPow (q := ∑ i ∈ T, e i) hc hmem
    exact idealPow_le_of_le (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg) hle x g
      (mem_idealPow_congr hcm hgc.symm)

/-- **The invariant vanishes exactly off the cosupport** of a monomial ideal. -/
theorem gamma_eq_bot_iff_of_monomial (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent)
    (hmono : (monomialPart n 𝔞 E).Le 𝔞) (d : ℕ) (x : M) :
    gamma n 𝔞 E d x = ⊥ ↔ x ∉ cosupport n univ 𝔞 d := by
  rw [gamma, inv_eq_bot_iff, mem_cosupport_iff_of_monomial hn hE h𝔞 hmono d x, not_le]

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

/-- At a point of value `v`, the top set `topSet v` is feasible and dominates every feasible set. -/
theorem top_of_gamma_eq {x : M} {v : Val} (hx : gamma n 𝔞 E d x = v) :
    topSet v ∈ feasible (memberIdx E x) (expData n 𝔞 E x) d ∧
      ∀ K ∈ feasible (memberIdx E x) (expData n 𝔞 E x) d,
        key n (expData n 𝔞 E x) K ≤ key n (expData n 𝔞 E x) (topSet v) := by
  have hne : inv n (memberIdx E x) (expData n 𝔞 E x) d ≠ ⊥ := by
    change gamma n 𝔞 E d x ≠ ⊥
    rw [hx]
    exact WithBot.coe_ne_bot
  rw [Ne, inv_eq_bot_iff, not_lt] at hne
  obtain ⟨I, hI, hinv, htop⟩ := exists_top (n := n) hne
  have hv : ((key n (expData n 𝔞 E x) I : Val) : WithBot Val) = v := by
    rw [← hinv]
    exact hx
  rw [← WithBot.coe_inj.mp hv, topSet_key]
  exact ⟨hI, htop⟩

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

/-- **The locus of a value near a point of that value** is the intersection of the members of its top set. -/
theorem eventually_gamma_eq_iff_mem_memberInter (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent)
    (h0 : ∀ y, IsNonzeroAt 𝔞 y) {x : M} {v : Val} (hx : gamma n 𝔞 E d x = v) :
    ∀ᶠ y in 𝓝 x, (gamma n 𝔞 E d y = v ↔ y ∈ memberInter E (topIdx E v)) := by
  obtain ⟨hI, htop⟩ := top_of_gamma_eq hx
  have hlt : ∀ i ∈ topSet v, i < E.length := fun i hi =>
    ((mem_memberIdx E).mp ((mem_feasible.mp hI).1 hi)).1
  filter_upwards [eventually_gamma_eq_iff hn hE h𝔞 h0 x hI htop] with y hy
  rw [← hx, hy, mem_memberInter_topIdx_iff hlt]

/-- The points of value `v` lie on the members of the top set of `v`. -/
theorem mem_memberInter_of_gamma_eq (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent)
    (h0 : ∀ y, IsNonzeroAt 𝔞 y) {x : M} {v : Val} (hx : gamma n 𝔞 E d x = v) :
    x ∈ memberInter E (topIdx E v) :=
  ((eventually_gamma_eq_iff_mem_memberInter hn hE h𝔞 h0 hx).self_of_nhds).mp hx

/-- **Upper semicontinuity** in the form of the resolution driver. -/
theorem isInvUSCOn_gamma (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent)
    (h0 : ∀ y, IsNonzeroAt 𝔞 y) (d : ℕ) (s : Set M) :
    ResolutionInvariantOrder.IsInvUSCOn (gamma n 𝔞 E d) s :=
  fun x _ => (eventually_gamma_le hn hE h𝔞 h0 d x).mono fun _ hy _ => hy

/-- If `v` bounds the invariant, the locus of value `v` is closed. -/
theorem isClosed_gamma_eq (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent)
    (h0 : ∀ y, IsNonzeroAt 𝔞 y) {v : WithBot Val} (hmax : ∀ y, gamma n 𝔞 E d y ≤ v) :
    IsClosed {y | gamma n 𝔞 E d y = v} := by
  refine isClosed_iff_frequently.mpr fun x hx => ?_
  obtain ⟨y, hy, hyle⟩ := (hx.and_eventually (eventually_gamma_le hn hE h𝔞 h0 d x)).exists
  have hy' : gamma n 𝔞 E d y = v := hy
  rw [hy'] at hyle
  exact le_antisymm (hmax x) hyle

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

/-- **The locus of a maximal value is an admissible centre** (`hir:monomial-case` (1), `N = M`): if `v` bounds the
invariant of a monomial ideal, the points of value `v` form a closed submanifold inside the cosupport with only normal
crossings with `E` (near each of its points it is the intersection of the members of the top set of `v`). -/
theorem isAdmissibleCentre_gamma_eq (hn : 0 < n) (𝔪 : MarkedIdeal n M) (hN : 𝔪.N = univ)
    (hE : IsSNCDivisor n 𝔪.E) (h𝔞 : 𝔪.ideal.IsCoherent) (h0 : ∀ y, IsNonzeroAt 𝔪.ideal y)
    (hmono : (monomialPart n 𝔪.ideal 𝔪.E).Le 𝔪.ideal) {v : Val}
    (hmax : ∀ y, gamma n 𝔪.ideal 𝔪.E 𝔪.d y ≤ v) :
    𝔪.IsAdmissibleCentre {y | gamma n 𝔪.ideal 𝔪.E 𝔪.d y = v} := by
  have hloc : ∀ x, gamma n 𝔪.ideal 𝔪.E 𝔪.d x = v → ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
      memberInter 𝔪.E (topIdx 𝔪.E v) ∩ W = {y | gamma n 𝔪.ideal 𝔪.E 𝔪.d y = v} ∩ W := by
    intro x hx
    obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp (eventually_gamma_eq_iff_mem_memberInter hn hE h𝔞 h0 hx)
    refine ⟨W, hWo, hxW, ?_⟩
    ext y
    exact ⟨fun hy => ⟨(hWsub hy.2).mpr hy.1, hy.2⟩, fun hy => ⟨(hWsub hy.2).mp hy.1, hy.2⟩⟩
  refine ⟨⟨isClosed_gamma_eq hn hE h𝔞 h0 hmax, fun x hx => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨k, hk⟩ := (isClosedSubmanifold_memberInter hn hE (topIdx 𝔪.E v)).2 x
      (mem_memberInter_of_gamma_eq hn hE h𝔞 h0 hx)
    obtain ⟨W, hWo, hxW, hW⟩ := hloc x hx
    exact ⟨k, regularAtDim_of_inter_eq hWo hxW hW hk⟩
  · have hc : x ∈ cosupport n univ 𝔪.ideal 𝔪.d := by
      by_contra hc
      have h' := (gamma_eq_bot_iff_of_monomial hn hE h𝔞 hmono 𝔪.d x).mpr hc
      have hx' : gamma n 𝔪.ideal 𝔪.E 𝔪.d x = v := hx
      rw [hx'] at h'
      exact WithBot.coe_ne_bot h'
    change x ∈ cosupport n 𝔪.N 𝔪.ideal 𝔪.d
    rw [hN]
    exact hc
  · obtain ⟨S₀, S, hfam, hcard⟩ := hasNormalCrossings_memberInter hE (topIdx 𝔪.E v) x
      (mem_memberInter_of_gamma_eq hn hE h𝔞 h0 hx)
    obtain ⟨W, hWo, hxW, hW⟩ := hloc x hx
    refine ⟨S₀, S, isCoordinateFamilyAt_of_inter_eq hWo hxW (fun o => ?_) hfam, hcard⟩
    cases o with
    | none => exact hW
    | some i => rfl

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

/-- **The maximum locus of the invariant on the cosupport** (`hir:monomial-case` (1), `N = M`, in the form of the
resolution driver `ResolutionDriver.exists_isGeoResolution_of_wellFounded_invariant`): for a monomial marked ideal
`(M, M, E, 𝔞, d)` it is an admissible centre, with empty interior when `d ≥ 1`. -/
theorem isAdmissibleCentre_maxLocus_gamma (hn : 0 < n) (𝔪 : MarkedIdeal n M) (hN : 𝔪.N = univ)
    (hE : IsSNCDivisor n 𝔪.E) (h𝔞 : 𝔪.ideal.IsCoherent) (h0 : ∀ y, IsNonzeroAt 𝔪.ideal y)
    (hmono : (monomialPart n 𝔪.ideal 𝔪.E).Le 𝔪.ideal) :
    𝔪.IsAdmissibleCentre (ResolutionDriver.maxLocus (gamma n 𝔪.ideal 𝔪.E 𝔪.d) 𝔪.cosupp) ∧
      (1 ≤ 𝔪.d → interior (ResolutionDriver.maxLocus (gamma n 𝔪.ideal 𝔪.E 𝔪.d) 𝔪.cosupp) = ∅) := by
  have hcs : 𝔪.cosupp = cosupport n univ 𝔪.ideal 𝔪.d := by
    change cosupport n 𝔪.N 𝔪.ideal 𝔪.d = _
    rw [hN]
  rcases (ResolutionDriver.maxLocus (gamma n 𝔪.ideal 𝔪.E 𝔪.d) 𝔪.cosupp).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [h]
    exact ⟨isAdmissibleCentre_empty 𝔪, fun _ => interior_empty⟩
  have hx₀c : x₀ ∈ cosupport n univ 𝔪.ideal 𝔪.d := hcs ▸ hx₀.1
  have hne : gamma n 𝔪.ideal 𝔪.E 𝔪.d x₀ ≠ ⊥ := fun h =>
    (gamma_eq_bot_iff_of_monomial hn hE h𝔞 hmono 𝔪.d x₀).mp h hx₀c
  obtain ⟨v, hv⟩ := WithBot.ne_bot_iff_exists.mp hne
  have hmax : ∀ y, gamma n 𝔪.ideal 𝔪.E 𝔪.d y ≤ v := by
    intro y
    by_cases hy : y ∈ 𝔪.cosupp
    · rw [hv]
      exact hx₀.2 y hy
    · have h' : gamma n 𝔪.ideal 𝔪.E 𝔪.d y = ⊥ :=
        (gamma_eq_bot_iff_of_monomial hn hE h𝔞 hmono 𝔪.d y).mpr (hcs ▸ hy)
      rw [h']
      exact bot_le
  have heq : ResolutionDriver.maxLocus (gamma n 𝔪.ideal 𝔪.E 𝔪.d) 𝔪.cosupp =
      {y | gamma n 𝔪.ideal 𝔪.E 𝔪.d y = v} := by
    ext y
    constructor
    · rintro ⟨-, hymax⟩
      have h' := hymax x₀ hx₀.1
      rw [← hv] at h'
      exact le_antisymm (hmax y) h'
    · intro hy
      have hy' : gamma n 𝔪.ideal 𝔪.E 𝔪.d y = v := hy
      have hyc : y ∈ 𝔪.cosupp := by
        rw [hcs]
        by_contra hyc
        have h' := (gamma_eq_bot_iff_of_monomial hn hE h𝔞 hmono 𝔪.d y).mpr hyc
        rw [hy'] at h'
        exact WithBot.coe_ne_bot h'
      exact ⟨hyc, fun y' _ => hy' ▸ hmax y'⟩
  rw [heq]
  refine ⟨isAdmissibleCentre_gamma_eq hn 𝔪 hN hE h𝔞 h0 hmono hmax, fun hd => ?_⟩
  -- the top set is nonempty (its exponents add up to at least `d ≥ 1`), so the locus lies on a member
  obtain ⟨hI, -⟩ := top_of_gamma_eq (𝔞 := 𝔪.ideal) (E := 𝔪.E) (d := 𝔪.d) hv.symm
  have hIne : (topSet v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have h' := (mem_feasible.mp hI).2
    rw [h, Finset.sum_empty] at h'
    omega
  obtain ⟨i, hi⟩ := hIne
  have hlt : i < 𝔪.E.length := ((mem_memberIdx 𝔪.E).mp ((mem_feasible.mp hI).1 hi)).1
  refine Set.eq_empty_of_subset_empty ((interior_mono fun y hy => ?_).trans
    (interior_get_eq_empty hn hE ⟨i, hlt⟩).subset)
  classical
  exact mem_memberInter_of_gamma_eq hn hE h𝔞 h0 hy ⟨i, hlt⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

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

/-- The monomial is holomorphic on the flat domain. -/
theorem holomorphicAt_flatMonomial {y : M} (hy : y ∈ flatDomain Φ) :
    HolomorphicAt n (fun z => ∏ i ∈ T, flatCoord Φ (σ i) z ^ a i) y :=
  holomorphicAt_finset_prod T fun i _ =>
    CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ i) hy) (a i)

include hΦsrc hgen in
/-- **A principal monomial ideal is nonzero** at every point near `x`. -/
theorem eventually_isNonzeroAt_of_principal : ∀ᶠ y in 𝓝 x, IsNonzeroAt 𝔞 y := by
  filter_upwards [hgen, (isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy hyD
  refine ⟨fun z => ∏ i ∈ T, flatCoord Φ (σ i) z ^ a i, (hy _).mpr (isInSpanAt_eq_iff.mpr
    ⟨holomorphicAt_flatMonomial (σ := σ) (T := T) a hyD, fun _ => 1,
      holomorphicAt_const (n := n) (x := y) (1 : ℂ), Eventually.of_forall fun z => by simp⟩), ?_⟩
  refine (frequently_flatMap_ne_zero hΦsrc hyD (T.image σ)).mono fun y' hy' => ?_
  show (∏ i ∈ T, flatCoord Φ (σ i) y' ^ a i) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hy'.2.1 (σ i) (Finset.mem_image_of_mem σ hi))

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

include hΦsrc hσ hA hgen in
/-- **The exponents of a principal monomial ideal** (`hir:monomial-case` (2), consumer side of `hir:monomial-blowup`):
if near `x` the ideal is generated by `∏_{i ∈ T} u_{σ i}^{a_i}` in coordinates in which the members `E_i`, `i ∈ T`, are the
coordinate hyperplanes `{u_{σ i} = 0}`, then the exponent of the ideal along a member `E_i` through `x` is `a_i`. -/
theorem divExp_eq_of_principal (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y) {i : Fin E.length} (hi : i ∈ T)
    (hxi : x ∈ E.get i) : divExp n 𝔞 (E.get i) x = a i := by
  have hx : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hne : IsNonzeroAt 𝔞 x := (eventually_isNonzeroAt_of_principal hΦsrc a hgen).self_of_nhds
  have hm := flatMonomial_mem_idealPow_vanishingIdeal hA a hi
  -- `𝔞` is divisible by `𝓘_{E_i}^{a_i}` near `x`
  have hdiv : IsDivNear n 𝔞 (E.get i) (a i) x := by
    filter_upwards [hgen, eventually_mem_idealPow_vanishingIdeal hm] with z hz hzm hzH
    refine ⟨mem_univ z, fun f hf => IsInSpanAt.vanishesToOrderOn ((hz f).mp hf) ?_⟩
    rintro _ rfl
    exact vanishesToOrderOn_of_mem (mem_idealPow_pointIdeal_of_mem_idealPow_vanishingIdeal hzH hzm)
  -- and not by `𝓘_{E_i}^{a_i + 1}`: at the points of `E_i` off the other hyperplanes the monomial has order `a_i`
  have hndiv : ¬ IsDivNear n 𝔞 (E.get i) (a i + 1) x := by
    intro hd
    have hfreq := frequently_flatMap_ne_zero hΦsrc hx ((T.erase i).image σ)
    obtain ⟨z, ⟨hzD, hzne, hzeq⟩, hzd, hzgen⟩ := (hfreq.and_eventually (hd.and hgen)).exists
    have hσi : σ i ∉ (T.erase i).image σ := by
      intro h
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      exact (Finset.mem_erase.mp hj).1 (hσ (Finset.mem_erase.mp hj).2 hi hji)
    have hu0 : flatCoord Φ (σ i) z = 0 := by
      rw [show flatCoord Φ (σ i) z = flatMap Φ z (σ i) from rfl, hzeq _ hσi]
      exact (hA i hi hx.1 hx.2).mp hxi
    have hzi : z ∈ E.get i := (hA i hi hzD.1 hzD.2).mpr hu0
    have hmz : 𝔞.mem z (fun z => ∏ i ∈ T, flatCoord Φ (σ i) z ^ a i) :=
      (hzgen _).mpr (isInSpanAt_eq_iff.mpr ⟨holomorphicAt_flatMonomial a hzD, fun _ => 1,
        holomorphicAt_const (n := n) (x := z) (1 : ℂ), Eventually.of_forall fun w => by simp⟩)
    have hord := mem_idealPow_of_vanishesToOrderOn_univ ((hzd hzi).2 _ hmz)
    have huh : HolomorphicAt n (flatCoord Φ (σ i)) z := holomorphicAt_flatCoord Φ (σ i) hzD
    have hrest : HolomorphicAt n (fun w => ∏ j ∈ T.erase i, flatCoord Φ (σ j) w ^ a j) z :=
      holomorphicAt_finset_prod _ fun j _ =>
        CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ j) hzD) (a j)
    have hrest0 : ¬ (idealPow (pointIdeal n z) (0 + 1)).mem z
        (fun w => ∏ j ∈ T.erase i, flatCoord Φ (σ j) w ^ a j) := by
      intro h
      have h' := apply_eq_zero_of_mem_idealPow_pointIdeal (le_refl 1) h
      refine Finset.prod_ne_zero_iff.mpr (fun j hj => pow_ne_zero _ ?_) h'
      exact hzne (σ j) (Finset.mem_image_of_mem σ hj)
    have hpow : ¬ (idealPow (pointIdeal n z) (a i + 1)).mem z (fun w => flatCoord Φ (σ i) w ^ a i) := by
      have := CompanionReduction.pow_notMem_idealPow huh (flatCoord_notMem_idealPow_two Φ (σ i) hzD) (a i)
      simpa using this
    have hprod := mul_notMem_idealPow hrest (CompanionReduction.holomorphicAt_pow_of huh (a i)) hrest0 hpow
    refine hprod (mem_idealPow_congr (by simpa using hord) (Eventually.of_forall fun w => ?_))
    change ∏ j ∈ T, flatCoord Φ (σ j) w ^ a j = (∏ j ∈ T.erase i, flatCoord Φ (σ j) w ^ a j) * flatCoord Φ (σ i) w ^ a i
    rw [mul_comm, Finset.mul_prod_erase T (fun j => flatCoord Φ (σ j) w ^ a j) hi]
  have h1 := (isDivNear_iff_le_divExp h𝔞 hxi hne).mp hdiv
  have h2 : ¬ a i + 1 ≤ divExp n 𝔞 (E.get i) x := fun h => hndiv ((isDivNear_iff_le_divExp h𝔞 hxi hne).mpr h)
  omega

include hΦsrc hσ hA hgen in
/-- **A principal monomial ideal is monomial** near `x` (`hir:monomial-case` (2), consumer side of
`hir:monomial-blowup`): if near `x` the ideal is generated by `∏_{i ∈ T} u_{σ i}^{a_i}`, `T` the members through `x`, in
coordinates in which these members are the coordinate hyperplanes `{u_{σ i} = 0}`, then `𝓜(𝔞) ⊆ 𝔞` near `x`. -/
theorem eventually_monomialPart_le_of_principal (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent)
    (hT : ∀ i, i ∈ T ↔ x ∈ E.get i) :
    ∀ᶠ y in 𝓝 x, ∀ g, (monomialPart n 𝔞 E).mem y g → 𝔞.mem y g := by
  have hhol : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hreg : ∀ i ∈ T, ∀ y ∈ E.get i, ∃ k, RegularAtDim (n := n) (E.get i) y k :=
    fun i _ y hy => (isClosedSubmanifold_get hn hE i).2 y hy
  have hexp : ∀ i ∈ T, ∀ᶠ y in 𝓝 x, y ∈ E.get i → divExp n 𝔞 (E.get i) y = a i := by
    intro i hi
    have hxi : x ∈ E.get i := (hT i).mp hi
    obtain ⟨k, hk⟩ := hreg i hi x hxi
    filter_upwards [eventually_divExp_eq h𝔞 hk (eventually_isNonzeroAt_of_principal hΦsrc a hgen)] with y hy hyi
    rw [hy hyi, divExp_eq_of_principal hΦsrc hσ hA a hgen hhol hi hxi]
  have hsub : ∀ᶠ y in 𝓝 x, ∀ i : Fin E.length, y ∈ E.get i → i ∈ T := by
    refine eventually_all.mpr fun i => ?_
    by_cases hxi : x ∈ E.get i
    · exact Eventually.of_forall fun _ _ => (hT i).mpr hxi
    · filter_upwards [(hE.1 _ (List.get_mem E i)).isOpen_compl.mem_nhds hxi] with y hy hyi
      exact absurd hyi hy
  filter_upwards [hgen, (isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ), hsub,
    (eventually_all_finset T).mpr hexp] with y hy hyD hyT hye g hg
  have hdiv : ∀ i ∈ T, ∃ c, HolomorphicAt n c y ∧ g =ᶠ[𝓝 y] fun z => c z * flatMap Φ z (σ i) ^ a i := by
    intro i hi
    by_cases hyi : y ∈ E.get i
    · have h1 := hg.2 i hyi
      rw [hye i hi hyi] at h1
      exact exists_eq_mul_pow_of_mem_idealPow
        (fun g hg => (vanishingIdeal_mem_iff_flatCoord Φ (hA i hi) hyD g).mp hg) h1
    · have huy : flatMap Φ y (σ i) ≠ 0 := fun h => hyi ((hA i hi hyD.1 hyD.2).mpr h)
      exact exists_eq_mul_pow_of_ne_zero (holomorphicAt_flatCoord Φ (σ i) hyD) huy hg.1 (a i)
  obtain ⟨c, hc, hgc⟩ := exists_eq_mul_prod_of_forall hΦsrc (A := fun i => E.get i) a hyD T hA hreg hσ hg.1 hdiv
  exact (hy g).mpr (isInSpanAt_eq_iff.mpr ⟨hg.1, c, hc, hgc⟩)

include hΦsrc hσ hA hgen in
/-- **The invariant of a principal monomial ideal** at `x` is read off its exponents (`T` the members through `x`). -/
theorem gamma_eq_of_principal (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y) (hT : ∀ i, i ∈ T ↔ x ∈ E.get i)
    (d : ℕ) : gamma n 𝔞 E d x = inv n (memberIdx E x) (fun i => if h : i < E.length then a ⟨i, h⟩ else 0) d := by
  unfold gamma
  refine inv_congr fun i hi => ?_
  obtain ⟨hlt, hxi⟩ := (mem_memberIdx E).mp hi
  simp only [expData, dif_pos hlt]
  exact divExp_eq_of_principal hΦsrc hσ hA a hgen h𝔞 ((hT _).mpr hxi) hxi

/-- **A stalk generator of a coherent ideal generates the nearby stalks**: if `𝔞_z = (m)` with `m` holomorphic at `z`, then
`𝔞_y = (m)` for `y` near `z` (so the generator form of `hir:monomial-blowup` at a point gives the hypothesis `hgen` above). -/
theorem eventually_isInSpanAt_iff_of_isCoherent (h𝔞 : 𝔞.IsCoherent) {z : M} {m : M → ℂ} (hm : HolomorphicAt n m z)
    (hz : ∀ g, 𝔞.mem z g ↔ IsInSpanAt (n := n) (· = m) z g) :
    ∀ᶠ y in 𝓝 z, ∀ g, 𝔞.mem y g ↔ IsInSpanAt (n := n) (· = m) y g := by
  obtain ⟨U, hU, hzU, N, s, hs, hgen⟩ := h𝔞 z
  have hsz : ∀ k, IsInSpanAt (n := n) (· = m) z (s k) := fun k =>
    (hz (s k)).mp ((hgen z hzU (s k)).mpr (InvertibleIdealQuotient.isInSpanAt_self ⟨k, rfl⟩
      (holomorphicAt_of_mdifferentiableOn_open hU (hs k) hzU)))
  choose _hsh c hc hsc using fun k => isInSpanAt_eq_iff.mp (hsz k)
  have hmz : 𝔞.mem z m := (hz m).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hm)
  filter_upwards [hU.mem_nhds hzU, eventually_all.mpr fun k => (hc k).eventually,
    eventually_all.mpr fun k => (hsc k).eventually_nhds,
    HadamardBridge.eventually_mem_of_isCoherent h𝔞 hmz] with y hyU hcy hscy hmemy g
  constructor
  · intro hg
    refine RelativePrincipalizationSpan.IsInSpanAt.trans (fun t ht => ?_) ((hgen y hyU g).mp hg)
    obtain ⟨k, rfl⟩ := ht
    exact isInSpanAt_eq_iff.mpr ⟨holomorphicAt_of_mdifferentiableOn_open hU (hs k) hyU, c k, hcy k, hscy k⟩
  · intro hg
    exact GermIdealTotalTransform.mem_of_isInSpanAt_mem h𝔞 (IsInSpanAt.mono (fun t ht => by rw [ht]; exact hmemy) hg)

end Principal

end

end Hironaka.MonomialCase
