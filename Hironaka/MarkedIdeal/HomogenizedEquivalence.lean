import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.CompanionReduction

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The homogenized ideal is equivalent to the marked ideal

Hironaka phase H3 (TN23-ENVELOPES), requested by TN-CLASSICAL on I-0981 (C-0027, item 1, requirement node
`hir:homogenized-coefficient`); blueprint `mc:hom-sum`, `mc:hom-sum-transform`, `mc:homogenized-tower`,
`mc:homogenized-equivalent`, `mc:homogenized-maximal-order` (`blueprint/src/maximal-contact.tex`).  Source:
Włodarczyk 2005, the lemma after `le:hom` (`(𝓗(𝓘), μ) ≃ (𝓘, μ)`, `hiron.tex` lines 822--840); the analytic paper
(GGT 2008) §5.5.

* `homSum A B μ = ∑_{i<μ} Aᵢ Bⁱ`, so `𝓗(𝔞) = homSum (𝓓^i 𝔞) T(𝔞) μ` (`homogenizedIdeal_eq_homSum`, by definition);
  `controlledTransform_homSum`: for `Aᵢ ⊆ 𝓘_C^{μ-i}` and `B ⊆ 𝓘_C`,
  `σ^c(∑ᵢ Aᵢ Bⁱ, μ) = ∑ᵢ σ^c(Aᵢ, μ - i) σ^c(B, 1)ⁱ`;  `orderGE_homSum`: the order of `∑ᵢ Aᵢ Bⁱ` is `≥ μ` where
  `ord Aᵢ ≥ μ - i` and `ord B ≥ 1`.
* `homMarked 𝔪 = (M, N, E, 𝓗(𝔞), μ)`; `hom_tower`: along a multiple test blow-up `T` of `𝔪 = (X, X, E, 𝔞, μ)`
  (`𝔞` coherent, `μ ≥ 1`), `T` is a multiple test blow-up of `𝓗(𝔪)` and
  `𝓗(𝔪)_T = ∑ᵢ [𝓓^i 𝔪]_T · [T(𝔪)]_Tⁱ`.
* **`hom_wEquiv`: `𝓗(𝔪) ≃ 𝔪`** (`MarkedIdealEquivalence.WEquiv`), and `coeff_hom_wEquiv`: `𝓒(𝓗(𝔪)) ≃ 𝔪`.
* `isMaximalOrder_homogenizedIdeal`, `isMaximalOrder_coeffMarked`, `isMaximalOrder_coeff_hom`: if `(𝔞, μ)` is of
  maximal order, so are `𝓗(𝔞)` and `𝓒(𝓗(𝔞))` (with the mark `μ_𝓒`).

Not here: `𝓗` and `𝓒` commute with restriction to open sets and with biholomorphisms between open sets
(`le:etale2` / `le:etale3`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedEquivalence

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal
  IdealWeightPowers BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal DerivativeIdealTower CoefficientIdeal
  HomogenizedIdeal HomogenizedGlueing MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
  BlowupControlledTransform MarkedIdealOperationsTransform MaximalContact CoefficientIdealRestriction
  GermIdealPullbackCalculus

noncomputable section

/-! ### Sums `∑ᵢ Aᵢ Bⁱ` -/

section OneSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- `∑_{i<μ} Aᵢ · Bⁱ`. -/
def homSum (A : ℕ → GermIdeal n M) (B : GermIdeal n M) (μ : ℕ) : GermIdeal n M :=
  finSumIdeal (fun i => (A i).mul (idealPow B i)) μ

/-- `𝓗(𝔞) = ∑_{i<μ} 𝓓^i(𝔞) · T(𝔞)^i` with `T(𝔞) = 𝓓^{μ-1}(𝔞)`. -/
theorem homogenizedIdeal_eq_homSum (𝔞 : GermIdeal n M) (μ : ℕ) :
    homogenizedIdeal 𝔞 μ = homSum (fun i => iterDerivIdeal 𝔞 i) (iterDerivIdeal 𝔞 (μ - 1)) μ := rfl

variable [IsComplexManifold n M]

theorem homSum_congr {A A' : ℕ → GermIdeal n M} {B B' : GermIdeal n M} {μ : ℕ} (hA : ∀ i < μ, A i = A' i)
    (hB : B = B') : homSum A B μ = homSum A' B' μ := by
  subst hB
  exact finSumIdeal_congr fun i hi => by rw [hA i hi]

/-- The order of a product: `ord(𝔞𝔟) ≥ p + q` where `ord 𝔞 ≥ p` and `ord 𝔟 ≥ q` (along any `N`). -/
theorem orderGE_mul {N : Set M} {𝔞 𝔟 : GermIdeal n M} {x : M} {p q : ℕ} (ha : OrderGE n N 𝔞 x p)
    (hb : OrderGE n N 𝔟 x q) : OrderGE n N (𝔞.mul 𝔟) x (p + q) := fun _ hg =>
  IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn (IdealOrderArithmetic.mem_mul_iff.mp hg) (by
    rintro s ⟨a, b, ha', hb', rfl⟩
    exact (ha a ha').mul (hb b hb'))

/-- The order of a power: `ord(𝔟^i) ≥ i` where `ord 𝔟 ≥ 1` (along any `N`). -/
theorem orderGE_idealPow {N : Set M} {𝔟 : GermIdeal n M} {x : M} (h1 : OrderGE n N 𝔟 x 1) :
    ∀ i : ℕ, OrderGE n N (idealPow 𝔟 i) x i
  | 0 => fun _ hg => vanishesToOrderOn_zero (holomorphicAt_of_mem_idealPow hg)
  | i + 1 => fun _ hg => by
      refine IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn (mem_idealPow_succ_iff.mp hg) ?_
      rintro s ⟨a, b, ha, hb, rfl⟩
      exact (orderGE_idealPow h1 i a ha).mul (h1 b hb)

/-- **The order of `∑ᵢ Aᵢ Bⁱ` is `≥ μ`** where `ord Aᵢ ≥ μ - i` (`i < μ`) and `ord B ≥ 1`. -/
theorem orderGE_homSum {N : Set M} {A : ℕ → GermIdeal n M} {B : GermIdeal n M} {μ : ℕ} {x : M}
    (hA : ∀ i < μ, OrderGE n N (A i) x (μ - i)) (hB : OrderGE n N B x 1) :
    OrderGE n N (homSum A B μ) x μ := fun _ hg =>
  IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn
    (show IsInSpanAt (n := n) (fun s => ∃ i, i < μ ∧ ((A i).mul (idealPow B i)).mem x s) x _ from hg) (by
    rintro s ⟨i, hi, hs⟩
    have := orderGE_mul (hA i hi) (orderGE_idealPow hB i) s hs
    rwa [Nat.sub_add_cancel hi.le] at this)

/-- `A₀ ⊆ ∑ᵢ Aᵢ Bⁱ` (`μ ≥ 1`). -/
theorem le_homSum {A : ℕ → GermIdeal n M} {B : GermIdeal n M} {μ : ℕ} (hμ : 1 ≤ μ)
    (hA : ∀ x g, (A 0).mem x g → HolomorphicAt n g x) : (A 0).Le (homSum A B μ) := by
  intro x g hg
  have hgh := hA x g hg
  show IsInSpanAt (n := n) (fun s => ∃ i, i < μ ∧ ((A i).mul (idealPow B i)).mem x s) x g
  refine isInSpanAt_of_eq_mul (s := fun p => g p * 1) ⟨0, hμ, ?_⟩ hgh (holomorphicAt_const 1)
    (Eventually.of_forall fun p => by simp)
  exact mul_mem_mul (b := fun _ => 1) hg (holomorphicAt_const (n := n) (x := x) 1) (by simpa using hgh)

theorem isCoherent_homSum {A : ℕ → GermIdeal n M} {B : GermIdeal n M} {μ : ℕ} (hA : ∀ i < μ, (A i).IsCoherent)
    (hB : B.IsCoherent) : (homSum A B μ).IsCoherent :=
  isCoherent_finSumIdeal_of_lt fun i hi => isCoherent_mul (hA i hi) (isCoherent_idealPow hB i)

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  {C : Set M} {π : M' → M}

/-- **The controlled transform of `∑ᵢ Aᵢ Bⁱ`** (`μ ≥ 1`, coherent `Aᵢ ⊆ 𝓘_C^{μ-i}` and `B ⊆ 𝓘_C`):
`σ^c(∑ᵢ Aᵢ Bⁱ, μ) = ∑ᵢ σ^c(Aᵢ, μ - i) σ^c(B, 1)ⁱ`. -/
theorem controlledTransform_homSum (hπ : IsBlowupAlong n C π) {A : ℕ → GermIdeal n M} {B : GermIdeal n M}
    {μ : ℕ} (hμ : 1 ≤ μ) (hA : ∀ i < μ, (A i).IsCoherent) (hB : B.IsCoherent)
    (hAle : ∀ i < μ, (A i).Le (idealPow (vanishingIdeal (n := n) C) (μ - i)))
    (hBle : B.Le (idealPow (vanishingIdeal (n := n) C) 1)) :
    controlledTransform hπ (homSum A B μ) μ =
      homSum (fun i => controlledTransform hπ (A i) (μ - i)) (controlledTransform hπ B 1) μ := by
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have hBpow : ∀ i, (idealPow B i).Le (idealPow (vanishingIdeal (n := n) C) (1 * i)) := fun i => by
    rw [← idealPow_idealPow hIC]; exact idealPow_mono hBle i
  have hprod : ∀ i < μ, ((A i).mul (idealPow B i)).Le (idealPow (vanishingIdeal (n := n) C) μ) :=
    fun i hi => by
      have := mul_le_mul' (hAle i hi) (hBpow i)
      rwa [← RestrictLeCalculus.idealPow_add hIC, one_mul, Nat.sub_add_cancel hi.le] at this
  unfold homSum
  rw [controlledTransform_finSumIdeal hπ hμ (fun i hi => isCoherent_mul (hA i hi) (isCoherent_idealPow hB i))
    hprod]
  refine finSumIdeal_congr fun i hi => ?_
  have hm := controlledTransform_mul hπ (hA i hi) (isCoherent_idealPow hB i) (hAle i hi) (hBpow i)
  have hp := controlledTransform_idealPow hπ hB hBle i
  rw [one_mul] at hm hp
  rw [Nat.sub_add_cancel hi.le] at hm
  rw [hm, hp]

/-- **The maximal order of the homogenized ideal**: `𝔞 ⊆ 𝓗(𝔞)`, so `𝓓^μ 𝓗(𝔞) ⊇ 𝓓^μ 𝔞 = 𝒪`. -/
theorem isMaximalOrder_homogenizedIdeal {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ)
    (h : IsMaximalOrder 𝔞 μ) : IsMaximalOrder (homogenizedIdeal 𝔞 μ) μ := fun x =>
  iterDerivIdeal_mono (le_homogenizedIdeal (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞) hμ)
    μ x _ (h x)

/-- **The coefficient ideal of a marked ideal of maximal order is of maximal order** (`N = M`, `𝔞` coherent,
`d ≥ 1`), with the mark `μ_𝓒`: the last summand `(𝓓^{d-1}𝔞)^e` (`μ_𝓒 = e`) contains `g^e` with `g ∉ 𝔪_x²`. -/
theorem isMaximalOrder_coeffMarked {𝔫 : MarkedIdeal n M} (hN : 𝔫.N = univ) (h𝔞 : 𝔫.ideal.IsCoherent)
    (hd : 1 ≤ 𝔫.d) (hmax : IsMaximalOrder 𝔫.ideal 𝔫.d) :
    IsMaximalOrder (coeffMarked 𝔫).ideal (coeffMarked 𝔫).d := by
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  set D : ℕ → ℕ := fun j => (derivMarked 𝔫 j).d with hD
  have hD1 : ∀ j < 𝔫.d, 1 ≤ D j := fun j hj => by simp only [hD, derivMarked_d]; omega
  set e := sumExp D 𝔫.d (𝔫.d - 1) with he
  have hmark : (coeffMarked 𝔫).d = e := by
    have := mul_sumExp D (show 𝔫.d - 1 < 𝔫.d by omega)
    simp only [hD, derivMarked_d, show 𝔫.d - (𝔫.d - 1) = 1 by omega, one_mul] at this
    exact this.symm
  have hcoh : (coeffMarked 𝔫).ideal.IsCoherent := (isAmbientFamily_derivMarked hN h𝔞).isCoherent_msum
  refine CompanionReduction.isMaximalOrder_of_forall_notMem hcoh fun x hx => ?_
  -- `(𝓓^{d-1}𝔞, 1)` is of maximal order, so it has order `≤ 1` at `x`
  have hmax1 : IsMaximalOrder (iterDerivIdeal 𝔫.ideal (𝔫.d - 1)) 1 := by
    have := hmax.iterDerivIdeal (show 𝔫.d - 1 ≤ 𝔫.d by omega)
    rwa [show 𝔫.d - (𝔫.d - 1) = 1 by omega] at this
  have hx2 : x ∉ cosupport n univ (iterDerivIdeal 𝔫.ideal (𝔫.d - 1)) (1 + 1) := by
    intro h2
    have h := cosupport_add_subset_cosupport_iterDerivIdeal (iterDerivIdeal 𝔫.ideal (𝔫.d - 1)) 1 1 h2
    have h1 := (vanishesToOrderOn_one_iff (mem_univ x) (holomorphicAt_const 1)).mp (h.2 _ (hmax1 x))
    exact one_ne_zero h1
  obtain ⟨g, hg, hgno⟩ := CompanionReduction.exists_notMem_idealPow_of_notMem_cosupport hx2
  have hghol : HolomorphicAt n g x := holomorphicAt_of_mem_iterDerivIdeal hhol (𝔫.d - 1) x g hg
  have hpow : (idealPow (derivMarked 𝔫 (𝔫.d - 1)).ideal e).mem x (fun p => g p ^ e) :=
    OrderMultiplicativity.pow_mem_idealPow hg hghol e
  have hmem : (coeffMarked 𝔫).ideal.mem x (fun p => g p ^ e) :=
    (InvertibleIdealQuotient.isInSpanAt_self
      (S := fun s => ∃ i, i < 𝔫.d ∧ (idealPow (derivMarked 𝔫 i).ideal (sumExp D 𝔫.d i)).mem x s)
      ⟨𝔫.d - 1, by omega, hpow⟩ (holomorphicAt_of_mem_idealPow hpow) : IsInSpanAt (n := n) _ x _)
  have hin := OrderTaylor.mem_idealPow_of_vanishesToOrderOn_univ (hx.2 _ hmem)
  rw [hmark] at hin
  exact CompanionReduction.pow_notMem_idealPow hghol hgno e (by rwa [Nat.mul_one])

end OneSpace

/-! ### Along multiple test blow-ups -/

section Tower

variable {n : ℕ}

/-- **The homogenized marked ideal** `𝓗(𝔪) = (M, N, E, 𝓗(𝔞), μ)` of `𝔪 = (M, N, E, 𝔞, μ)`. -/
def homMarked {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] (𝔪 : MarkedIdeal n M) :
    MarkedIdeal n M where
  N := 𝔪.N
  E := 𝔪.E
  ideal := homogenizedIdeal 𝔪.ideal 𝔪.d
  d := 𝔪.d

variable {X : CMfd.{u} n}

/-- Along a multiple test blow-up of `𝔪`, the cosupport of `𝔪_T` lies in that of `[𝓓^i 𝔪]_T` (mark `μ - i`). -/
theorem mem_cosupport_derivMarked_tower (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    {Y : CMfd.{u} n} {T : BlowupTower X Y} (hT : IsGeoTestTower 𝔪 T) {i : ℕ} (hi : i ≤ 𝔪.d) {x : Y}
    (hx : x ∈ (geoTransformAlong 𝔪 T).cosupp) :
    x ∈ cosupport n univ (geoTransformAlong (derivMarked 𝔪 i) T).ideal (𝔪.d - i) := by
  obtain ⟨-, hNT, -, -, -, -, hle⟩ := inclusions_tower 𝔪 hN h𝔞 hi T hT
  have hdT : i ≤ (geoTransformAlong 𝔪 T).d := by rw [d_geoTransformAlong]; exact hi
  have h1 := cosupp_subset_cosupp_derivMarked hNT hdT hx
  have h1' : x ∈ cosupport n univ (iterDerivIdeal (geoTransformAlong 𝔪 T).ideal i)
      ((geoTransformAlong 𝔪 T).d - i) := by
    have := h1
    rwa [MarkedIdeal.cosupp, derivMarked_N, hNT] at this
  rw [d_geoTransformAlong] at h1'
  exact cosupport_subset_of_le hle _ h1'

/-- If the ideal of `𝔥` (on `N = Y`, mark `μ`) is `∑ᵢ [𝓓^i 𝔪]_T [T(𝔪)]_Tⁱ`, its cosupport contains that of `𝔪_T`. -/
theorem cosupp_subset_of_eq_homSum (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} {T : BlowupTower X Y} (hT : IsGeoTestTower 𝔪 T) {𝔥 : MarkedIdeal n Y}
    (hNH : 𝔥.N = univ) (hdH : 𝔥.d = 𝔪.d)
    (hform : 𝔥.ideal = homSum (fun i => (geoTransformAlong (derivMarked 𝔪 i) T).ideal)
      (geoTransformAlong (derivMarked 𝔪 (𝔪.d - 1)) T).ideal 𝔪.d) :
    (geoTransformAlong 𝔪 T).cosupp ⊆ 𝔥.cosupp := by
  intro x hx
  have hA : ∀ i < 𝔪.d, OrderGE n univ (geoTransformAlong (derivMarked 𝔪 i) T).ideal x (𝔪.d - i) :=
    fun i hi => (mem_cosupport_derivMarked_tower 𝔪 hN h𝔞 hT hi.le hx).2
  have hB : OrderGE n univ (geoTransformAlong (derivMarked 𝔪 (𝔪.d - 1)) T).ideal x 1 := by
    have := (mem_cosupport_derivMarked_tower 𝔪 hN h𝔞 hT (show 𝔪.d - 1 ≤ 𝔪.d by omega) hx).2
    rwa [show 𝔪.d - (𝔪.d - 1) = 1 by omega] at this
  refine ⟨hNH ▸ mem_univ x, ?_⟩
  rw [hNH, hform, hdH]
  exact orderGE_homSum hA hB

/-- If the ideal of `𝔥` is `∑ᵢ [𝓓^i 𝔪]_T [T(𝔪)]_Tⁱ`, it contains the ideal of `𝔪_T` (the term `i = 0`). -/
theorem le_of_eq_homSum (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    {Y : CMfd.{u} n} {T : BlowupTower X Y} (hT : IsGeoTestTower 𝔪 T) {𝔥 : MarkedIdeal n Y}
    (hform : 𝔥.ideal = homSum (fun i => (geoTransformAlong (derivMarked 𝔪 i) T).ideal)
      (geoTransformAlong (derivMarked 𝔪 (𝔪.d - 1)) T).ideal 𝔪.d) :
    (geoTransformAlong 𝔪 T).ideal.Le 𝔥.ideal := by
  obtain ⟨-, -, -, -, -, hcoh0, -⟩ := inclusions_tower 𝔪 hN h𝔞 (Nat.zero_le 𝔪.d) T hT
  rw [hform]
  have h := le_homSum (A := fun i => (geoTransformAlong (derivMarked 𝔪 i) T).ideal)
    (B := (geoTransformAlong (derivMarked 𝔪 (𝔪.d - 1)) T).ideal) hd
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcoh0)
  rw [derivMarked_zero] at h
  exact h

/-- **The transform of the homogenized ideal along a multiple test blow-up** (`N = M`, `𝔞` coherent, `μ ≥ 1`): every
multiple test blow-up `T` of `𝔪` is one of `𝓗(𝔪)`, `𝓗(𝔪)_T` keeps `N` the whole space, and
`𝓗(𝔪)_T = ∑_{i<μ} [𝓓^i 𝔪]_T · [T(𝔪)]_Tⁱ` with `T(𝔪) = 𝓓^{μ-1}(𝔪)`. -/
theorem hom_tower (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      IsGeoTestTower (homMarked 𝔪) T ∧ (geoTransformAlong (homMarked 𝔪) T).N = univ ∧
      (geoTransformAlong (homMarked 𝔪) T).ideal =
        homSum (fun i => (geoTransformAlong (derivMarked 𝔪 i) T).ideal)
          (geoTransformAlong (derivMarked 𝔪 (𝔪.d - 1)) T).ideal 𝔪.d
  | _, .refl => fun _ => ⟨trivial, hN, rfl⟩
  | _, .step T C π hπ => fun hT => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hHT, hNH, hform⟩ := hom_tower 𝔪 hN h𝔞 hd T hT0
      have hDi : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) T).N = univ ∧
          (geoTransformAlong (derivMarked 𝔪 i) T).ideal.IsCoherent ∧
          (geoTransformAlong (derivMarked 𝔪 i) T).IsAdmissibleCentre C := fun i hi => by
        obtain ⟨hDstep, -⟩ := inclusions_tower 𝔪 hN h𝔞 hi (.step T C π hπ) hT
        obtain ⟨-, hCD⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hDstep
        obtain ⟨-, -, hND, -, -, hcohD, -⟩ := inclusions_tower 𝔪 hN h𝔞 hi T hT0
        exact ⟨hND, hcohD, hCD⟩
      have hdH : (geoTransformAlong (homMarked 𝔪) T).d = 𝔪.d := d_geoTransformAlong _ T
      have hEH : (geoTransformAlong (homMarked 𝔪) T).E = (geoTransformAlong 𝔪 T).E :=
        E_geoTransformAlong_eq (𝔪 := homMarked 𝔪) (𝔫 := 𝔪) rfl T
      have hCH : (geoTransformAlong (homMarked 𝔪) T).IsAdmissibleCentre C :=
        ⟨hC.1, hC.2.1.trans (cosupp_subset_of_eq_homSum 𝔪 hN h𝔞 hd hT0 hNH hdH hform), hEH ▸ hC.2.2⟩
      have hcohH : (geoTransformAlong (homMarked 𝔪) T).ideal.IsCoherent := by
        rw [hform]
        exact isCoherent_homSum (fun i hi => (hDi i hi.le).2.1) (hDi (𝔪.d - 1) (by omega)).2.1
      refine ⟨(isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hHT, hCH⟩, geoTransform_N_eq_univ hNH hπ, ?_⟩
      have hideal : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) (.step T C π hπ)).ideal =
          controlledTransform hπ (geoTransformAlong (derivMarked 𝔪 i) T).ideal (𝔪.d - i) := fun i hi => by
        rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform (hDi i hi).1 (hDi i hi).2.1 hπ,
          d_geoTransformAlong, derivMarked_d]
      have hAle : ∀ i < 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) T).ideal.Le
          (idealPow (vanishingIdeal (n := n) C) (𝔪.d - i)) := fun i hi => by
        have := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre (hDi i hi.le).1 (hDi i hi.le).2.1
          (hDi i hi.le).2.2
        rwa [d_geoTransformAlong, derivMarked_d] at this
      have hBle : (geoTransformAlong (derivMarked 𝔪 (𝔪.d - 1)) T).ideal.Le
          (idealPow (vanishingIdeal (n := n) C) 1) := by
        have := hAle (𝔪.d - 1) (by omega)
        rwa [show 𝔪.d - (𝔪.d - 1) = 1 by omega] at this
      rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hNH hcohH hπ, hdH, hform,
        controlledTransform_homSum hπ hd (fun i hi => (hDi i hi.le).2.1) (hDi (𝔪.d - 1) (by omega)).2.1 hAle hBle]
      refine homSum_congr (fun i hi => (hideal i hi.le).symm) ?_
      rw [hideal (𝔪.d - 1) (by omega), show 𝔪.d - (𝔪.d - 1) = 1 by omega]

/-- A multiple test blow-up of `𝓗(𝔪)` is one of `𝔪`. -/
theorem isGeoTestTower_of_hom (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower (homMarked 𝔪) T →
      IsGeoTestTower 𝔪 T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
      have hTm := isGeoTestTower_of_hom 𝔪 hN h𝔞 hd T hT0
      obtain ⟨-, hNH, hform⟩ := hom_tower 𝔪 hN h𝔞 hd T hTm
      obtain ⟨-, hNT, -, -, -, -, -⟩ := inclusions_tower 𝔪 hN h𝔞 (Nat.zero_le 𝔪.d) T hTm
      have hle := le_of_eq_homSum 𝔪 hN h𝔞 hd hTm hform
      have hEH : (geoTransformAlong (homMarked 𝔪) T).E = (geoTransformAlong 𝔪 T).E :=
        E_geoTransformAlong_eq (𝔪 := homMarked 𝔪) (𝔫 := 𝔪) rfl T
      refine (isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hTm, hC.1, fun x hx => ?_, hEH ▸ hC.2.2⟩
      have h := hC.2.1 hx
      rw [MarkedIdeal.cosupp, hNH, d_geoTransformAlong] at h
      rw [MarkedIdeal.cosupp, hNT, d_geoTransformAlong]
      exact cosupport_subset_of_le hle _ h

/-- **Włodarczyk: `(𝓗(𝓘), μ) ≃ (𝓘, μ)`** (the lemma after `le:hom`; `N = M`, `𝔞` coherent, `μ ≥ 1`). -/
theorem hom_wEquiv (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) :
    WEquiv (homMarked 𝔪) 𝔪 := by
  refine ⟨rfl, fun T => ⟨⟨isGeoTestTower_of_hom 𝔪 hN h𝔞 hd T, fun hT => (hom_tower 𝔪 hN h𝔞 hd T hT).1⟩,
    fun hTH => ?_⟩⟩
  have hT := isGeoTestTower_of_hom 𝔪 hN h𝔞 hd T hTH
  obtain ⟨-, hNH, hform⟩ := hom_tower 𝔪 hN h𝔞 hd T hT
  obtain ⟨-, hNT, -, -, -, -, -⟩ := inclusions_tower 𝔪 hN h𝔞 (Nat.zero_le 𝔪.d) T hT
  refine Subset.antisymm ?_ (cosupp_subset_of_eq_homSum 𝔪 hN h𝔞 hd hT hNH (d_geoTransformAlong _ T) hform)
  have hle := le_of_eq_homSum 𝔪 hN h𝔞 hd hT hform
  intro x hx
  rw [MarkedIdeal.cosupp, hNH, d_geoTransformAlong] at hx
  rw [MarkedIdeal.cosupp, hNT, d_geoTransformAlong]
  exact cosupport_subset_of_le hle _ hx

/-- **`𝓒(𝓗(𝔪)) ≃ 𝔪`** (`N = M`, `𝔞` coherent, `μ ≥ 1`). -/
theorem coeff_hom_wEquiv (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) :
    WEquiv (coeffMarked (homMarked 𝔪)) 𝔪 :=
  (coeff_wEquiv (homMarked 𝔪) hN (isCoherent_homogenizedIdeal h𝔞 _) hd).trans (hom_wEquiv 𝔪 hN h𝔞 hd)

/-- **`𝓒(𝓗(𝔪))` is of maximal order** when `𝔪` is (`N = M`, `𝔞` coherent, `μ ≥ 1`). -/
theorem isMaximalOrder_coeff_hom (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) (hmax : IsMaximalOrder 𝔪.ideal 𝔪.d) :
    IsMaximalOrder (coeffMarked (homMarked 𝔪)).ideal (coeffMarked (homMarked 𝔪)).d :=
  isMaximalOrder_coeffMarked (𝔫 := homMarked 𝔪) hN (isCoherent_homogenizedIdeal h𝔞 _) hd
    (isMaximalOrder_homogenizedIdeal h𝔞 hd hmax)

end Tower

end

end Hironaka.HomogenizedEquivalence
