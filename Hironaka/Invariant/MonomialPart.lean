import Hironaka.Invariant.DivisorExponent
import Hironaka.Invariant.MemberPullback
import Hironaka.Invariant.CompanionReduction
import Hironaka.MarkedIdeal.CodimOneCentre
import Hironaka.Invariant.BoundaryCount

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The monomial and nonmonomial parts of an ideal

Blueprint `hir:monomial-factorization`, `hir:monomial-part-ambient` (`blueprint/src/hironaka.tex`, Hironaka phase H4,
the second half of H2 item 1 of TN-CLASSICAL's list, `N = M`).  Sources: Bierstone--Milman 2008, §5 (the monomial part
`𝓜(𝓘)` and the residual factor), Włodarczyk 2005, Step 2 (`𝓘 = 𝓜(𝓘) 𝓝(𝓘)`, `𝓜(𝓘) = 𝓘_{D_1}^{a_1} ⋯ 𝓘_{D_k}^{a_k}`).

* `exists_eq_mul_pow_of_mem_idealPow`: if `𝓘 = (u)` at `y`, the germs of `𝓘^a` at `y` are the multiples of `u^a`.
* `frequently_flatMap_ne_zero`: in flat coordinates, points where a chosen set of coordinates is nonzero and the others
  are unchanged accumulate at every point.
* **Simultaneous divisibility** `exists_eq_mul_prod_of_forall`: in a chart in which the sets `A_i` (`i ∈ T`) are the
  distinct coordinate hyperplanes `{w_{σ i} = 0}` (submanifolds at their points), a germ divisible by each `u_i^{a_i}`
  (`u_i` the coordinate) is divisible by `∏ u_i^{a_i}`.  The coordinate hyperplanes are pairwise non-associate primes;
  formally, by induction on `T`, the cofactor `c'` of `∏_{T'} u^a` lies in `𝔪_z^{a_j}` at the points `z` of `A_j` near
  points of `A_j` off the other hyperplanes, and the identity principle along `A_j`
  (`DivisorExponent.mem_idealPow_vanishingIdeal_of_frequently`) gives `c' ∈ 𝓘_{A_j}^{a_j} = (u_j^{a_j})`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.MonomialPart

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.DerivativeIdeal Hironaka.OrderTaylor
  Hironaka.BlowupFlatCoordinates Hironaka.HadamardBridge
  Hironaka.GiraudAlong Hironaka.DivisorExponent
  Hironaka.GermOrderProduct Hironaka.CodimOneCentre
  Hironaka.MemberPullback

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Powers of a principal ideal -/

section Principal

/-- **Powers of a principal ideal**: if every germ of `𝓘` at `y` is a multiple of `u`, every germ of `𝓘^a` at `y` is a
multiple of `u^a`. -/
theorem exists_eq_mul_pow_of_mem_idealPow {I : GermIdeal n M} {u : M → ℂ} {y : M}
    (hI : ∀ g, I.mem y g → IsInSpanAt (n := n) (· = u) y g) :
    ∀ {a : ℕ} {g : M → ℂ}, (idealPow I a).mem y g →
      ∃ c, HolomorphicAt n c y ∧ g =ᶠ[𝓝 y] fun z => c z * u z ^ a
  | 0, g, hg => ⟨g, hg, Eventually.of_forall fun z => by simp⟩
  | a + 1, g, hg => by
    obtain ⟨-, K, r, c, hr, hc, hsum⟩ := mem_idealPow_succ_iff.mp hg
    choose p q hp hq hpq using hr
    choose d hd hpd using fun k => exists_eq_mul_pow_of_mem_idealPow hI (hp k)
    choose hqhol f hf hqf using fun k => isInSpanAt_eq_iff.mp (hI _ (hq k))
    refine ⟨fun z => ∑ k, c k z * (d k z * f k z),
      HolomorphicAt.sum _ fun k _ => (hc k).mul ((hd k).mul (hf k)), ?_⟩
    filter_upwards [hsum, eventually_all.mpr hpd, eventually_all.mpr hqf] with z hz h1 h2
    rw [hz, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hpq k]
    simp only [Pi.mul_apply, h1 k, h2 k]
    ring

/-- Finite products of holomorphic germs are holomorphic. -/
theorem holomorphicAt_finset_prod {ι : Type*} (T : Finset ι) {F : ι → M → ℂ} {y : M}
    (h : ∀ i ∈ T, HolomorphicAt n (F i) y) : HolomorphicAt n (fun z => ∏ i ∈ T, F i z) y := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holomorphicAt_const (n := n) (x := y) (1 : ℂ)
  | insert j T hj ih =>
    have := (h j (Finset.mem_insert_self j T)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.prod_insert hj] using this

/-- A germ is a multiple of every power of a germ that does not vanish at the point. -/
theorem exists_eq_mul_pow_of_ne_zero {u g : M → ℂ} {y : M} (hu : HolomorphicAt n u y) (huy : u y ≠ 0)
    (hg : HolomorphicAt n g y) (a : ℕ) : ∃ c, HolomorphicAt n c y ∧ g =ᶠ[𝓝 y] fun z => c z * u z ^ a := by
  refine ⟨fun z => g z * ((u z)⁻¹) ^ a,
    hg.mul (CompanionReduction.holomorphicAt_pow_of (BlowupFlatCoordinates.HolomorphicAt.inv hu huy) _), ?_⟩
  filter_upwards [hu.continuousAt.eventually (isOpen_ne.mem_nhds huy)] with z hz
  rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hz, one_pow, mul_one]

/-- A germ of `𝓘` has its powers in the powers of `𝓘`. -/
theorem pow_mem_idealPow {I : GermIdeal n M} {y : M} {u : M → ℂ} (hu : I.mem y u)
    (huh : HolomorphicAt n u y) : ∀ a : ℕ, (idealPow I a).mem y (fun z => u z ^ a)
  | 0 => by
    show HolomorphicAt n (fun z => u z ^ 0) y
    simpa using holomorphicAt_const (n := n) (x := y) (1 : ℂ)
  | a + 1 => by
    have h := mul_mem_idealPow_succ (pow_mem_idealPow hu huh a) hu
      (by simpa [pow_succ] using (CompanionReduction.holomorphicAt_pow_of huh (a + 1)))
    simpa [pow_succ] using h

end Principal

/-! ### Points off coordinate hyperplanes -/

section Frequently

variable {x : M} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
  (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)

include hΦsrc in
/-- In flat coordinates, the points at which the coordinates with index in `T` are nonzero and the other coordinates
are those of `y` accumulate at every point `y` of the flat domain. -/
theorem frequently_flatMap_ne_zero {y : M} (hy : y ∈ flatDomain Φ) (T : Finset (Fin n)) :
    ∃ᶠ y' in 𝓝 y, y' ∈ flatDomain Φ ∧ (∀ l ∈ T, flatMap Φ y' l ≠ 0) ∧
      ∀ l, l ∉ T → flatMap Φ y' l = flatMap Φ y l := by
  set w₀ := flatMap Φ y
  set v : ComplexModel n := ∑ l ∈ T, EuclideanSpace.single l (1 : ℂ)
  have hv : ∀ l, v l = if l ∈ T then 1 else 0 := fun l => by simp [v]
  have hw₀T : w₀ ∈ Φ.target := flatMap_mem_target hy
  set γ : ℂ → ComplexModel n := fun t => w₀ + t • v
  have hγl : ∀ t l, γ t l = w₀ l + t * (if l ∈ T then 1 else 0) := fun t l => by
    simp [γ, hv l]
  have hγc : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hγT : Tendsto γ (𝓝[≠] 0) (𝓝 w₀) := by
    have h := hγc.continuousAt (x := (0 : ℂ))
    simp only [ContinuousAt, γ, zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hφT : Tendsto (fun t => flatInv Φ (γ t)) (𝓝[≠] 0) (𝓝 y) := by
    have h1 := (continuousAt_flatInv hw₀T hΦsrc).tendsto
    rw [show flatInv Φ w₀ = y from flatInv_flatMap hy] at h1
    exact h1.comp hγT
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), γ t ∈ Φ.target ∧ ∀ l ∈ T, γ t l ≠ 0 := by
    refine (hγT.eventually (Φ.isOpen_target.mem_nhds hw₀T)).and ((eventually_all_finset T).mpr fun l hl => ?_)
    by_cases h0 : w₀ l = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hγl, h0, if_pos hl]
      simpa using ht
    · have hc : ContinuousAt (fun t : ℂ => w₀ l + t) 0 := (continuous_const.add continuous_id).continuousAt
      have : ∀ᶠ t in 𝓝 (0 : ℂ), w₀ l + t ≠ 0 :=
        hc.eventually (isOpen_ne.mem_nhds (by simpa using h0))
      filter_upwards [this.filter_mono nhdsWithin_le_nhds] with t ht
      rw [hγl, if_pos hl, mul_one]
      exact ht
  refine hφT.frequently (hev.frequently.mono fun t ⟨htT, htl⟩ => ?_)
  refine ⟨flatInv_mem_flatDomain htT hΦsrc, fun l hl => ?_, fun l hl => ?_⟩
  · rw [flatMap_flatInv htT hΦsrc]
    exact htl l hl
  · rw [flatMap_flatInv htT hΦsrc, hγl, if_neg hl, mul_zero, add_zero]

end Frequently

/-! ### Simultaneous divisibility by coordinate hyperplanes -/

section Factorization

variable {x : M} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
  (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
  {ι : Type*} [DecidableEq ι] {A : ι → Set M} {σ : ι → Fin n}

include hΦsrc in
/-- **Simultaneous divisibility** (`hir:monomial-factorization`): in a chart in which the sets `A i` are the coordinate
hyperplanes `{w_{σ i} = 0}` (submanifolds at their points), with `σ` injective on `T`, a germ at a point `y` of the chart
which is divisible by each `u_i^{a_i}` (`u_i = w_{σ i}`, `i ∈ T`) is divisible by `∏_{i ∈ T} u_i^{a_i}`. -/
theorem exists_eq_mul_prod_of_forall (a : ι → ℕ) {y : M} (hy : y ∈ flatDomain Φ) :
    ∀ (T : Finset ι),
      (∀ i ∈ T, ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ A i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i) = 0)) →
      (∀ i ∈ T, ∀ y ∈ A i, ∃ k, RegularAtDim (n := n) (A i) y k) →
      Set.InjOn σ T → ∀ {g : M → ℂ}, HolomorphicAt n g y →
      (∀ i ∈ T, ∃ c, HolomorphicAt n c y ∧ g =ᶠ[𝓝 y] fun z => c z * flatMap Φ z (σ i) ^ a i) →
      ∃ c, HolomorphicAt n c y ∧ g =ᶠ[𝓝 y] fun z => c z * ∏ i ∈ T, flatMap Φ z (σ i) ^ a i := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ _ _ g hg _
    exact ⟨g, hg, Eventually.of_forall fun z => by simp⟩
  | insert j T' hj ih =>
    intro hA' hreg' hσ g hg hdiv
    have hA : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ A j ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ j) = 0) :=
      fun hy1 hy2 => hA' j (Finset.mem_insert_self j T') hy1 hy2
    have hreg := hreg' j (Finset.mem_insert_self j T')
    obtain ⟨c', hc', hgc'⟩ := ih (fun i hi _ hy1 hy2 => hA' i (Finset.mem_insert_of_mem hi) hy1 hy2)
      (fun i hi => hreg' i (Finset.mem_insert_of_mem hi)) (hσ.mono (by simp)) hg
      fun i hi => hdiv i (Finset.mem_insert_of_mem hi)
    obtain ⟨d, hd, hgd⟩ := hdiv j (Finset.mem_insert_self j T')
    set u : M → ℂ := fun z => flatMap Φ z (σ j) with hu_def
    set p : M → ℂ := fun z => ∏ i ∈ T', flatMap Φ z (σ i) ^ a i with hp_def
    have hcoord : ∀ l, ∀ z ∈ flatDomain Φ, HolomorphicAt n (fun z => flatMap Φ z l) z :=
      fun l z hz => holomorphicAt_flatCoord Φ l hz
    have hph : ∀ z ∈ flatDomain Φ, HolomorphicAt n p z := fun z hz =>
      holomorphicAt_finset_prod T' fun i _ => CompanionReduction.holomorphicAt_pow_of (hcoord (σ i) z hz) (a i)
    have huh : HolomorphicAt n u y := hcoord (σ j) y hy
    -- the cofactor `c'` is divisible by `u^{a_j}`
    obtain ⟨c'', hc'', hc'eq⟩ : ∃ c'', HolomorphicAt n c'' y ∧
        c' =ᶠ[𝓝 y] fun z => c'' z * u z ^ a j := by
      by_cases huy : u y = 0
      · have hyA : y ∈ A j := (hA hy.1 hy.2).mpr huy
        obtain ⟨k, hk⟩ := hreg y hyA
        have hσj : σ j ∉ T'.image σ := by
          intro h
          obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp h
          have := hσ (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self j T') hij
          exact hj (this ▸ hi)
        -- near `y`: the two factorizations, holomorphy
        have key : ∀ᶠ z in 𝓝 y, z ∈ flatDomain Φ ∧ HolomorphicAt n d z ∧ HolomorphicAt n c' z ∧
            (∀ᶠ z' in 𝓝 z, g z' = c' z' * p z') ∧ (∀ᶠ z' in 𝓝 z, g z' = d z' * u z' ^ a j) := by
          filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy, hd.eventually_nhds, hc'.eventually_nhds,
            hgc'.eventually_nhds, hgd.eventually_nhds] with z h1 h2 h3 h4 h5
          exact ⟨h1, h2, h3, h4, h5⟩
        have hmem : (idealPow (vanishingIdeal (n := n) (A j)) (a j)).mem y c' := by
          refine mem_idealPow_vanishingIdeal_of_frequently hk hc' ?_
          refine ((frequently_flatMap_ne_zero hΦsrc hy (T'.image σ)).and_eventually
            key.eventually_nhds).mono ?_
          rintro y' ⟨⟨hy'D, hy'ne, hy'eq⟩, hy'key⟩
          have hy'A : y' ∈ A j := by
            refine (hA hy'D.1 hy'D.2).mpr ?_
            have := hy'eq (σ j) hσj
            change flatMap Φ y' (σ j) = 0
            rw [this]
            exact huy
          have hpy' : p y' ≠ 0 := by
            refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ ?_
            exact hy'ne (σ i) (Finset.mem_image_of_mem σ hi)
          have hpne : ∀ᶠ z in 𝓝 y', p z ≠ 0 :=
            (hph y' hy'D).continuousAt.eventually (isOpen_ne.mem_nhds hpy')
          refine ⟨hy'A, ?_⟩
          filter_upwards [hy'key, hpne.eventually_nhds] with z hzkey hzp hzA
          obtain ⟨hzD, hdz, -, hz1, hz2⟩ := hzkey
          have huz : u z = 0 := (hA hzD.1 hzD.2).mp hzA
          have hq : HolomorphicAt n (fun z' => d z' * (p z')⁻¹) z :=
            hdz.mul (BlowupFlatCoordinates.HolomorphicAt.inv (hph z hzD) hzp.self_of_nhds)
          have hupow : (idealPow (pointIdeal n z) (a j)).mem z (fun z' => u z' ^ a j) :=
            mem_idealPow_of_vanishesToOrderOn_univ
              (CodimOneCentre.vanishesToOrderOn_pow (mem_univ z) (hcoord (σ j) z hzD) huz (a j))
          refine mem_idealPow_congr (mul_mem_idealPow hq hupow) ?_
          filter_upwards [hz1, hz2, hzp] with z' h1 h2 h3
          have : c' z' = g z' / p z' := by rw [h1]; field_simp
          rw [this, h2]
          field_simp
        exact exists_eq_mul_pow_of_mem_idealPow
          (fun g hg => (vanishingIdeal_mem_iff_flatCoord Φ hA hy g).mp hg) hmem
      · refine ⟨fun z => c' z * ((u z)⁻¹) ^ a j,
          hc'.mul (CompanionReduction.holomorphicAt_pow_of
            (BlowupFlatCoordinates.HolomorphicAt.inv huh huy) _), ?_⟩
        filter_upwards [huh.continuousAt.eventually (isOpen_ne.mem_nhds huy)] with z hz
        rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hz, one_pow, mul_one]
    refine ⟨c'', hc'', ?_⟩
    filter_upwards [hgc', hc'eq] with z h1 h2
    rw [h1, h2, Finset.prod_insert hj]
    ring

end Factorization

/-! ### The monomial and nonmonomial parts -/

section Parts

open BoundaryCount NormalCrossings

variable {𝔞 : GermIdeal n M} {E : List (Set M)}

/-- The members of a simple normal crossings divisor are closed submanifolds. -/
theorem isClosedSubmanifold_get (hn : 0 < n) (hE : IsSNCDivisor n E) (i : Fin E.length) :
    IsClosedSubmanifold n (E.get i) := by
  have h := isClosedSubmanifold_memberInter hn hE {i}
  have heq : memberInter E {i} = E.get i := by
    ext y
    simp [memberInter]
  rwa [heq] at h

variable (n) in
/-- **The monomial part** `𝓜(𝔞)` (`hir:monomial-part-ambient`): at `y`, the germs lying in `𝓘_H^{e_H(y)}` for every
member `H` of `E` through `y`, where `e_H = divExp 𝔞 H` is the exponent of `𝔞` along `H`. -/
def monomialPart (𝔞 : GermIdeal n M) (E : List (Set M)) : GermIdeal n M where
  mem y g := HolomorphicAt n g y ∧ ∀ i : Fin E.length, y ∈ E.get i →
    (idealPow (vanishingIdeal (n := n) (E.get i)) (divExp n 𝔞 (E.get i) y)).mem y g

variable (n) in
/-- **The nonmonomial part** `𝓝(𝔞) = (𝔞 : 𝓜(𝔞))`. -/
def nonmonomialPart (𝔞 : GermIdeal n M) (E : List (Set M)) : GermIdeal n M where
  mem y h := HolomorphicAt n h y ∧ ∀ m, (monomialPart n 𝔞 E).mem y m → 𝔞.mem y (fun z => h z * m z)

/-- `𝔞 ⊆ 𝓜(𝔞)`: every germ of `𝔞` is divisible by the powers of the members given by the exponents. -/
theorem le_monomialPart (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent) :
    𝔞.Le (monomialPart n 𝔞 E) := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  intro y g hg
  refine ⟨hhol y g hg, fun i hyi => ?_⟩
  obtain ⟨k, hk⟩ := (isClosedSubmanifold_get hn hE i).2 y hyi
  exact (isDivNear_iff h𝔞 hk).mp (isDivNear_divExp hhol y) g hg

/-- **The monomial part is locally principal** (`hir:monomial-part-ambient`): near every point `x` it is generated by
one function `m = ∏_{H ∋ x} u_H^{e_H(x)}` (`u_H` a coordinate cutting out `H`), which vanishes identically near no
point. -/
theorem exists_generator_monomialPart (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent)
    (h0 : ∀ y, IsNonzeroAt 𝔞 y) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ m : M → ℂ, (∀ y ∈ U, HolomorphicAt n m y) ∧
      (∀ y ∈ U, ∃ᶠ z in 𝓝 y, m z ≠ 0) ∧
      ∀ y ∈ U, ∀ g, (monomialPart n 𝔞 E).mem y g ↔ IsInSpanAt (n := n) (· = m) y g := by
  classical
  obtain ⟨S, ⟨Φ, hΦsrc, -, hcoord⟩, hcard, hinj⟩ := hE.2 x
  set T : Finset (Fin E.length) := Finset.univ.filter fun i => x ∈ E.get i with hT_def
  set σ : Fin E.length → Fin n := fun i => if h : (S i).Nonempty then (S i).min' h else ⟨0, hn⟩
  have hSσ : ∀ i ∈ T, S i = {σ i} := by
    intro i hi
    have hxi : x ∈ E.get i := (Finset.mem_filter.mp hi).2
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hcard i hxi)
    simp [σ, ha]
  have hA : ∀ i ∈ T, ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i) = 0) := by
    intro i hi y hy1 hy2
    rw [hcoord i (Finset.mem_filter.mp hi).2 hy1 hy2, hSσ i hi]
    simp only [coordSubspace, Finset.mem_singleton, forall_eq, Set.mem_ofPred_eq]
    rfl
  have hreg : ∀ i ∈ T, ∀ y ∈ E.get i, ∃ k, RegularAtDim (n := n) (E.get i) y k :=
    fun i _ y hy => (isClosedSubmanifold_get hn hE i).2 y hy
  have hσ : Set.InjOn σ T := by
    intro i hi j hj hij
    apply hinj (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    rw [hSσ i hi, hSσ j hj, hij]
  set e : Fin E.length → ℕ := fun i => divExp n 𝔞 (E.get i) x
  set m : M → ℂ := fun z => ∏ i ∈ T, flatMap Φ z (σ i) ^ e i
  have hev : ∀ᶠ y in 𝓝 x, y ∈ flatDomain Φ ∧ (∀ i, y ∈ E.get i → i ∈ T) ∧
      ∀ i ∈ T, y ∈ E.get i → divExp n 𝔞 (E.get i) y = e i := by
    have hD : ∀ᶠ y in 𝓝 x, y ∈ flatDomain Φ := (isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)
    refine hD.and ((eventually_all.mpr fun i => ?_).and ((eventually_all_finset T).mpr fun i hi => ?_))
    · by_cases hxi : x ∈ E.get i
      · exact Eventually.of_forall fun _ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩
      · filter_upwards [(hE.1 _ (List.get_mem E i)).isOpen_compl.mem_nhds hxi] with y hy hyi
        exact absurd hyi hy
    · obtain ⟨k, hk⟩ := hreg i hi x (Finset.mem_filter.mp hi).2
      exact eventually_divExp_eq h𝔞 hk (Eventually.of_forall h0)
  obtain ⟨U, hUsub, hUo, hxU⟩ := eventually_nhds_iff.mp hev
  have hmhol : ∀ y ∈ flatDomain Φ, HolomorphicAt n m y := fun y hy =>
    holomorphicAt_finset_prod T fun i _ =>
      CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ i) hy) (e i)
  refine ⟨U, hUo, hxU, m, fun y hy => hmhol y (hUsub y hy).1, fun y hy => ?_,
    fun y hy g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · refine (frequently_flatMap_ne_zero hΦsrc (hUsub y hy).1 (T.image σ)).mono fun y' hy' => ?_
    exact Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hy'.2.1 (σ i) (Finset.mem_image_of_mem σ hi))
  · obtain ⟨hyD, -, hye⟩ := hUsub y hy
    have hdiv : ∀ i ∈ T, ∃ c, HolomorphicAt n c y ∧
        g =ᶠ[𝓝 y] fun z => c z * flatMap Φ z (σ i) ^ e i := by
      intro i hi
      by_cases hyi : y ∈ E.get i
      · have h1 := hg.2 i hyi
        rw [hye i hi hyi] at h1
        exact exists_eq_mul_pow_of_mem_idealPow
          (fun g hg => (vanishingIdeal_mem_iff_flatCoord Φ (hA i hi) hyD g).mp hg) h1
      · have huy : flatMap Φ y (σ i) ≠ 0 := fun h => hyi ((hA i hi hyD.1 hyD.2).mpr h)
        exact exists_eq_mul_pow_of_ne_zero (holomorphicAt_flatCoord Φ (σ i) hyD) huy hg.1 (e i)
    obtain ⟨c, hc, hgc⟩ := exists_eq_mul_prod_of_forall hΦsrc (A := fun i => E.get i) e hyD T hA hreg hσ
      hg.1 hdiv
    exact isInSpanAt_eq_iff.mpr ⟨hg.1, c, hc, hgc⟩
  · obtain ⟨hyD, hyT, hye⟩ := hUsub y hy
    obtain ⟨hgh, c, hc, hgc⟩ := isInSpanAt_eq_iff.mp hg
    refine ⟨hgh, fun i hyi => ?_⟩
    have hi := hyT i hyi
    rw [hye i hi hyi]
    have hu : (vanishingIdeal (n := n) (E.get i)).mem y (fun z => flatMap Φ z (σ i)) := by
      refine ⟨holomorphicAt_flatCoord Φ (σ i) hyD, ?_⟩
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds hyD] with z hz hzi
      exact (hA i hi hz.1 hz.2).mp hzi
    have hpow := pow_mem_idealPow hu (holomorphicAt_flatCoord Φ (σ i) hyD) (e i)
    have hrest : HolomorphicAt n (fun z => c z * ∏ j ∈ T.erase i, flatMap Φ z (σ j) ^ e j) y :=
      hc.mul (holomorphicAt_finset_prod _ fun j _ =>
        CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ j) hyD) (e j))
    refine mem_idealPow_congr (mul_mem_idealPow hrest hpow) ?_
    filter_upwards [hgc] with z hz
    rw [hz]
    simp only [m]
    rw [← Finset.mul_prod_erase T (fun j => flatMap Φ z (σ j) ^ e j) hi]
    ring

/-- A germ of a coherent ideal stays in it under germ equality. -/
theorem mem_congr_of_isCoherent {𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) {y : M} {g g' : M → ℂ}
    (hg : 𝔟.mem y g) (hgg : g =ᶠ[𝓝 y] g') : 𝔟.mem y g' :=
  GermIdealTotalTransform.mem_of_isInSpanAt_mem h𝔟 (isInSpanAt_of_eq_mul hg
    ((RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hg).congr hgg)
    (holomorphicAt_const 1) (hgg.symm.mono fun _ hz => by simp [hz]))

/-- **A germ that vanishes identically near no point is a non-zero-divisor**: if `f m = 0` near `y`, `m` holomorphic
at `y` and not vanishing near `y`, then `f = 0` near `y` (orders add, and a germ of infinite order vanishes). -/
theorem eventually_eq_zero_of_mul_eventually_eq_zero {f m : M → ℂ} {y : M} (hf : HolomorphicAt n f y)
    (hm : HolomorphicAt n m y) (hmne : ∃ᶠ z in 𝓝 y, m z ≠ 0)
    (h : (fun z => f z * m z) =ᶠ[𝓝 y] fun _ => 0) : f =ᶠ[𝓝 y] fun _ => 0 := by
  obtain ⟨b, hb⟩ := exists_notMem_idealPow_of_frequently hm hmne
  rcases b with _ | b
  · exact absurd hm hb
  refine eventually_eq_zero_of_forall_mem_idealPow hf fun q => ?_
  have hfm : (idealPow (pointIdeal n y) (q + b)).mem y (fun z => f z * m z) :=
    mem_idealPow_congr (zero_mem_idealPow _ y _) h.symm
  exact mem_idealPow_of_mul_mem hf hm hb hfm

variable (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent) (h0 : ∀ y, IsNonzeroAt 𝔞 y)

include hn hE h𝔞 h0 in
/-- **The monomial part is coherent.** -/
theorem isCoherent_monomialPart : (monomialPart n 𝔞 E).IsCoherent := by
  intro x
  obtain ⟨U, hUo, hxU, m, hmh, -, hgen⟩ := exists_generator_monomialPart hn hE h𝔞 h0 x
  refine ⟨U, hUo, hxU, 1, fun _ => m, fun _ z hz => (hmh z hz).mdifferentiableAt.mdifferentiableWithinAt,
    fun y hy g => ?_⟩
  rw [hgen y hy g]
  exact (isInSpanAt_range_one_iff m g).symm

include hn hE h𝔞 h0 in
/-- **Factorization of a germ of `𝔞`**: every `g ∈ 𝔞_y` is `c · m` near `y` with `c ∈ 𝓝(𝔞)_y`, `m ∈ 𝓜(𝔞)_y`. -/
theorem exists_mem_nonmonomialPart_mul (y : M) {g : M → ℂ} (hg : 𝔞.mem y g) :
    ∃ c m, (nonmonomialPart n 𝔞 E).mem y c ∧ (monomialPart n 𝔞 E).mem y m ∧
      g =ᶠ[𝓝 y] fun z => c z * m z := by
  obtain ⟨U, hUo, hyU, m, hmh, -, hgen⟩ := exists_generator_monomialPart hn hE h𝔞 h0 y
  obtain ⟨-, c, hc, hgc⟩ := isInSpanAt_eq_iff.mp ((hgen y hyU g).mp (le_monomialPart hn hE h𝔞 y g hg))
  have hmM : (monomialPart n 𝔞 E).mem y m := (hgen y hyU m).mpr
    (isInSpanAt_of_eq_mul rfl (hmh y hyU) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm))
  refine ⟨c, m, ⟨hc, fun m' hm' => ?_⟩, hmM, hgc⟩
  obtain ⟨-, c', hc', hm'c⟩ := isInSpanAt_eq_iff.mp ((hgen y hyU m').mp hm')
  refine mem_congr_of_isCoherent h𝔞 (CompanionReduction.mul_mem_of_isCoherent h𝔞 hc' hg) ?_
  filter_upwards [hgc, hm'c] with z h1 h2
  rw [h2, h1]
  ring

include hn hE h𝔞 h0 in
/-- **`𝔞 = 𝓝(𝔞) · 𝓜(𝔞)`** (`hir:monomial-part-ambient`). -/
theorem eq_mul_monomialPart : 𝔞 = (nonmonomialPart n 𝔞 E).mul (monomialPart n 𝔞 E) := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · obtain ⟨c, m, hc, hm, hgc⟩ := exists_mem_nonmonomialPart_mul hn hE h𝔞 h0 y hg
    change IsInSpanAt (n := n) (fun s => ∃ a b, (nonmonomialPart n 𝔞 E).mem y a ∧
      (monomialPart n 𝔞 E).mem y b ∧ s = a * b) y g
    exact isInSpanAt_of_eq_mul (s := c * m) ⟨c, m, hc, hm, rfl⟩ (hhol y g hg) (holomorphicAt_const 1)
      (hgc.mono fun z hz => by rw [hz]; simp)
  · change IsInSpanAt (n := n) (fun s => ∃ a b, (nonmonomialPart n 𝔞 E).mem y a ∧
      (monomialPart n 𝔞 E).mem y b ∧ s = a * b) y g at hg
    refine GermIdealTotalTransform.mem_of_isInSpanAt_mem h𝔞 (IsInSpanAt.mono ?_ hg)
    rintro s ⟨a, b, ha, hb, rfl⟩
    exact ha.2 b hb

include hn hE h𝔞 h0 in
/-- **The nonmonomial part is contained in the ideal of no member at its points**: at `y ∈ H` some germ of
`𝓝(𝔞)_y` does not vanish on `H` near `y`. -/
theorem exists_mem_nonmonomialPart_notMem {y : M} {i : Fin E.length} (hyi : y ∈ E.get i) :
    ∃ h, (nonmonomialPart n 𝔞 E).mem y h ∧ ¬ (vanishingIdeal (n := n) (E.get i)).mem y h := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  obtain ⟨k, hk⟩ := (isClosedSubmanifold_get hn hE i).2 y hyi
  have hnot := not_isDivNear_divExp_succ hhol hyi (h0 y)
  rw [isDivNear_iff h𝔞 hk] at hnot
  push Not at hnot
  obtain ⟨g, hg, hgnot⟩ := hnot
  obtain ⟨c, m, hc, hm, hgc⟩ := exists_mem_nonmonomialPart_mul hn hE h𝔞 h0 y hg
  refine ⟨c, hc, fun hcI => hgnot ?_⟩
  refine mem_idealPow_congr (mul_mem_idealPow_succ (hm.2 i hyi) hcI (hm.1.mul hc.1)) ?_
  filter_upwards [hgc] with z hz
  rw [hz, mul_comm]

include hn hE h𝔞 h0 in
/-- **The nonmonomial part is coherent**: near `x` it is generated by the quotients `t_k = s_k / m` of generators of
`𝔞` by the generator `m` of the monomial part. -/
theorem isCoherent_nonmonomialPart : (nonmonomialPart n 𝔞 E).IsCoherent := by
  intro x
  obtain ⟨U₀, hU₀o, hxU₀, m, hmh, hmne, hgen⟩ := exists_generator_monomialPart hn hE h𝔞 h0 x
  obtain ⟨U₁, hU₁o, hxU₁, K, s, hs, hgen𝔞⟩ := h𝔞 x
  have hshol : ∀ k, ∀ z ∈ U₁, HolomorphicAt n (s k) z := fun k _ hz =>
    holomorphicAt_of_mdifferentiableOn_open hU₁o (hs k) hz
  have hsmem : ∀ k, ∀ z ∈ U₁, 𝔞.mem z (s k) := fun k z hz => (hgen𝔞 z hz (s k)).mpr
    (isInSpanAt_of_eq_mul ⟨k, rfl⟩ (hshol k z hz) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm))
  have hdiv : ∀ k, ∃ t, HolomorphicAt n t x ∧ s k =ᶠ[𝓝 x] fun z => t z * m z := fun k =>
    (isInSpanAt_eq_iff.mp ((hgen x hxU₀ (s k)).mp
      (le_monomialPart hn hE h𝔞 x (s k) (hsmem k x hxU₁)))).2
  choose t ht hst using hdiv
  have hev : ∀ᶠ z in 𝓝 x, z ∈ U₀ ∧ z ∈ U₁ ∧ ∀ k, HolomorphicAt n (t k) z ∧ s k z = t k z * m z := by
    have h1 : ∀ᶠ z in 𝓝 x, z ∈ U₀ := hU₀o.mem_nhds hxU₀
    have h2 : ∀ᶠ z in 𝓝 x, z ∈ U₁ := hU₁o.mem_nhds hxU₁
    filter_upwards [h1, h2, eventually_all.mpr fun k => (ht k).eventually_nhds,
      eventually_all.mpr hst] with z hz1 hz2 hz3 hz4
    exact ⟨hz1, hz2, fun k => ⟨hz3 k, hz4 k⟩⟩
  obtain ⟨V, hVsub, hVo, hxV⟩ := eventually_nhds_iff.mp hev
  have hstV : ∀ k, ∀ y ∈ V, s k =ᶠ[𝓝 y] fun z => t k z * m z := fun k y hy =>
    Filter.eventually_of_mem (hVo.mem_nhds hy) fun z hz => ((hVsub z hz).2.2 k).2
  refine ⟨V, hVo, hxV, K, t, fun k z hz => ((hVsub z hz).2.2 k).1.mdifferentiableAt.mdifferentiableWithinAt,
    fun y hy h => ⟨fun hh => ?_, fun hh => ?_⟩⟩
  · obtain ⟨hyU₀, hyU₁, -⟩ := hVsub y hy
    have hmM : (monomialPart n 𝔞 E).mem y m := (hgen y hyU₀ m).mpr
      (isInSpanAt_of_eq_mul rfl (hmh y hyU₀) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm))
    obtain ⟨-, K', r, a, hr, ha, hsum⟩ := (hgen𝔞 y hyU₁ _).mp (hh.2 m hmM)
    choose ρ hρ using hr
    have htρ : ∀ j, HolomorphicAt n (t (ρ j)) y := fun j => ((hVsub y hy).2.2 (ρ j)).1
    -- `(h - ∑ a_j t_{ρ j}) m = 0` near `y`
    have hzero : (fun z => (h z - ∑ j, a j z * t (ρ j) z) * m z) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hsum, eventually_all.mpr fun j => hstV (ρ j) y hy] with z hz hz'
      rw [sub_mul, hz, Finset.sum_mul]
      refine sub_eq_zero.mpr (Finset.sum_congr rfl fun j _ => ?_)
      rw [← hρ j, hz' j]
      ring
    have hdiff := eventually_eq_zero_of_mul_eventually_eq_zero
      (holomorphicAt_sub hh.1 (HolomorphicAt.sum _ fun j _ => (ha j).mul (htρ j))) (hmh y hyU₀)
      (hmne y hyU₀) hzero
    refine ⟨hh.1, K', fun j => t (ρ j), a, fun j => ⟨ρ j, rfl⟩, ha, ?_⟩
    filter_upwards [hdiff] with z hz
    exact sub_eq_zero.mp hz
  · obtain ⟨hyU₀, hyU₁, -⟩ := hVsub y hy
    refine ⟨hh.1, fun m' hm' => ?_⟩
    obtain ⟨-, c, hc, hm'c⟩ := isInSpanAt_eq_iff.mp ((hgen y hyU₀ m').mp hm')
    obtain ⟨hhh, K', r, a, hr, ha, hsum⟩ := hh
    choose ρ hρ using hr
    refine GermIdealTotalTransform.mem_of_isInSpanAt_mem h𝔞
      ⟨hhh.mul ((hc.mul (hmh y hyU₀)).congr hm'c.symm), K', fun j => s (ρ j),
        fun j => c * a j, fun j => hsmem (ρ j) y hyU₁, fun j => hc.mul (ha j), ?_⟩
    filter_upwards [hsum, hm'c, eventually_all.mpr fun j => hstV (ρ j) y hy] with z hz hz' hz''
    rw [hz, hz', Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz'' j, hρ j]
    simp only [Pi.mul_apply]
    ring

end Parts

end

end Hironaka.MonomialPart
