import Hironaka.Analytic.IdealPowers

set_option autoImplicit false

/-!
# The order of an ideal sheaf at a point, relative to a submanifold

Blueprint `hir:order` (`blueprint/src/hironaka.tex`, Hironaka phase H1).  Sources:
Włodarczyk 2005 §2.1 (`ord_x(𝓘) := max{i | 𝓘 ⊂ 𝔪_x^i}`, `supp(X, 𝓘, E, μ) = {x | ord_x 𝓘 ≥ μ}`) and
Bierstone--Milman 2008, Definitions 2.1 (the cosupport `{x ∈ N | ord_x 𝓘 ≥ d}` of a marked ideal
`(M, N, E, 𝓘, d)`, with `ord_x 𝓘` the largest `q` such that `𝓘_x ⊂ 𝔪^q_{N,x}`).

## The ambient encoding

An ideal of `𝒪_N`, for a closed submanifold `N ⊆ M`, is represented by an ideal sheaf `𝔞` of `𝒪_M`
(a `GermIdeal`); only the restrictions `g|_N` of its germs matter.  Since `𝒪_{N,x} = 𝒪_{M,x}/𝓘_{N,x}`
and the maximal ideal of `𝒪_{N,x}` is the image of `𝔪_x = 𝓘_{{x}}`, the germ `g|_N` lies in
`𝔪_{N,x}^q` exactly when `g` agrees on `N`, near `x`, with a germ of `𝔪_x^q`.  That is the definition
of `VanishesToOrderOn` below, and it needs no chart and no submanifold structure on `N`.  For `N = M`
it is Włodarczyk's `ord_x`.

## Main declarations

* `pointIdeal x` -- the maximal ideal sheaf `𝔪_x = 𝓘_{{x}}`;
* `VanishesToOrderOn n N x q g` -- `g|_N ∈ 𝔪_{N,x}^q`; `OrderGE n N 𝔞 x q` -- `ord_x(𝔞|_N) ≥ q`;
* `order n N 𝔞 x : ℕ∞` -- `ord_x(𝔞|_N)`, with `le_order_iff`;
* `cosupport n N 𝔞 d` -- `{x ∈ N | ord_x(𝔞|_N) ≥ d}`;
* the elementary facts: `𝔪^{q+1} ⊆ 𝔪^q` (`idealPow_pointIdeal_succ_le`), monotonicity in `q`,
  order `≥ 0` for holomorphic germs, order `≥ 1` iff vanishing at the point
  (`vanishesToOrderOn_one_iff`), `cosupport_zero`, `cosupport_one`, `cosupport_unitIdeal`,
  multiplicativity `𝔪^p 𝔪^q ⊆ 𝔪^{p+q}` (`VanishesToOrderOn.mul`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`, so that those two statements can
later be proved in place from it.

Sorry-free.  The Taylor characterisation of `𝔪_x^q` by vanishing derivatives (needed for
`supp(𝓘, μ) = V(𝓓^{μ-1} 𝓘)`) is the next H1 item, not done here.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.GermIdealOrder

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightPowers

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-! ### The maximal ideal of a point and its powers -/

variable (n) in
/-- The maximal ideal sheaf `𝔪_x = 𝓘_{{x}}` of a point. -/
def pointIdeal (x : M) : GermIdeal n M := vanishingIdeal {x}

theorem mem_pointIdeal_iff {x y : M} {g : M → ℂ} :
    (pointIdeal n x).mem y g ↔ HolomorphicAt n g y ∧ ∀ᶠ z in 𝓝 y, z = x → g z = 0 :=
  Iff.rfl

/-- A germ of `𝔪_x` at `x` vanishes at `x`. -/
theorem apply_eq_zero_of_mem_pointIdeal {x : M} {g : M → ℂ} (hg : (pointIdeal n x).mem x g) :
    g x = 0 :=
  hg.2.self_of_nhds rfl

/-- A function holomorphic at `x` and vanishing at `x` is a germ of `𝔪_x`. -/
theorem mem_pointIdeal_of_apply_eq_zero {x : M} {g : M → ℂ} (hg : HolomorphicAt n g x)
    (hx : g x = 0) : (pointIdeal n x).mem x g :=
  ⟨hg, Eventually.of_forall fun _ hz => hz ▸ hx⟩

theorem mem_idealPow_succ_iff {𝔞 : GermIdeal n M} {q : ℕ} {y : M} {g : M → ℂ} :
    (idealPow 𝔞 (q + 1)).mem y g ↔
      IsInSpanAt (n := n)
        (fun s => ∃ a b, (idealPow 𝔞 q).mem y a ∧ 𝔞.mem y b ∧ s = a * b) y g :=
  Iff.rfl

/-- Every germ of a power of `𝔪_x` (more generally of a power of an ideal of holomorphic germs) is
holomorphic. -/
theorem holomorphicAt_of_mem_idealPow {𝔞 : GermIdeal n M} {y : M} {g : M → ℂ} :
    ∀ {q : ℕ}, (idealPow 𝔞 q).mem y g → HolomorphicAt n g y
  | 0, hg => hg
  | _ + 1, hg => hg.1

/-- The stalk of a power `𝔞^q` (`𝔞` an ideal of holomorphic germs) is closed under multiplication
by holomorphic germs. -/
theorem mul_mem_idealPow {𝔞 : GermIdeal n M} {y : M} {g c : M → ℂ} (hc : HolomorphicAt n c y) :
    ∀ {q : ℕ}, (idealPow 𝔞 q).mem y g → (idealPow 𝔞 q).mem y (fun z => c z * g z)
  | 0, hg => HolomorphicAt.mul hc hg
  | _ + 1, hg => mem_idealPow_succ_iff.mpr
      (RelativePrincipalizationSpan.IsInSpanAt.mul_left hc (mem_idealPow_succ_iff.mp hg))

/-- The stalk of a power `𝔞^q` is closed under finite holomorphic combinations. -/
theorem mem_idealPow_of_isInSpanAt {𝔞 : GermIdeal n M} {y : M} {g : M → ℂ} :
    ∀ {q : ℕ}, IsInSpanAt (n := n) ((idealPow 𝔞 q).mem y) y g → (idealPow 𝔞 q).mem y g
  | 0, hg => hg.holomorphicAt
  | _ + 1, hg => mem_idealPow_succ_iff.mpr
      (RelativePrincipalizationSpan.IsInSpanAt.trans (fun _ hs => mem_idealPow_succ_iff.mp hs) hg)

/-- `𝔞^{q+1} ⊆ 𝔞^q` for an ideal `𝔞` of holomorphic germs. -/
theorem idealPow_succ_le {𝔞 : GermIdeal n M}
    (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y) (q : ℕ) :
    (idealPow 𝔞 (q + 1)).Le (idealPow 𝔞 q) := by
  intro y g hg
  refine mem_idealPow_of_isInSpanAt ((mem_idealPow_succ_iff.mp hg).mono ?_)
  rintro s ⟨a, b, ha, hb, rfl⟩
  have := mul_mem_idealPow (q := q) (h𝔞 y b hb) ha
  refine (congrArg (fun F => (idealPow 𝔞 q).mem y F) ?_).mp this
  funext z
  exact mul_comm _ _

/-- `𝔞^p ⊆ 𝔞^q` for `q ≤ p`. -/
theorem idealPow_le_of_le {𝔞 : GermIdeal n M}
    (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y) {p q : ℕ} (hqp : q ≤ p) :
    (idealPow 𝔞 p).Le (idealPow 𝔞 q) := by
  induction p, hqp using Nat.le_induction with
  | base => exact fun _ _ h => h
  | succ p _ ih => exact fun y g hg => ih y g (idealPow_succ_le h𝔞 p y g hg)

theorem holomorphicAt_of_mem_pointIdeal {x y : M} {g : M → ℂ} (hg : (pointIdeal n x).mem y g) :
    HolomorphicAt n g y :=
  hg.1

/-- `𝔪_x^{q+1} ⊆ 𝔪_x^q`. -/
theorem idealPow_pointIdeal_succ_le (x : M) (q : ℕ) :
    (idealPow (pointIdeal n x) (q + 1)).Le (idealPow (pointIdeal n x) q) :=
  idealPow_succ_le (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg) q

/-- A germ of `𝔪_x^q` with `q ≥ 1` vanishes at `x`. -/
theorem apply_eq_zero_of_mem_idealPow_pointIdeal {x : M} {g : M → ℂ} {q : ℕ} (hq : 1 ≤ q)
    (hg : (idealPow (pointIdeal n x) q).mem x g) : g x = 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hq
  obtain ⟨-, N, s, a, hs, -, hsum⟩ := hg
  rw [hsum.self_of_nhds]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨b, c, -, hc, hsi⟩ := hs i
  rw [hsi]
  simp [apply_eq_zero_of_mem_pointIdeal hc]

/-- `𝔪_x^p · 𝔪_x^q ⊆ 𝔪_x^{p+q}` (in fact for any ideal of holomorphic germs). -/
theorem mul_mem_idealPow_add {𝔞 : GermIdeal n M}
    (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y) {y : M} {f g : M → ℂ} {p : ℕ}
    (hf : (idealPow 𝔞 p).mem y f) :
    ∀ {q : ℕ}, (idealPow 𝔞 q).mem y g → (idealPow 𝔞 (p + q)).mem y (fun z => f z * g z)
  | 0, hg => by
    simpa [mul_comm] using mul_mem_idealPow (q := p) hg hf
  | q + 1, hg => by
    -- `g = ∑ aᵢ (bᵢ cᵢ)` with `bᵢ ∈ 𝔞^q`, `cᵢ ∈ 𝔞`; then `f g = ∑ aᵢ ((f bᵢ) cᵢ)`.
    obtain ⟨hghol, N, s, a, hs, ha, hsum⟩ := mem_idealPow_succ_iff.mp hg
    have hfhol := holomorphicAt_of_mem_idealPow hf
    refine mem_idealPow_succ_iff.mpr
      ⟨hfhol.mul hghol, N, fun i z => f z * s i z, a, fun i => ?_, ha, ?_⟩
    · obtain ⟨b, c, hb, hc, hsi⟩ := hs i
      refine ⟨fun z => f z * b z, c, mul_mem_idealPow_add h𝔞 hf hb, hc, ?_⟩
      show (fun z => f z * s i z) = (fun z => f z * b z) * c
      rw [hsi]
      funext z
      simp only [Pi.mul_apply]
      ring
    · filter_upwards [hsum] with z hz
      rw [hz, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Vanishing order along a submanifold -/

variable (n) in
/-- **`g|_N ∈ 𝔪_{N,x}^q`**: near `x`, the function `g` agrees on `N` with a germ of `𝔪_x^q`. -/
def VanishesToOrderOn (N : Set M) (x : M) (q : ℕ) (g : M → ℂ) : Prop :=
  ∃ h : M → ℂ, (idealPow (pointIdeal n x) q).mem x h ∧ ∀ᶠ y in 𝓝 x, y ∈ N → g y = h y

variable {N : Set M} {x : M} {g : M → ℂ}

/-- Monotonicity in the order. -/
theorem VanishesToOrderOn.mono {p q : ℕ} (hqp : q ≤ p) (hg : VanishesToOrderOn n N x p g) :
    VanishesToOrderOn n N x q g := by
  obtain ⟨h, hh, hgh⟩ := hg
  exact ⟨h, idealPow_le_of_le (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg) hqp x h hh, hgh⟩

/-- Monotonicity in the submanifold. -/
theorem VanishesToOrderOn.mono_set {N' : Set M} (hN : N' ⊆ N) {q : ℕ}
    (hg : VanishesToOrderOn n N x q g) : VanishesToOrderOn n N' x q g := by
  obtain ⟨h, hh, hgh⟩ := hg
  exact ⟨h, hh, hgh.mono fun y hy hyN => hy (hN hyN)⟩

/-- Every holomorphic germ vanishes to order `0`. -/
theorem vanishesToOrderOn_zero (hg : HolomorphicAt n g x) : VanishesToOrderOn n N x 0 g :=
  ⟨g, hg, Eventually.of_forall fun _ _ => rfl⟩

/-- Order `≥ 1` along `N` at a point `x ∈ N` means vanishing at `x`. -/
theorem vanishesToOrderOn_one_iff (hx : x ∈ N) (hg : HolomorphicAt n g x) :
    VanishesToOrderOn n N x 1 g ↔ g x = 0 := by
  constructor
  · rintro ⟨h, hh, hgh⟩
    rw [hgh.self_of_nhds hx]
    exact apply_eq_zero_of_mem_idealPow_pointIdeal le_rfl hh
  · intro hx0
    refine ⟨g, ?_, Eventually.of_forall fun _ _ => rfl⟩
    refine mem_idealPow_succ_iff.mpr (isInSpanAt_of_eq_mul (s := (fun _ => (1 : ℂ)) * g)
      (a := fun _ => (1 : ℂ)) ⟨fun _ => (1 : ℂ), g, holomorphicAt_const 1,
        mem_pointIdeal_of_apply_eq_zero hg hx0, rfl⟩ hg (holomorphicAt_const 1)
      (Eventually.of_forall fun z => by simp))

/-- **Multiplicativity**: orders add under products. -/
theorem VanishesToOrderOn.mul {f : M → ℂ} {p q : ℕ} (hf : VanishesToOrderOn n N x p f)
    (hg : VanishesToOrderOn n N x q g) :
    VanishesToOrderOn n N x (p + q) (fun y => f y * g y) := by
  obtain ⟨h, hh, hfh⟩ := hf
  obtain ⟨k, hk, hgk⟩ := hg
  refine ⟨fun y => h y * k y,
    mul_mem_idealPow_add (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg) hh hk, ?_⟩
  filter_upwards [hfh, hgk] with y hy1 hy2 hyN
  rw [hy1 hyN, hy2 hyN]

/-- A holomorphic multiple keeps the order. -/
theorem VanishesToOrderOn.mul_left {c : M → ℂ} (hc : HolomorphicAt n c x) {q : ℕ}
    (hg : VanishesToOrderOn n N x q g) : VanishesToOrderOn n N x q (fun y => c y * g y) := by
  simpa using (vanishesToOrderOn_zero (N := N) hc).mul hg

/-! ### The order of an ideal -/

variable (n) in
/-- **`ord_x(𝔞|_N) ≥ q`**: every germ of `𝔞` at `x` vanishes to order `q` along `N`. -/
def OrderGE (N : Set M) (𝔞 : GermIdeal n M) (x : M) (q : ℕ) : Prop :=
  ∀ g, 𝔞.mem x g → VanishesToOrderOn n N x q g

variable {𝔞 : GermIdeal n M}

theorem OrderGE.mono {p q : ℕ} (hqp : q ≤ p) (h : OrderGE n N 𝔞 x p) : OrderGE n N 𝔞 x q :=
  fun g hg => (h g hg).mono hqp

/-- For an ideal of holomorphic germs the order is always `≥ 0`. -/
theorem orderGE_zero (h𝔞 : ∀ g, 𝔞.mem x g → HolomorphicAt n g x) : OrderGE n N 𝔞 x 0 :=
  fun g hg => vanishesToOrderOn_zero (h𝔞 g hg)

variable (n) in
/-- **The order `ord_x(𝔞|_N) ∈ ℕ∞`**: the supremum of the `q` with `𝔞_x|_N ⊆ 𝔪_{N,x}^q`
(`⊤` when `𝔞|_N` vanishes near `x`, e.g. for the zero ideal). -/
def order (N : Set M) (𝔞 : GermIdeal n M) (x : M) : ℕ∞ :=
  ⨆ (q : ℕ) (_ : OrderGE n N 𝔞 x q), (q : ℕ∞)

/-- **`q ≤ ord_x(𝔞|_N)` iff `ord_x(𝔞|_N) ≥ q`** (for an ideal of holomorphic germs). -/
theorem le_order_iff (h𝔞 : ∀ g, 𝔞.mem x g → HolomorphicAt n g x) {q : ℕ} :
    (q : ℕ∞) ≤ order n N 𝔞 x ↔ OrderGE n N 𝔞 x q := by
  constructor
  · intro hq
    by_contra hnot
    have hlt : ∀ k : ℕ, OrderGE n N 𝔞 x k → k < q := fun k hk => by
      by_contra hkq
      exact hnot (hk.mono (not_lt.mp hkq))
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · exact hnot (orderGE_zero h𝔞)
    have hle : order n N 𝔞 x ≤ ((q - 1 : ℕ) : ℕ∞) :=
      iSup₂_le fun k hk => by exact_mod_cast Nat.le_sub_one_of_lt (hlt k hk)
    have := hq.trans hle
    have : q ≤ q - 1 := by exact_mod_cast this
    omega
  · intro hq
    exact le_iSup₂ (f := fun (k : ℕ) (_ : OrderGE n N 𝔞 x k) => (k : ℕ∞)) q hq

/-! ### The cosupport -/

variable (n) in
/-- **The cosupport** `{x ∈ N | ord_x(𝔞|_N) ≥ d}` of the marked ideal `(𝔞|_N, d)`
(Włodarczyk's `supp(𝓘, μ)`, BM08's `cosupp`). -/
def cosupport (N : Set M) (𝔞 : GermIdeal n M) (d : ℕ) : Set M :=
  {x | x ∈ N ∧ OrderGE n N 𝔞 x d}

theorem cosupport_subset (d : ℕ) : cosupport n N 𝔞 d ⊆ N := fun _ hx => hx.1

theorem cosupport_anti {d d' : ℕ} (hdd' : d ≤ d') :
    cosupport n N 𝔞 d' ⊆ cosupport n N 𝔞 d :=
  fun _ hx => ⟨hx.1, hx.2.mono hdd'⟩

/-- With the mark `0` the cosupport is all of `N` (for an ideal of holomorphic germs). -/
theorem cosupport_zero (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    cosupport n N 𝔞 0 = N :=
  Subset.antisymm (cosupport_subset 0) fun x hx => ⟨hx, orderGE_zero (h𝔞 x)⟩

/-- With the mark `1` the cosupport is the zero locus on `N` (Włodarczyk: `supp(𝓘, 1) = supp 𝓘`). -/
theorem cosupport_one (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    cosupport n N 𝔞 1 = N ∩ 𝔞.zeroLocus := by
  ext x
  constructor
  · rintro ⟨hxN, hx⟩
    exact ⟨hxN, fun g hg => (vanishesToOrderOn_one_iff hxN (h𝔞 x g hg)).mp (hx g hg)⟩
  · rintro ⟨hxN, hx⟩
    exact ⟨hxN, fun g hg => (vanishesToOrderOn_one_iff hxN (h𝔞 x g hg)).mpr (hx g hg)⟩

/-- The unit ideal has empty cosupport for every positive mark. -/
theorem cosupport_unitIdeal {d : ℕ} (hd : 1 ≤ d) : cosupport n N (unitIdeal n M) d = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  have h1 := (hx.2 (fun _ => (1 : ℂ)) (holomorphicAt_const 1)).mono hd
  have := (vanishesToOrderOn_one_iff hx.1 (holomorphicAt_const (n := n) (M := M) (x := x) 1)).mp h1
  exact one_ne_zero this

end

end Hironaka.GermIdealOrder
