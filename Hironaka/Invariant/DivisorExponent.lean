import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Invariant.OrderMultiplicativity
import Hironaka.Analytic.GermOrderProduct
import Hironaka.Analytic.HolomorphicAnalytic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Exponents of an ideal along a submanifold

Blueprint `hir:divisor-exponent` (`blueprint/src/hironaka.tex`, Hironaka phase H4, the first half of H2 item 1 of
TN-CLASSICAL's list, `N = M`).  Sources: Bierstone--Milman 2008, §5 (the monomial part `𝓜(𝓘)` of a marked ideal: the
largest power of the ideal of each member of `E` dividing `𝓘`), Włodarczyk 2005, Step 2 (the decomposition
`𝓘 = 𝓜(𝓘) 𝓝(𝓘)` with `𝓜(𝓘) = 𝓘_{D_1}^{a_1} ⋯ 𝓘_{D_k}^{a_k}`).

For an ideal `𝔞` of holomorphic germs and a closed submanifold `H` (in the application a member of `E`) put
`IsDivNear 𝔞 H e x` when, near `x`, the points of `H` lie in `cosupp(𝔞, e)`; for coherent `𝔞` and `x ∈ H` this is
`𝔞_x ⊆ (𝓘_H^e)_x` (`isDivNear_iff`, a local Hadamard bridge).  The **exponent** `divExp 𝔞 H x` is the largest such `e`.

* `eventually_eq_zero_of_forall_mem_idealPow`: a germ lying in every power `𝔪_x^q` vanishes near `x` (Krull, from the
  power series); hence the exponent is finite when `𝔞_x` contains a germ that does not vanish near `x`
  (`exists_not_isDivNear`).
* `isDivNear_of_frequently` (**identity principle along `H`**): if points `y ∈ H` with `IsDivNear 𝔞 H e y` accumulate at
  `x ∈ H`, then `IsDivNear 𝔞 H e x`.  In flat coordinates `ψ` at `x` (`H = ψ⁻¹(ℂᵏ × 0)`), the derivatives of order `< e`
  of the generators `s_i ∘ ψ⁻¹`, restricted to `ℂᵏ × 0` (composed with the retraction `P`), are holomorphic on the convex
  set `P⁻¹(B)` and vanish on a nonempty open subset of it, hence on `ℂᵏ × 0` near `0`; TN23's Taylor lemma gives
  `s_i ∈ 𝓘_H^e` at `x`.
* `divExp`, `isDivNear_iff_le_divExp`, and **local constancy** `eventually_divExp_eq`: `divExp 𝔞 H` is locally constant
  on `H`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.DivisorExponent

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.DerivativeIdeal Hironaka.HolomorphicTaylorTail
  Hironaka.OrderTaylor Hironaka.BlowupFlatCoordinates
  Hironaka.HadamardBridge Hironaka.HadamardBridgeAlong
  Hironaka.IdealOrderArithmetic Hironaka.GiraudAlong
  Hironaka.OrderMultiplicativity Hironaka.GermOrderProduct
  Hironaka.HolomorphicAnalytic

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Krull: a germ of infinite order vanishes -/

section Krull

/-- **A germ lying in every power of `𝔪_x` vanishes near `x`** (its Taylor series is zero). -/
theorem eventually_eq_zero_of_forall_mem_idealPow {x : M} {g : M → ℂ} (hg : HolomorphicAt n g x)
    (h : ∀ q, (idealPow (pointIdeal n x) q).mem x g) : g =ᶠ[𝓝 x] fun _ => 0 := by
  set e := complexChartAt (n := n) x
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  set G := g ∘ e.val.symm
  have hall : ∀ j, iteratedFDeriv ℂ j G (e.val x) = 0 := fun j =>
    (mem_idealPow_pointIdeal_iff_iteratedFDeriv hg (j + 1)).mp (h (j + 1)) j (Nat.lt_succ_self j)
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp (eventually_differentiableAt_comp_symm e hxe hg)
  have hGan : AnalyticAt ℂ G (e.val x) :=
    analyticOnNhd_of_differentiableOn hUo (fun z hz => (hU z hz).differentiableWithinAt) _ hpU
  obtain ⟨p, r, hp⟩ := hGan
  -- `G (e x + y) = ∑ (j!)⁻¹ D^j G (e x) (y, …, y) = 0` for small `y`
  have hzero : ∀ᶠ y in 𝓝 (0 : ComplexModel n), G (e.val x + y) = 0 := by
    filter_upwards [Metric.eball_mem_nhds (0 : ComplexModel n) hp.r_pos] with y hy
    have hs := hp.hasSum_iteratedFDeriv hy
    simp only [hall, zero_apply, smul_zero] at hs
    exact hs.unique hasSum_zero
  have hT : Tendsto (fun p => e.val p - e.val x) (𝓝 x) (𝓝 0) := by
    have := ((e.val.continuousAt hxe).tendsto).sub_const (e.val x)
    simpa using this
  filter_upwards [hT.eventually hzero, e.val.open_source.mem_nhds hxe] with p hp hpe
  have : g p = G (e.val x + (e.val p - e.val x)) := by
    simp [G, e.val.left_inv hpe]
  rw [this, hp]

/-- A germ that does not vanish near `x` lies outside some power of `𝔪_x`. -/
theorem exists_notMem_idealPow_of_frequently {x : M} {g : M → ℂ} (hg : HolomorphicAt n g x)
    (hne : ∃ᶠ y in 𝓝 x, g y ≠ 0) : ∃ q, ¬ (idealPow (pointIdeal n x) q).mem x g := by
  by_contra! h
  exact hne ((eventually_eq_zero_of_forall_mem_idealPow hg h).mono fun _ hy hy' => hy' hy)

end Krull

/-! ### Powers of the ideal of a submanifold -/

section Powers

variable {C : Set M}

/-- Germs of `𝓘_C^μ` at `x` are germs of `𝓘_C^μ` at every point near `x`. -/
theorem eventually_mem_idealPow_vanishingIdeal {x : M} {g : M → ℂ} :
    ∀ {μ : ℕ}, (idealPow (vanishingIdeal (n := n) C) μ).mem x g →
      ∀ᶠ y in 𝓝 x, (idealPow (vanishingIdeal (n := n) C) μ).mem y g
  | 0, h => h.eventually_nhds
  | μ + 1, h => by
    obtain ⟨hghol, K, r, c, hr, hc, hsum⟩ := mem_idealPow_succ_iff.mp h
    choose a b ha hb hab using hr
    have hev : ∀ᶠ y in 𝓝 x, ∀ k, (idealPow (vanishingIdeal (n := n) C) μ).mem y (a k) ∧
        (vanishingIdeal (n := n) C).mem y (b k) ∧ HolomorphicAt n (c k) y := by
      refine eventually_all.mpr fun k => ?_
      filter_upwards [eventually_mem_idealPow_vanishingIdeal (ha k), (hb k).1.eventually_nhds,
        (hb k).2.eventually_nhds, (hc k).eventually_nhds] with y h1 h2 h3 h4
      exact ⟨h1, ⟨h2, h3⟩, h4⟩
    filter_upwards [hev, hghol.eventually_nhds, hsum.eventually_nhds] with y hy hgy hsumy
    exact mem_idealPow_succ_iff.mpr ⟨hgy, K, r, c, fun k => ⟨a k, b k, (hy k).1, (hy k).2.1, hab k⟩,
      fun k => (hy k).2.2, hsumy⟩

/-- Powers are monotone in the ideal. -/
theorem idealPow_le_idealPow {I J : GermIdeal n M} (h : I.Le J) : ∀ k, (idealPow I k).Le (idealPow J k)
  | 0 => fun _ _ hg => hg
  | k + 1 => fun y _ hg => mem_idealPow_succ_iff.mpr ((mem_idealPow_succ_iff.mp hg).mono
      fun _ ⟨a, b, ha, hb, hs⟩ => ⟨a, b, idealPow_le_idealPow h k y a ha, h y b hb, hs⟩)

/-- At a point `z ∈ C`, `𝓘_C^μ ⊆ 𝔪_z^μ`. -/
theorem mem_idealPow_pointIdeal_of_mem_idealPow_vanishingIdeal {z : M} (hz : z ∈ C) {g : M → ℂ} {μ : ℕ}
    (h : (idealPow (vanishingIdeal (n := n) C) μ).mem z g) : (idealPow (pointIdeal n z) μ).mem z g :=
  idealPow_le_idealPow (I := vanishingIdeal (n := n) C) (J := pointIdeal n z)
    (fun _ _ hs => ⟨hs.1, hs.2.mono fun _ hw hwz => hw (hwz ▸ hz)⟩) μ z g h

end Powers

/-! ### The Taylor criterion in flat coordinates, without retraction -/

section FlatUniv

variable {x : M} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}

/-- With `k = n` the retraction is the identity: the flattened function is `f ∘ φ`. -/
theorem flatten_univ (f : M → ℂ) (w : ComplexModel n) : flatten Φ n f w = f (flatInv Φ w) := by
  simp only [flatten, planeRetract_of_mem (k := n) (w := w) fun i hi => absurd hi (not_le.mpr i.2)]

/-- Every point is in `univ`, and every vector is in `ℂⁿ × 0`. -/
theorem flat_univ {y : M} (_ : y ∈ (chartAt (ComplexModel n) x).source)
    (_ : chartAt (ComplexModel n) x y ∈ Φ.source) :
    y ∈ (univ : Set M) ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n n :=
  ⟨fun _ i hi => absurd hi (not_le.mpr i.2), fun _ => mem_univ y⟩

variable (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
  (hΦx : Φ.toFun (chartAt (ComplexModel n) x x) = 0)

include hΦsrc in
/-- At a point `z` of the flat domain, the derivatives of order `< μ` of `f ∘ φ` vanish at `ψ z` when
`f ∈ 𝔪_z^μ`. -/
theorem iterDeriv_flatten_univ_eq_zero {z : M} (hz : z ∈ flatDomain Φ) {f : M → ℂ} {μ : ℕ}
    (hf : (idealPow (pointIdeal n z) μ).mem z f) (L : List (ComplexModel n)) (hL : L.length < μ) :
    iterDeriv L (flatten Φ n f) (flatMap Φ z) = 0 :=
  iterDeriv_flatten_flatMap_eq_zero (N := univ) hΦsrc flat_univ hz (mem_univ z)
    (vanishesToOrderOn_of_mem hf) L hL

variable {C : Set M} {k : ℕ}
  (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
    (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))

include hΦsrc hΦx hflat in
/-- **Taylor criterion for `𝓘_C^μ`**: if the derivatives of order `< μ` of `f ∘ φ` vanish on `ℂᵏ × 0` near `0`, then
`f ∈ 𝓘_C^μ` at the centre. -/
theorem mem_idealPow_vanishingIdeal_of_iterDeriv {f : M → ℂ} (hf : HolomorphicAt n f x) {μ : ℕ}
    (hvan : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ complexCoordinatePlane n k →
      ∀ L : List (ComplexModel n), L.length < μ → iterDeriv L (flatten Φ n f) w = 0) :
    (idealPow (vanishingIdeal (n := n) C) μ).mem x f := by
  have hq : (0 : ComplexModel n) ∈ complexCoordinatePlane n k := fun _ _ => rfl
  have hF : InNormalPow k 0 μ (flatten Φ n f) :=
    inNormalPow_of_iterDeriv_eq_zero μ hq (eventually_differentiableAt_flatten hΦsrc hΦx n hf) hvan
  have hψx : flatMap Φ x = 0 := hΦx
  have hψ : ∀ᶠ p in 𝓝 x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (flatMap Φ) p := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with p hp
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.toFun
        (chartAt (ComplexModel n) x p) :=
      (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hp.2)).mdifferentiableAt
    exact h1.comp p (mdifferentiableAt_chart hp.1)
  have hψI : ∀ i : Fin n, k ≤ i.1 → (vanishingIdeal (n := n) C).mem x (fun p => flatMap Φ p i) :=
    fun i hi => flatCoord_mem_vanishingIdeal Φ hflat hi (mem_flatDomain_self Φ)
  refine mem_idealPow_of_inNormalPow hψx hψ hψI μ hF ?_
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with p hp
  rw [flatten_univ, flatInv_flatMap hp]

end FlatUniv

/-- **The Hadamard bridge, local form for one germ**: if `C` is a submanifold at `x` and `f ∈ 𝔪_z^μ` at the points
`z ∈ C` near `x`, then `f ∈ 𝓘_C^μ` at `x`. -/
theorem mem_idealPow_vanishingIdeal_of_eventually {C : Set M} {x : M} {k : ℕ}
    (hC : RegularAtDim (n := n) C x k) {f : M → ℂ} (hf : HolomorphicAt n f x) {μ : ℕ}
    (hsub : ∀ᶠ z in 𝓝 x, z ∈ C → (idealPow (pointIdeal n z) μ).mem z f) :
    (idealPow (vanishingIdeal (n := n) C) μ).mem x f := by
  obtain ⟨-, -, Φ, hΦsrc, hΦx, hflat⟩ := hC
  refine mem_idealPow_vanishingIdeal_of_iterDeriv hΦsrc hΦx hflat hf ?_
  have hT : Tendsto (flatInv Φ) (𝓝 0) (𝓝 x) := by
    have h := (continuousAt_flatInv (zero_mem_target hΦx) hΦsrc).tendsto
    rwa [flatInv_zero hΦx] at h
  filter_upwards [Φ.isOpen_target.mem_nhds (zero_mem_target hΦx), hT.eventually hsub]
    with w hw hwf hwk L hL
  have h := iterDeriv_flatten_univ_eq_zero hΦsrc (flatInv_mem_flatDomain hw hΦsrc)
    (hwf (flatInv_mem hΦsrc hflat hw hwk)) L hL
  rwa [flatMap_flatInv hw hΦsrc] at h

/-! ### Divisibility near a point and the exponent -/

/-- A function holomorphic on an open set is holomorphic at each of its points. -/
theorem holomorphicAt_of_mdifferentiableOn_open {U : Set M} (hUo : IsOpen U) {g : M → ℂ}
    (hg : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g U) {y : M} (hy : y ∈ U) : HolomorphicAt n g y :=
  eventually_of_mem (hUo.mem_nhds hy) fun w hw => (hg w hw).mdifferentiableAt (hUo.mem_nhds hw)

section Exponent

variable {𝔞 : GermIdeal n M} {H : Set M}

variable (n) in
/-- **`𝔞 ⊆ 𝓘_H^e` near `x`, in cosupport form**: near `x`, the points of `H` lie in `cosupp(𝔞, e)`. -/
def IsDivNear (𝔞 : GermIdeal n M) (H : Set M) (e : ℕ) (x : M) : Prop :=
  ∀ᶠ z in 𝓝 x, z ∈ H → z ∈ cosupport n univ 𝔞 e

theorem isDivNear_zero (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (x : M) : IsDivNear n 𝔞 H 0 x :=
  Eventually.of_forall fun z _ => by rw [cosupport_zero h𝔞]; exact mem_univ z

theorem IsDivNear.mono {e e' : ℕ} {x : M} (h : IsDivNear n 𝔞 H e x) (he : e' ≤ e) : IsDivNear n 𝔞 H e' x :=
  Filter.Eventually.mono h fun _ hz hzH => cosupport_anti he (hz hzH)

/-- Divisibility near `x` holds near every point close to `x`. -/
theorem IsDivNear.eventually {e : ℕ} {x : M} (h : IsDivNear n 𝔞 H e x) : ∀ᶠ y in 𝓝 x, IsDivNear n 𝔞 H e y :=
  Filter.Eventually.eventually_nhds h

/-- Off a closed set `H`, every divisibility holds. -/
theorem isDivNear_of_notMem (hH : IsClosed H) {x : M} (hx : x ∉ H) (e : ℕ) : IsDivNear n 𝔞 H e x := by
  filter_upwards [hH.isOpen_compl.mem_nhds hx] with z hz hzH
  exact absurd hzH hz

/-- If the generators of a coherent ideal lie in `𝓘_H^e` at `x`, then `IsDivNear 𝔞 H e x`. -/
theorem isDivNear_of_generators {U : Set M} (hUo : IsOpen U) {x : M} (hxU : x ∈ U) {K : ℕ} {s : Fin K → M → ℂ}
    (hgen : ∀ y ∈ U, ∀ g, 𝔞.mem y g ↔ IsInSpanAt (n := n) (· ∈ range s) y g) {e : ℕ}
    (hs : ∀ i, (idealPow (vanishingIdeal (n := n) H) e).mem x (s i)) : IsDivNear n 𝔞 H e x := by
  filter_upwards [hUo.mem_nhds hxU, eventually_all.mpr fun i => eventually_mem_idealPow_vanishingIdeal (hs i)]
    with z hzU hz hzH
  refine ⟨mem_univ z, fun f hf => IsInSpanAt.vanishesToOrderOn ((hgen z hzU f).mp hf) ?_⟩
  rintro _ ⟨i, rfl⟩
  exact vanishesToOrderOn_of_mem (mem_idealPow_pointIdeal_of_mem_idealPow_vanishingIdeal hzH (hz i))

/-- **Divisibility near `x` is divisibility of the stalk**: for `𝔞` coherent and `H` a submanifold at `x`,
`IsDivNear 𝔞 H e x ↔ 𝔞_x ⊆ (𝓘_H^e)_x`. -/
theorem isDivNear_iff (h𝔞 : 𝔞.IsCoherent) {x : M} {k : ℕ} (hH : RegularAtDim (n := n) H x k) {e : ℕ} :
    IsDivNear n 𝔞 H e x ↔ ∀ g, 𝔞.mem x g → (idealPow (vanishingIdeal (n := n) H) e).mem x g := by
  constructor
  · intro h g hg
    refine mem_idealPow_vanishingIdeal_of_eventually hH
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) ?_
    filter_upwards [h, eventually_mem_of_isCoherent h𝔞 hg] with z hz hgz hzH
    exact mem_idealPow_of_vanishesToOrderOn_univ ((hz hzH).2 g hgz)
  · intro h
    obtain ⟨U, hUo, hxU, K, s, hs, hgen⟩ := h𝔞 x
    refine isDivNear_of_generators hUo hxU hgen fun i => h _ ((hgen x hxU _).mpr ?_)
    exact isInSpanAt_of_eq_mul ⟨i, rfl⟩
      (holomorphicAt_of_mdifferentiableOn_open hUo (hs i) hxU) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm)

/-- **Identity principle along a submanifold, for one germ**: let `C` be a submanifold at `x` and `f` holomorphic at
`x`. If the points `y ∈ C` near which `f ∈ 𝔪_z^e` at every `z ∈ C` accumulate at `x`, then `f ∈ 𝓘_C^e` at `x`. -/
theorem mem_idealPow_vanishingIdeal_of_frequently {C : Set M} {x : M} {k : ℕ}
    (hC : RegularAtDim (n := n) C x k) {f : M → ℂ} (hf : HolomorphicAt n f x) {e : ℕ}
    (h : ∃ᶠ y in 𝓝 x, y ∈ C ∧ ∀ᶠ z in 𝓝 y, z ∈ C → (idealPow (pointIdeal n z) e).mem z f) :
    (idealPow (vanishingIdeal (n := n) C) e).mem x f := by
  obtain ⟨-, -, Φ, hΦsrc, hΦx, hflat⟩ := hC
  refine mem_idealPow_vanishingIdeal_of_iterDeriv hΦsrc hΦx hflat hf ?_
  set F := flatten Φ n f
  set P := planeRetract (n := n) k
  -- a ball `B` around `0` inside the target on which `F` is holomorphic
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((eventually_differentiableAt_flatten hΦsrc hΦx n hf).and
      (Φ.isOpen_target.mem_nhds (zero_mem_target hΦx)))
  set B := Metric.ball (0 : ComplexModel n) r
  have hFB : DifferentiableOn ℂ F B := fun w hw => (hball w hw).1.differentiableWithinAt
  -- a point `y ∈ C` near `x` where the vanishing holds, with `ψ y ∈ B`
  have hψT : Tendsto (flatMap Φ) (𝓝 x) (𝓝 0) := by
    have h1 : ContinuousAt (flatMap Φ) x :=
      ((Φ.toFun_holomorphic.differentiableAt
        (Φ.isOpen_source.mem_nhds Φ.center_mem_source)).continuousAt).comp
        ((chartAt (ComplexModel n) x).continuousAt (mem_chart_source _ x))
    have h2 : flatMap Φ x = 0 := hΦx
    rw [ContinuousAt, h2] at h1
    exact h1
  have hD' : ∀ᶠ y in 𝓝 x, y ∈ flatDomain Φ := (isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)
  have hB' : ∀ᶠ y in 𝓝 x, flatMap Φ y ∈ Metric.ball (0 : ComplexModel n) r :=
    hψT.eventually (Metric.ball_mem_nhds 0 hr)
  obtain ⟨y, ⟨hyC, hyd⟩, hyD, hyB⟩ := (h.and_eventually (hD'.and hB')).exists
  set z₀ := flatMap Φ y
  have hz₀k : z₀ ∈ complexCoordinatePlane n k := (mem_iff_flatMap_mem hflat hyD).mp hyC
  have hPz₀ : P z₀ = z₀ := planeRetract_of_mem hz₀k
  have hz₀T : z₀ ∈ Φ.target := flatMap_mem_target hyD
  have hPT : Tendsto P (𝓝 z₀) (𝓝 z₀) := by
    have := P.continuous.tendsto z₀
    rwa [hPz₀] at this
  have hφT : Tendsto (fun u => flatInv Φ (P u)) (𝓝 z₀) (𝓝 y) := by
    have h1 := (continuousAt_flatInv hz₀T hΦsrc).tendsto
    rw [flatInv_flatMap hyD] at h1
    exact h1.comp hPT
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr) fun w hwB hwk L hL => ?_
  -- `G = D ∘ P` with `D` the derivative along `L`
  have hD : DifferentiableOn ℂ (iterDeriv L F) B := differentiableOn_iterDeriv hFB Metric.isOpen_ball L
  set Q := P ⁻¹' B
  have hQo : IsOpen Q := Metric.isOpen_ball.preimage P.continuous
  have hG : AnalyticOnNhd ℂ (fun u => iterDeriv L F (P u)) Q :=
    analyticOnNhd_of_differentiableOn hQo (hD.comp P.differentiableOn fun _ hu => hu)
  have hQc : IsPreconnected Q := by
    have hlin : IsLinearMap ℝ P := ⟨P.map_add, fun c u => P.map_smul_of_tower c u⟩
    exact ((convex_ball (0 : ComplexModel n) r).is_linear_preimage hlin).isPreconnected
  have hz₀Q : z₀ ∈ Q := by
    change P z₀ ∈ B
    rw [hPz₀]
    exact hyB
  -- `G` vanishes near `z₀`
  have hG0 : (fun u => iterDeriv L F (P u)) =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hPT.eventually (Φ.isOpen_target.mem_nhds hz₀T), hφT.eventually hyd] with u hu hφd
    have hsm := hφd (flatInv_mem hΦsrc hflat hu (planeRetract_mem k u))
    have h0 := iterDeriv_flatten_univ_eq_zero hΦsrc (flatInv_mem_flatDomain hu hΦsrc) hsm L hL
    rw [flatMap_flatInv hu hΦsrc] at h0
    exact h0
  have hEq := hG.eqOn_zero_of_preconnected_of_eventuallyEq_zero hQc hz₀Q hG0
  have hPw : P w = w := planeRetract_of_mem hwk
  have hwQ : w ∈ Q := by
    change P w ∈ B
    rw [hPw]
    exact hwB
  have := hEq hwQ
  simp only [Pi.zero_apply, hPw] at this
  exact this

/-- **Identity principle along `H`**: for `𝔞` coherent and `H` a submanifold at `x`, if points `y ∈ H` with
`IsDivNear 𝔞 H e y` accumulate at `x`, then `IsDivNear 𝔞 H e x`. -/
theorem isDivNear_of_frequently (h𝔞 : 𝔞.IsCoherent) {x : M} {k : ℕ} (hH : RegularAtDim (n := n) H x k)
    {e : ℕ} (h : ∃ᶠ y in 𝓝 x, y ∈ H ∧ IsDivNear n 𝔞 H e y) : IsDivNear n 𝔞 H e x := by
  obtain ⟨U, hUo, hxU, K, s, hs, hgen⟩ := h𝔞 x
  have hshol : ∀ i, ∀ z ∈ U, HolomorphicAt n (s i) z := fun i _ hz =>
    holomorphicAt_of_mdifferentiableOn_open hUo (hs i) hz
  have hmem : ∀ i, ∀ z ∈ U, 𝔞.mem z (s i) := fun i z hz => (hgen z hz (s i)).mpr
    (isInSpanAt_of_eq_mul ⟨i, rfl⟩ (hshol i z hz) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm))
  refine isDivNear_of_generators hUo hxU hgen fun i => ?_
  refine mem_idealPow_vanishingIdeal_of_frequently hH (hshol i x hxU) ?_
  have hU' : ∀ᶠ y in 𝓝 x, y ∈ U := hUo.mem_nhds hxU
  refine (h.and_eventually (Filter.Eventually.eventually_nhds hU')).mono ?_
  rintro y ⟨⟨hyH, hyd⟩, hyU⟩
  refine ⟨hyH, ?_⟩
  filter_upwards [hyd, hyU] with z hz hzU hzH
  exact mem_idealPow_of_vanishesToOrderOn_univ ((hz hzH).2 (s i) (hmem i z hzU))

variable (n) in
/-- **The exponent of `𝔞` along `H` at `x`**: the largest `e` with `IsDivNear 𝔞 H e x` (`0` if there is none, or if
every `e` works). -/
noncomputable def divExp (𝔞 : GermIdeal n M) (H : Set M) (x : M) : ℕ := by
  classical
  exact if h : ∃ e, ¬ IsDivNear n 𝔞 H (e + 1) x then Nat.find h else 0

/-- `𝔞_x` contains a germ that does not vanish near `x`. -/
def IsNonzeroAt (𝔞 : GermIdeal n M) (x : M) : Prop :=
  ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0

/-- **The exponent is finite**: at a point `x ∈ H` where `𝔞_x` contains a germ not vanishing near `x`, some
`IsDivNear 𝔞 H e x` fails. -/
theorem exists_not_isDivNear (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {x : M} (hx : x ∈ H)
    (hne : IsNonzeroAt 𝔞 x) : ∃ e, ¬ IsDivNear n 𝔞 H (e + 1) x := by
  obtain ⟨g, hg, hgne⟩ := hne
  obtain ⟨q, hq⟩ := exists_notMem_idealPow_of_frequently (h𝔞 x g hg) hgne
  refine ⟨q, fun hd => hq ?_⟩
  have h1 := (hd.self_of_nhds hx).2 g hg
  exact (idealPow_le_of_le (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg) (Nat.le_succ q)) x g
    (mem_idealPow_of_vanishesToOrderOn_univ h1)

theorem isDivNear_divExp (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (x : M) :
    IsDivNear n 𝔞 H (divExp n 𝔞 H x) x := by
  classical
  unfold divExp
  split_ifs with h
  · rcases hm : Nat.find h with _ | m
    · exact isDivNear_zero h𝔞 x
    · have := Nat.find_min h (show m < Nat.find h by omega)
      push Not at this
      exact this
  · exact isDivNear_zero h𝔞 x

theorem not_isDivNear_divExp_succ (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {x : M} (hx : x ∈ H)
    (hne : IsNonzeroAt 𝔞 x) : ¬ IsDivNear n 𝔞 H (divExp n 𝔞 H x + 1) x := by
  classical
  have h := exists_not_isDivNear h𝔞 hx hne
  unfold divExp
  rw [dif_pos h]
  exact Nat.find_spec h

/-- **The exponent characterizes divisibility**: `IsDivNear 𝔞 H e x ↔ e ≤ divExp 𝔞 H x`. -/
theorem isDivNear_iff_le_divExp (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {x : M} (hx : x ∈ H)
    (hne : IsNonzeroAt 𝔞 x) {e : ℕ} : IsDivNear n 𝔞 H e x ↔ e ≤ divExp n 𝔞 H x := by
  refine ⟨fun hd => ?_, fun he => (isDivNear_divExp h𝔞 x).mono he⟩
  by_contra hlt
  exact not_isDivNear_divExp_succ h𝔞 hx hne (hd.mono (by omega))

/-- **The exponent is locally constant on `H`** (`hir:divisor-exponent`): for `𝔞` coherent, nonzero at every point
near `x`, and `H` a submanifold at `x`, `divExp 𝔞 H y = divExp 𝔞 H x` for `y ∈ H` near `x`. -/
theorem eventually_divExp_eq (h𝔞 : 𝔞.IsCoherent) {x : M} {k : ℕ} (hH : RegularAtDim (n := n) H x k)
    (hne : ∀ᶠ y in 𝓝 x, IsNonzeroAt 𝔞 y) :
    ∀ᶠ y in 𝓝 x, y ∈ H → divExp n 𝔞 H y = divExp n 𝔞 H x := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  set e := divExp n 𝔞 H x
  have hxH : x ∈ H := hH.2.1
  have h1 : ∀ᶠ y in 𝓝 x, IsDivNear n 𝔞 H e y := (isDivNear_divExp hhol x).eventually
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ H → ¬ IsDivNear n 𝔞 H (e + 1) y := by
    by_contra hc
    rw [Filter.not_eventually] at hc
    exact not_isDivNear_divExp_succ hhol hxH hne.self_of_nhds
      (isDivNear_of_frequently h𝔞 hH (hc.mono fun y hy => by push Not at hy; exact hy))
  filter_upwards [h1, h2, hne] with y hy1 hy2 hyne hyH
  have hle : e ≤ divExp n 𝔞 H y := (isDivNear_iff_le_divExp hhol hyH hyne).mp hy1
  have hlt : ¬ e + 1 ≤ divExp n 𝔞 H y := fun h => hy2 hyH ((isDivNear_iff_le_divExp hhol hyH hyne).mpr h)
  omega

end Exponent


end

end Hironaka.DivisorExponent
