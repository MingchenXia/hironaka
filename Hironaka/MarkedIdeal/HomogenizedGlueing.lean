import Hironaka.MarkedIdeal.HomogenizedIdeal
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The glueing lemma for homogenized ideals (analytic form)

Hironaka phase H3 (TN23-ENVELOPES, agreed with TN-CLASSICAL on I-0981); blueprint
`mc:homogenized-coherent`, `mc:coordinate-pair`, `mc:glueing-lemma`
(`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005, §2.10, Lemmas `le:homo0` and
`le:homo` (Glueing Lemma) (1)–(3), for `E = ∅` (the only case the source uses), in the analytic
adaptation of design note D7: the étale neighbourhoods `φ_u, φ_v : X̄ → X` become an open
neighbourhood of `x` with `φ_v = id` and `φ_u = φ` a convergent coordinate change.

* `isCoherent_homogenizedIdeal`: `𝓗(𝔞)` is coherent (finite sums of coherent ideals,
  `finSumIdeal_succ`, `isCoherent_finSumIdeal`).
* `eventually_mem`: a germ of a coherent ideal at `x` is a germ of it at every point near `x`;
  `eventually_pullback_le`: if `φ` is holomorphic near `x`, `φ x = x` and `φ^* 𝔟 ⊆ 𝔟` at `x`
  (coherent `𝔟`), then `φ^* 𝔟 ⊆ 𝔟` at every point near `x`.
* `CoordinatePair x u v` and `exists_coordinatePair`: for `u, v` holomorphic at `x` with
  `u x = v x` and nonvanishing differentials at `x` there are coordinates
  `W = (u, u₂, …, uₙ)` and `W' = (v, u₂, …, uₙ)` at `x` (the same `u₂, …, uₙ`, linear in the
  chart: `uⱼ = P ∘ e` with `P` a linear projection killing a vector on which both differentials
  are nonzero) and the two coordinate changes `φ` (`W ↦ W + (v - u) eᵢ`) and `ψ` (`W' ↦ W' + (u - v) eᵢ`),
  mutually inverse near `x`, with `u ∘ φ = v` and `v ∘ ψ = u` near `x`.
* `CoordinatePair.comp_mem_homogenizedIdeal_iff`: for tangent-ideal germs `u, v ∈ T(𝔞)_x`,
  `f ∘ φ ∈ 𝓗(𝔞)_x ↔ f ∈ 𝓗(𝔞)_x` (Włodarczyk `le:homo0` (1), equality, via the inverse change);
  `eventually_pullback_homogenizedIdeal`: `φ^* 𝓗(𝔞) = 𝓗(𝔞)` at every point near `x`;
  `eventually_coordMap_eq_self_of_mem_cosupport`: `φ` and `ψ` fix `cosupp(𝔞, μ)` pointwise near `x`.
* `glueing_lemma` (**the Glueing Lemma, analytic form, (1)–(3)**): for tangent directions `u`, `v`
  of `(𝔞, μ)` at `x ∈ cosupp(𝔞, μ)` there are `φ, ψ`, holomorphic and mutually inverse near `x`,
  with `u ∘ φ = v`, `φ^* 𝓗(𝔞) = 𝓗(𝔞)` near `x`, and `φ = id` on `cosupp(𝔞, μ)` near `x`.

Not here: part (4) of `le:homo` (the multiple test blow-ups of `(𝓗(𝔞), μ)` are `φ`-equivariant);
it needs the transport of test towers along local biholomorphisms.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold

namespace Hironaka.HomogenizedGlueing

open Hironaka.HolomorphicIdealSheaves GermIdealOrder DerivativeIdeal IdealWeightPowers
  HomogenizedIdeal

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Coherent ideals -/

section Coherent

variable {𝔞 : GermIdeal n M}

theorem holomorphicAt_of_mem (h𝔞 : 𝔞.IsCoherent) {x : M} {g : M → ℂ} (hg : 𝔞.mem x g) :
    HolomorphicAt n g x :=
  RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg

/-- A germ of a coherent ideal at `x` is a germ of it at every point near `x`. -/
theorem eventually_mem (h𝔞 : 𝔞.IsCoherent) {x : M} {g : M → ℂ} (hg : 𝔞.mem x g) :
    ∀ᶠ y in 𝓝 x, 𝔞.mem y g := by
  obtain ⟨U, hUo, hxU, N, s, -, hgen⟩ := h𝔞 x
  obtain ⟨hgh, K, t, c, ht, hc, hsum⟩ := (hgen x hxU g).mp hg
  filter_upwards [hUo.mem_nhds hxU, hgh.eventually, eventually_all.2 fun k => (hc k).eventually,
    hsum.eventuallyEq_nhds] with y hyU hgy hcy hsumy
  exact (hgen y hyU g).mpr ⟨hgy, K, t, c, ht, hcy, hsumy⟩

/-- A coherent ideal is closed under complex linear combinations of two of its germs. -/
theorem lin_mem (h𝔞 : 𝔞.IsCoherent) {x : M} {f g : M → ℂ} (hf : 𝔞.mem x f) (hg : 𝔞.mem x g)
    (a b : ℂ) : 𝔞.mem x (fun p => a * f p + b * g p) :=
  HomogenizedIdeal.mem_of_isInSpanAt h𝔞 (RelativePrincipalizationSpan.IsInSpanAt.add
    (RelativePrincipalizationSpan.IsInSpanAt.mul_left (holomorphicAt_const a)
      (InvertibleIdealQuotient.isInSpanAt_self hf (holomorphicAt_of_mem h𝔞 hf)))
    (RelativePrincipalizationSpan.IsInSpanAt.mul_left (holomorphicAt_const b)
      (InvertibleIdealQuotient.isInSpanAt_self hg (holomorphicAt_of_mem h𝔞 hg))))

/-- A coherent ideal is closed under subtraction. -/
theorem sub_mem (h𝔞 : 𝔞.IsCoherent) {x : M} {f g : M → ℂ} (hf : 𝔞.mem x f) (hg : 𝔞.mem x g) :
    𝔞.mem x (fun p => f p - g p) :=
  HomogenizedIdeal.mem_congr h𝔞 (lin_mem h𝔞 hf hg 1 (-1))
    (Eventually.of_forall fun p => by ring)

/-- The ideal generated stalkwise by the germs of `J 0, …, J (μ - 1)`. -/
def finSumIdeal (J : ℕ → GermIdeal n M) (μ : ℕ) : GermIdeal n M where
  mem x := IsInSpanAt (n := n) (fun s => ∃ i, i < μ ∧ (J i).mem x s) x

/-- `finSumIdeal J (μ + 1) = finSumIdeal J μ + J μ` for coherent `J i`. -/
theorem finSumIdeal_succ {J : ℕ → GermIdeal n M} {μ : ℕ} (hJ : ∀ i ≤ μ, (J i).IsCoherent) :
    finSumIdeal J (μ + 1) = RestrictedIdealExtension.sumIdeal (finSumIdeal J μ) (J μ) := by
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · show IsInSpanAt (n := n) (fun s => (finSumIdeal J μ).mem y s ∨ (J μ).mem y s) y g
    refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_
      (show IsInSpanAt (n := n) (fun s => ∃ i, i < μ + 1 ∧ (J i).mem y s) y g from hg)
    rintro s ⟨i, hi, hs⟩
    have hsh := holomorphicAt_of_mem (hJ i (Nat.lt_succ_iff.mp hi)) hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have hs' : IsInSpanAt (n := n) (fun s => ∃ i, i < μ ∧ (J i).mem y s) y s :=
        InvertibleIdealQuotient.isInSpanAt_self ⟨i, hi, hs⟩ hsh
      exact InvertibleIdealQuotient.isInSpanAt_self (Or.inl hs') hsh
    · exact InvertibleIdealQuotient.isInSpanAt_self (Or.inr hs) hsh
  · show IsInSpanAt (n := n) (fun s => ∃ i, i < μ + 1 ∧ (J i).mem y s) y g
    refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_
      (show IsInSpanAt (n := n) (fun s => (finSumIdeal J μ).mem y s ∨ (J μ).mem y s) y g
        from hg)
    rintro s (hs | hs)
    · exact IsInSpanAt.mono (fun t ⟨i, hi, ht⟩ => ⟨i, Nat.lt_succ_of_lt hi, ht⟩)
        (show IsInSpanAt (n := n) (fun s => ∃ i, i < μ ∧ (J i).mem y s) y s from hs)
    · exact InvertibleIdealQuotient.isInSpanAt_self ⟨μ, Nat.lt_succ_self μ, hs⟩
        (holomorphicAt_of_mem (hJ μ le_rfl) hs)

/-- **Finite sums of coherent ideals are coherent.** -/
theorem isCoherent_finSumIdeal {J : ℕ → GermIdeal n M} (hJ : ∀ i, (J i).IsCoherent) :
    ∀ μ, (finSumIdeal J μ).IsCoherent
  | 0 => by
    intro x
    refine ⟨univ, isOpen_univ, mem_univ x, 0, Fin.elim0, fun i => Fin.elim0 i, fun y _ g => ?_⟩
    change IsInSpanAt (n := n) (fun s => ∃ i, i < 0 ∧ (J i).mem y s) y g ↔ _
    constructor
    · intro hg
      exact IsInSpanAt.mono (fun s ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)) hg
    · intro hg
      exact IsInSpanAt.mono (fun s ⟨i, _⟩ => Fin.elim0 i) hg
  | μ + 1 => by
    rw [finSumIdeal_succ fun i _ => hJ i]
    exact RestrictedIdealExtension.isCoherent_sumIdeal (isCoherent_finSumIdeal hJ μ) (hJ μ)

/-- **The homogenized ideal of a coherent ideal is coherent.** -/
theorem isCoherent_homogenizedIdeal (h𝔞 : 𝔞.IsCoherent) (μ : ℕ) :
    (homogenizedIdeal 𝔞 μ).IsCoherent := by
  have h : homogenizedIdeal 𝔞 μ = finSumIdeal
      (fun i => (iterDerivIdeal 𝔞 i).mul (idealPow (tangentIdeal 𝔞 μ) i)) μ := rfl
  rw [h]
  exact isCoherent_finSumIdeal (fun i => isCoherent_mul (isCoherent_iterDerivIdeal h𝔞 i)
    (GermIdealPullbackCalculus.isCoherent_idealPow (isCoherent_iterDerivIdeal h𝔞 (μ - 1)) i)) μ

end Coherent

/-! ### Pullback inclusions near a fixed point -/

section Pullback

/-- Pulling a span back along a map holomorphic near `y`. -/
theorem isInSpanAt_comp {S : (M → ℂ) → Prop} {φ : M → M} {y : M}
    (hφ : ∀ᶠ p in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    {a : M → ℂ} (ha : IsInSpanAt (n := n) S (φ y) a) :
    IsInSpanAt (n := n) (fun t => ∃ s, S s ∧ t = s ∘ φ) y (a ∘ φ) := by
  obtain ⟨hah, K, t, c, ht, hc, hsum⟩ := ha
  refine ⟨HadamardBridge.holomorphicAt_comp_map hφ hah, K, fun k => t k ∘ φ, fun k => c k ∘ φ,
    fun k => ⟨t k, ht k, rfl⟩, fun k => HadamardBridge.holomorphicAt_comp_map hφ (hc k), ?_⟩
  filter_upwards [hφ.self_of_nhds.continuousAt.eventually hsum] with p hp
  simpa using hp

/-- **Pullback inclusion near a fixed point.**  Let `𝔟` be coherent, `φ` holomorphic near `x`
with `φ x = x`, and assume `g ∘ φ ∈ 𝔟_x` for every `g ∈ 𝔟_x`.  Then `φ^* 𝔟 ⊆ 𝔟` at every point
near `x`. -/
theorem eventually_pullback_le {𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) {x : M} {φ : M → M}
    (hφx : φ x = x)
    (hφ : ∀ᶠ p in 𝓝 x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (hcomp : ∀ g, 𝔟.mem x g → 𝔟.mem x (g ∘ φ)) :
    ∀ᶠ y in 𝓝 x, ∀ g, (GermIdeal.pullback (m := n) φ 𝔟).mem y g → 𝔟.mem y g := by
  obtain ⟨U, hUo, hxU, N, s, hs, hgen⟩ := h𝔟 x
  have hsx : ∀ k, 𝔟.mem x (s k) := fun k =>
    IdealWeightComparison.mem_of_isPresentation hUo hxU hs hgen k
  have hsy : ∀ᶠ y in 𝓝 x, ∀ k, 𝔟.mem y (s k ∘ φ) :=
    eventually_all.2 fun k => eventually_mem h𝔟 (hcomp _ (hsx k))
  have hφU : ∀ᶠ y in 𝓝 x, φ y ∈ U := by
    have hc : ContinuousAt φ x := hφ.self_of_nhds.continuousAt
    rw [ContinuousAt, hφx] at hc
    exact hc.eventually (hUo.mem_nhds hxU)
  filter_upwards [hsy, hφU, hφ.eventually_nhds] with y hy hyU hφy g hg
  refine HomogenizedIdeal.mem_of_isInSpanAt h𝔟 (RelativePrincipalizationSpan.IsInSpanAt.trans ?_
    (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg))
  rintro t ⟨a, ha, rfl⟩
  refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_
    (isInSpanAt_comp hφy ((hgen (φ y) hyU a).mp ha))
  rintro t ⟨r, ⟨k, rfl⟩, rfl⟩
  exact InvertibleIdealQuotient.isInSpanAt_self (hy k) (holomorphicAt_of_mem h𝔟 (hy k))

end Pullback

/-! ### Coordinate changes: holomorphy and fixed points -/

section CoordinateChangeFacts

variable {x : M} (d : CoordinateChange (n := n) x)

/-- The coordinate change is holomorphic near `x`. -/
theorem eventually_mdifferentiableAt_coordMap :
    ∀ᶠ p in 𝓝 x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) d.coordMap p := by
  obtain ⟨H, hH, hHx, hφ⟩ := d.exists_chart_form
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hHc : Tendsto H (𝓝 (e.val x)) (𝓝 (e.val x)) := by
    have := hH.self_of_nhds.continuousAt
    rwa [ContinuousAt, hHx] at this
  have hT : Tendsto e.val (𝓝 x) (𝓝 (e.val x)) := e.val.continuousAt hxs
  filter_upwards [hφ.eventually_nhds, e.val.open_source.mem_nhds hxs, hT.eventually hH,
    hT.eventually (hHc.eventually (e.val.open_target.mem_nhds (e.val.map_source hxs)))]
    with p hp1 hp2 hp3 hp4
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.val p :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property hp2
  have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) H (e.val p) :=
    mdifferentiableAt_iff_differentiableAt.mpr hp3
  have h3 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.val.symm (H (e.val p)) :=
    mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.property hp4
  exact (h3.comp p (h2.comp p h1)).congr_of_eventuallyEq hp1

/-- The coordinate change fixes, near `x`, every point where `h` vanishes. -/
theorem eventually_coordMap_eq_self : ∀ᶠ p in 𝓝 x, d.h p = 0 → d.coordMap p = p := by
  have hxs : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
  filter_upwards [d.left_inv, (complexChartAt (n := n) x).val.open_source.mem_nhds hxs]
    with p hp hps h0
  simp only [HomogenizedIdeal.CoordinateChange.coordMap, h0, zero_smul, add_zero, hp]
  exact (complexChartAt (n := n) x).val.left_inv hps

end CoordinateChangeFacts

/-! ### Two coordinate systems from two tangent directions -/

section Pair

/-- Two nonzero linear forms are both nonzero on some vector. -/
theorem exists_apply_ne_zero_and {ℓ ℓ' : ComplexModel n →L[ℂ] ℂ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) :
    ∃ w : ComplexModel n, ℓ w ≠ 0 ∧ ℓ' w ≠ 0 := by
  obtain ⟨w₁, hw₁⟩ : ∃ w, ℓ w ≠ 0 := by
    by_contra! h
    exact hℓ (ContinuousLinearMap.ext fun w => by simpa using h w)
  obtain ⟨w₂, hw₂⟩ : ∃ w, ℓ' w ≠ 0 := by
    by_contra! h
    exact hℓ' (ContinuousLinearMap.ext fun w => by simpa using h w)
  by_cases h1 : ℓ' w₁ = 0
  · by_cases h2 : ℓ w₂ = 0
    · exact ⟨w₁ + w₂, by simpa [map_add, h2] using hw₁, by simpa [map_add, h1] using hw₂⟩
    · exact ⟨w₂, h2, hw₂⟩
  · exact ⟨w₁, hw₁, h1⟩

/-- `P(ζ) = ζ - (w_k⁻¹ ζ_k) w`: for `w_k ≠ 0` it kills `w` and the `k`-th coordinate. -/
def killMap (w : ComplexModel n) (k : Fin n) : ComplexModel n →L[ℂ] ComplexModel n :=
  ContinuousLinearMap.id ℂ (ComplexModel n) -
    ((w k)⁻¹ • (EuclideanSpace.proj k : ComplexModel n →L[ℂ] ℂ)).smulRight w

theorem killMap_apply (w : ComplexModel n) (k : Fin n) (ζ : ComplexModel n) :
    killMap w k ζ = ζ - ((w k)⁻¹ * ζ k) • w := by
  simp [killMap, smul_eq_mul]

theorem killMap_apply_self {w : ComplexModel n} {k : Fin n} (hw : w k ≠ 0) (ζ : ComplexModel n) :
    killMap w k ζ k = 0 := by
  rw [killMap_apply]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem eq_smul_of_killMap_eq_zero {w : ComplexModel n} {k : Fin n} {ζ : ComplexModel n}
    (h : killMap w k ζ = 0) : ζ = ((w k)⁻¹ * ζ k) • w := by
  rwa [killMap_apply, sub_eq_zero] at h

/-- The coordinates `W(p) = P(e p) + u(p) e_k` at `x` (`e` the chart at `x`): the `k`-th coordinate is
`u`, the others are linear in the chart. -/
def pairCoord (x : M) (w : ComplexModel n) (k : Fin n) (u : M → ℂ) : M → ComplexModel n :=
  fun p => killMap w k ((complexChartAt (n := n) x).val p) + u p • EuclideanSpace.single k 1

theorem pairCoord_apply_self {x : M} {w : ComplexModel n} {k : Fin n} (hw : w k ≠ 0)
    (u : M → ℂ) (p : M) : pairCoord x w k u p k = u p := by
  simp [pairCoord, killMap_apply_self hw]

theorem pairCoord_sub (x : M) (w : ComplexModel n) (k : Fin n) (u v : M → ℂ) (p : M) :
    pairCoord x w k v p = pairCoord x w k u p + (v p - u p) • EuclideanSpace.single k 1 := by
  simp only [pairCoord, sub_smul]
  abel

/-- A nonvanishing partial derivative in some chart at `x` gives a nonzero differential in the
preferred chart at `x`. -/
theorem fderiv_ne_zero_of_chartDeriv {x : M} {f : M → ℂ} (hf : HolomorphicAt n f x)
    (h : ∃ (e : ComplexChart n M) (w : ComplexModel n), x ∈ e.val.source ∧ chartDeriv e w f x ≠ 0) :
    fderiv ℂ (f ∘ (complexChartAt (n := n) x).val.symm) ((complexChartAt (n := n) x).val x) ≠ 0 := by
  obtain ⟨e', w, hx', hne⟩ := h
  intro h0
  apply hne
  rw [(chartDeriv_eventuallyEq_sum (v := w) (complexChartAt (n := n) x) e'
    (mem_complexChartAt_source x) hx' hf).self_of_nhds]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp [chartDeriv, h0]

/-- The coordinates `pairCoord` are local holomorphic coordinates at `x` when `w_k ≠ 0` and the
differential of `u` is nonzero on `w`. -/
theorem pairCoord_coordinates {x : M} {u : M → ℂ} (hu : HolomorphicAt n u x) {w : ComplexModel n}
    {k : Fin n} (hwk : w k ≠ 0)
    (hℓ : fderiv ℂ (u ∘ (complexChartAt (n := n) x).val.symm) ((complexChartAt (n := n) x).val x) w ≠ 0) :
    ∃ N : Set (ComplexModel n), IsOpen N ∧ (complexChartAt (n := n) x).val x ∈ N ∧
      DifferentiableOn ℂ (pairCoord x w k u ∘ (complexChartAt (n := n) x).val.symm) N ∧
      Function.Injective (fderiv ℂ (pairCoord x w k u ∘ (complexChartAt (n := n) x).val.symm)
        ((complexChartAt (n := n) x).val x)) := by
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hud := eventually_differentiableAt_comp_symm e hxs hu
  set G : ComplexModel n → ComplexModel n :=
    fun ζ => killMap w k ζ + (u ∘ e.val.symm) ζ • EuclideanSpace.single k 1 with hG
  have hWG : ∀ ζ ∈ e.val.target, (pairCoord x w k u ∘ e.val.symm) ζ = G ζ := by
    intro ζ hζ
    simp only [Function.comp_apply, pairCoord, hG]
    rw [← he, e.val.right_inv hζ]
  have hWGev : ∀ ζ ∈ e.val.target, (pairCoord x w k u ∘ e.val.symm) =ᶠ[𝓝 ζ] G := fun ζ hζ =>
    eventually_of_mem (e.val.open_target.mem_nhds hζ) hWG
  have hGd : ∀ ζ, DifferentiableAt ℂ (u ∘ e.val.symm) ζ → DifferentiableAt ℂ G ζ := fun ζ hζ =>
    (killMap w k).differentiableAt.add (hζ.smul_const _)
  obtain ⟨N, hNsub, hNo, hxN⟩ := eventually_nhds_iff.mp
    (hud.and (e.val.open_target.mem_nhds (e.val.map_source hxs)))
  refine ⟨N, hNo, hxN, fun ζ hζ => ?_, ?_⟩
  · exact ((hGd ζ (hNsub ζ hζ).1).congr_of_eventuallyEq
      (hWGev ζ (hNsub ζ hζ).2)).differentiableWithinAt
  · have hx0 := hNsub _ hxN
    rw [(hWGev _ hx0.2).fderiv_eq]
    have hfd : fderiv ℂ G (e.val x) = killMap w k +
        (fderiv ℂ (u ∘ e.val.symm) (e.val x)).smulRight (EuclideanSpace.single k 1) :=
      ((killMap w k).hasFDerivAt.add (hx0.1.hasFDerivAt.smul_const _)).fderiv
    rw [hfd]
    set ℓ := fderiv ℂ (u ∘ e.val.symm) (e.val x) with hℓdef
    set L : ComplexModel n →L[ℂ] ComplexModel n :=
      killMap w k + ℓ.smulRight (EuclideanSpace.single k 1) with hLdef
    have hLapply : ∀ ξ, L ξ = killMap w k ξ + ℓ ξ • EuclideanSpace.single k (1 : ℂ) := fun ξ => by
      simp [hLdef]
    intro ξ₁ ξ₂ h12
    have hL : L (ξ₁ - ξ₂) = 0 := by rw [map_sub, h12, sub_self]
    set ξ := ξ₁ - ξ₂ with hξ
    rw [hLapply] at hL
    have hk := congrArg (fun z : ComplexModel n => z k) hL
    simp [killMap_apply_self hwk] at hk
    rw [hk, zero_smul, add_zero] at hL
    have hξw := eq_smul_of_killMap_eq_zero hL
    have hc : (w k)⁻¹ * ξ k = 0 := by
      have h0 : ℓ ξ = ((w k)⁻¹ * ξ k) * ℓ w := by
        conv_lhs => rw [hξw]
        rw [map_smul, smul_eq_mul]
      rw [hk] at h0
      exact (mul_eq_zero.mp h0.symm).resolve_right hℓ
    rw [hc, zero_smul, hξ] at hξw
    exact sub_eq_zero.mp hξw

/-- A holomorphic local inverse of local coordinates `W` at `x`, two-sided near `x`. -/
theorem exists_localInverse {x : M} {W : M → ComplexModel n} {N : Set (ComplexModel n)}
    (hN : IsOpen N) (hxN : (complexChartAt (n := n) x).val x ∈ N)
    (hFd : DifferentiableOn ℂ (W ∘ (complexChartAt (n := n) x).val.symm) N)
    (hinj : Function.Injective
      (fderiv ℂ (W ∘ (complexChartAt (n := n) x).val.symm) ((complexChartAt (n := n) x).val x))) :
    ∃ Ψ : ComplexModel n → ComplexModel n, (∀ᶠ z in 𝓝 (W x), DifferentiableAt ℂ Ψ z) ∧
      (∀ᶠ p in 𝓝 x, Ψ (W p) = (complexChartAt (n := n) x).val p) ∧
      (∀ᶠ z in 𝓝 (W x), W ((complexChartAt (n := n) x).val.symm (Ψ z)) = z) := by
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨Θ, -, hΘF, -⟩ := exists_localHolomorphicEquivAt hN hxN hFd hinj
  have hWΘ : ∀ p, p ∈ e.val.source → W p = Θ.toFun (e.val p) := fun p hp => by
    rw [hΘF]; simp only [Function.comp_apply, e.val.left_inv hp]
  have htgt : Θ.target ∈ 𝓝 (W x) := by
    rw [hWΘ x hxs]
    exact Θ.isOpen_target.mem_nhds (Θ.mapsTo_toFun Θ.center_mem_source)
  refine ⟨Θ.invFun, ?_, ?_, ?_⟩
  · filter_upwards [htgt] with z hz
    exact (Θ.invFun_holomorphic z hz).differentiableAt (Θ.isOpen_target.mem_nhds hz)
  · filter_upwards [e.val.open_source.mem_nhds hxs, (e.val.continuousAt hxs).preimage_mem_nhds
      (Θ.isOpen_source.mem_nhds Θ.center_mem_source)] with p hp hpΘ
    rw [hWΘ p hp, Θ.left_inv _ hpΘ]
  · filter_upwards [htgt] with z hz
    have := Θ.right_inv z hz
    rw [hΘF] at this
    exact this

/-- **Two coordinate systems `(u, u₂, …, uₙ)` and `(v, u₂, …, uₙ)` at `x`** and the two coordinate
changes between them (Włodarczyk, proof of `le:homo0`, step (0), analytic form): `d` replaces the
coordinate `u` by `v` (`φ = d.coordMap`, `u ∘ φ = v`), `d'` replaces `v` by `u` (`ψ = d'.coordMap`),
and `φ`, `ψ` are inverse to each other near `x`. -/
structure CoordinatePair (x : M) (u v : M → ℂ) where
  d : CoordinateChange (n := n) x
  d' : CoordinateChange (n := n) x
  h_eq : ∀ p, d.h p = v p - u p
  h'_eq : ∀ p, d'.h p = u p - v p
  i_eq : d'.i = d.i
  W_apply : ∀ p, d.W p d.i = u p
  W'_eq : ∀ p, d'.W p = d.W p + d.h p • EuclideanSpace.single d.i 1
  comp_d : ∀ᶠ p in 𝓝 x, u (d.coordMap p) = v p
  comp_d' : ∀ᶠ p in 𝓝 x, v (d'.coordMap p) = u p
  left_inv : ∀ᶠ p in 𝓝 x, d'.coordMap (d.coordMap p) = p
  right_inv : ∀ᶠ p in 𝓝 x, d.coordMap (d'.coordMap p) = p

theorem holomorphicAt_sub {x : M} {f g : M → ℂ} (hf : HolomorphicAt n f x)
    (hg : HolomorphicAt n g x) : HolomorphicAt n (fun p => f p - g p) x :=
  (hf.and hg).mono fun _ h => h.1.sub h.2

/-- **Existence of the coordinate pair**: `u`, `v` holomorphic at `x` with `u x = v x` and
nonvanishing differentials at `x` (a nonzero partial derivative in some chart). -/
theorem exists_coordinatePair {x : M} {u v : M → ℂ} (hu : HolomorphicAt n u x)
    (hv : HolomorphicAt n v x) (huv : u x = v x)
    (hdu : ∃ (e : ComplexChart n M) (w : ComplexModel n), x ∈ e.val.source ∧ chartDeriv e w u x ≠ 0)
    (hdv : ∃ (e : ComplexChart n M) (w : ComplexModel n), x ∈ e.val.source ∧ chartDeriv e w v x ≠ 0) :
    Nonempty (CoordinatePair (n := n) x u v) := by
  classical
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨w, hw, hw'⟩ := exists_apply_ne_zero_and (fderiv_ne_zero_of_chartDeriv hu hdu)
    (fderiv_ne_zero_of_chartDeriv hv hdv)
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra! h
    have hw0 : w = 0 := by ext j; simpa using h j
    exact hw (by rw [hw0, map_zero])
  obtain ⟨N, hNo, hxN, hNd, hNi⟩ := pairCoord_coordinates hu hk hw
  obtain ⟨N', hNo', hxN', hNd', hNi'⟩ := pairCoord_coordinates hv hk hw'
  set W := pairCoord x w k u with hW
  set W' := pairCoord x w k v with hW'
  obtain ⟨Ψ, hΨd, hΨl, hΨr⟩ := exists_localInverse hNo hxN hNd hNi
  obtain ⟨Ψ', hΨd', hΨl', hΨr'⟩ := exists_localInverse hNo' hxN' hNd' hNi'
  let d : CoordinateChange (n := n) x :=
    { W := W, N := N, isOpen := hNo, mem := hxN, differentiableOn := hNd, injective := hNi,
      Ψ := Ψ, differentiableAt := hΨd, left_inv := hΨl, h := fun p => v p - u p,
      holomorphicAt := holomorphicAt_sub hv hu, h_zero := by simp [huv], i := k }
  let d' : CoordinateChange (n := n) x :=
    { W := W', N := N', isOpen := hNo', mem := hxN', differentiableOn := hNd', injective := hNi',
      Ψ := Ψ', differentiableAt := hΨd', left_inv := hΨl', h := fun p => u p - v p,
      holomorphicAt := holomorphicAt_sub hu hv, h_zero := by simp [huv], i := k }
  -- the two coordinate systems differ only in the `k`-th coordinate
  have hWW' : ∀ p, W' p = W p + (v p - u p) • EuclideanSpace.single k 1 :=
    pairCoord_sub x w k u v
  have hW'W : ∀ p, W p = W' p + (u p - v p) • EuclideanSpace.single k 1 :=
    pairCoord_sub x w k v u
  have hWx : W' x = W x := by rw [hWW', huv, sub_self, zero_smul, add_zero]
  have hφ : ∀ p, d.coordMap p = e.val.symm (Ψ (W' p)) := fun p => by
    simp only [CoordinateChange.coordMap, d, hWW']
    rfl
  have hψ : ∀ p, d'.coordMap p = e.val.symm (Ψ' (W p)) := fun p => by
    simp only [CoordinateChange.coordMap, d', hW'W]
    rfl
  -- `W ∘ φ = W'` and `W' ∘ ψ = W` near `x`
  have hWc : ContinuousAt W x := d.continuousAt_W
  have hWc' : ContinuousAt W' x := d'.continuousAt_W
  have hWφ : ∀ᶠ p in 𝓝 x, W (d.coordMap p) = W' p := by
    have hr : ∀ᶠ z in 𝓝 (W' x), W (e.val.symm (Ψ z)) = z := by rw [hWx]; exact hΨr
    filter_upwards [hWc'.eventually hr] with p hp
    rw [hφ]; exact hp
  have hW'ψ : ∀ᶠ p in 𝓝 x, W' (d'.coordMap p) = W p := by
    have hr : ∀ᶠ z in 𝓝 (W x), W' (e.val.symm (Ψ' z)) = z := by rw [← hWx]; exact hΨr'
    filter_upwards [hWc.eventually hr] with p hp
    rw [hψ]; exact hp
  refine ⟨⟨d, d', fun p => rfl, fun p => rfl, rfl, pairCoord_apply_self hk u, hWW', ?_, ?_, ?_,
    ?_⟩⟩
  · filter_upwards [hWφ] with p hp
    have := congrArg (fun z : ComplexModel n => z k) hp
    simpa only [hW, hW', pairCoord_apply_self hk] using this
  · filter_upwards [hW'ψ] with p hp
    have := congrArg (fun z : ComplexModel n => z k) hp
    simpa only [hW, hW', pairCoord_apply_self hk] using this
  · filter_upwards [hWφ, hΨl', e.val.open_source.mem_nhds hxs] with p hp hpl hps
    rw [hψ, hp, hpl, e.val.left_inv hps]
  · filter_upwards [hW'ψ, hΨl, e.val.open_source.mem_nhds hxs] with p hp hpl hps
    rw [hφ, hp, hpl, e.val.left_inv hps]

end Pair

/-! ### The glueing lemma -/

namespace CoordinatePair

variable {x : M} {u v : M → ℂ} (P : CoordinatePair (n := n) x u v) {𝔞 : GermIdeal n M} {μ : ℕ}

theorem mem_tangentIdeal_h (h𝔞 : 𝔞.IsCoherent) (hu : (tangentIdeal 𝔞 μ).mem x u)
    (hv : (tangentIdeal 𝔞 μ).mem x v) : (tangentIdeal 𝔞 μ).mem x P.d.h := by
  have h : P.d.h = fun p => v p - u p := funext P.h_eq
  rw [h]
  exact sub_mem (isCoherent_iterDerivIdeal h𝔞 (μ - 1)) hv hu

theorem mem_tangentIdeal_h' (h𝔞 : 𝔞.IsCoherent) (hu : (tangentIdeal 𝔞 μ).mem x u)
    (hv : (tangentIdeal 𝔞 μ).mem x v) : (tangentIdeal 𝔞 μ).mem x P.d'.h := by
  have h : P.d'.h = fun p => u p - v p := funext P.h'_eq
  rw [h]
  exact sub_mem (isCoherent_iterDerivIdeal h𝔞 (μ - 1)) hu hv

/-- **`φ^* 𝓗(𝔞) = 𝓗(𝔞)` at `x`** (Włodarczyk, Lemma `le:homo0` (1), analytic form): for
`u, v ∈ T(𝔞)_x`, `f ∘ φ ∈ 𝓗(𝔞)_x` if and only if `f ∈ 𝓗(𝔞)_x`. -/
theorem comp_mem_homogenizedIdeal_iff (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (hu : (tangentIdeal 𝔞 μ).mem x u) (hv : (tangentIdeal 𝔞 μ).mem x v) {f : M → ℂ} :
    (homogenizedIdeal 𝔞 μ).mem x (fun p => f (P.d.coordMap p)) ↔
      (homogenizedIdeal 𝔞 μ).mem x f := by
  constructor
  · intro hf
    have h' := P.d'.comp_mem_homogenizedIdeal_of_mem h𝔞 hμ (P.mem_tangentIdeal_h' h𝔞 hu hv) hf
    refine DerivativeIdeal.isInSpanAt_congr h' ?_
    filter_upwards [P.right_inv] with p hp
    simp only [hp]
  · exact P.d.comp_mem_homogenizedIdeal_of_mem h𝔞 hμ (P.mem_tangentIdeal_h h𝔞 hu hv)

/-- **`φ` and `ψ` fix the cosupport** (Włodarczyk, `le:homo0` (4), `le:homo` (3)): near `x`, every
point of `cosupp(𝔞, μ)` is fixed by both coordinate changes. -/
theorem eventually_coordMap_eq_self_of_mem_cosupport (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (hu : (tangentIdeal 𝔞 μ).mem x u) (hv : (tangentIdeal 𝔞 μ).mem x v) :
    ∀ᶠ y in 𝓝 x, y ∈ cosupport n univ 𝔞 μ → P.d.coordMap y = y ∧ P.d'.coordMap y = y := by
  have hT := isCoherent_iterDerivIdeal h𝔞 (μ - 1)
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg => holomorphicAt_of_mem h𝔞 hg
  filter_upwards [eventually_mem hT hu, eventually_mem hT hv, eventually_coordMap_eq_self P.d,
    eventually_coordMap_eq_self P.d'] with y hyu hyv hy hy' hyc
  have h0u : u y = 0 := MaximalContact.apply_eq_zero_of_mem_cosupport hhol hμ hyc hyu
  have h0v : v y = 0 := MaximalContact.apply_eq_zero_of_mem_cosupport hhol hμ hyc hyv
  exact ⟨hy (by rw [P.h_eq, h0u, h0v, sub_zero]), hy' (by rw [P.h'_eq, h0u, h0v, sub_zero])⟩

/-- **`φ^* 𝓗(𝔞) = 𝓗(𝔞)` near `x`** (Włodarczyk, Lemma `le:homo` (1), analytic form, `E = ∅`): at
every point `y` near `x`, the pullback of `𝓗(𝔞)` by `φ` and `𝓗(𝔞)` have the same germs. -/
theorem eventually_pullback_homogenizedIdeal (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (hu : (tangentIdeal 𝔞 μ).mem x u) (hv : (tangentIdeal 𝔞 μ).mem x v) :
    ∀ᶠ y in 𝓝 x, ∀ g, (GermIdeal.pullback (m := n) P.d.coordMap (homogenizedIdeal 𝔞 μ)).mem y g ↔
      (homogenizedIdeal 𝔞 μ).mem y g := by
  have hH := isCoherent_homogenizedIdeal h𝔞 μ
  have h1 := eventually_pullback_le hH P.d.coordMap_self (eventually_mdifferentiableAt_coordMap P.d)
    (fun g hg => P.d.comp_mem_homogenizedIdeal_of_mem h𝔞 hμ (P.mem_tangentIdeal_h h𝔞 hu hv) hg)
  have h2 := eventually_pullback_le hH P.d'.coordMap_self (eventually_mdifferentiableAt_coordMap P.d')
    (fun g hg => P.d'.comp_mem_homogenizedIdeal_of_mem h𝔞 hμ (P.mem_tangentIdeal_h' h𝔞 hu hv) hg)
  have hφc : Tendsto P.d.coordMap (𝓝 x) (𝓝 x) := by
    have := P.d.continuousAt_coordMap
    rwa [ContinuousAt, P.d.coordMap_self] at this
  filter_upwards [h1, hφc.eventually h2, P.left_inv.eventually_nhds,
    hφc.eventually (eventually_mdifferentiableAt_coordMap P.d').eventually_nhds]
    with y hy1 hy2 hyinv hψd g
  refine ⟨hy1 g, fun hg => ?_⟩
  have hgh : HolomorphicAt n g y := holomorphicAt_of_mem hH hg
  have hψφ : P.d'.coordMap (P.d.coordMap y) = y := hyinv.self_of_nhds
  -- `g ∘ ψ ∈ 𝓗(𝔞)` at `φ y`
  have hgψ : (homogenizedIdeal 𝔞 μ).mem (P.d.coordMap y) (g ∘ P.d'.coordMap) := by
    refine hy2 _ (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr ?_)
    refine InvertibleIdealQuotient.isInSpanAt_self ⟨g, by rw [hψφ]; exact hg, rfl⟩ ?_
    exact HadamardBridge.holomorphicAt_comp_map hψd (by rw [hψφ]; exact hgh)
  -- `g = (g ∘ ψ) ∘ φ` near `y`
  refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
    (isInSpanAt_of_eq_mul ⟨g ∘ P.d'.coordMap, hgψ, rfl⟩ hgh (holomorphicAt_const 1) ?_)
  filter_upwards [hyinv] with p hp
  simp [hp]

end CoordinatePair

/-- **The Glueing Lemma** (Włodarczyk 2005, Lemma `le:homo` (1)–(3), for `E = ∅`; analytic form:
the étale neighbourhoods `φ_u, φ_v : X̄ → X` are an open neighbourhood of `x` with `φ_v = id` and
`φ_u = φ`).  Let `(𝔞, μ)` be a coherent marked ideal (`N = M`, `μ ≥ 1`), and let `u`, `v` be
tangent directions of `(𝔞, μ)` on open sets containing `x ∈ cosupp(𝔞, μ)`.  There are maps
`φ, ψ : M → M`, holomorphic near `x` and inverse to each other near `x`, with `φ x = x`, such that
1. `φ^* 𝓗(𝔞) = 𝓗(𝔞)` at every point near `x`;
2. `u ∘ φ = v` near `x`;
3. `φ` fixes `cosupp(𝔞, μ)` pointwise near `x`. -/
theorem glueing_lemma {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ) {x : M}
    (hx : x ∈ cosupport n univ 𝔞 μ) {U U' : Set M} {u v : M → ℂ}
    (hu : MaximalContact.IsTangentDirection 𝔞 μ U u) (hxU : x ∈ U)
    (hv : MaximalContact.IsTangentDirection 𝔞 μ U' v) (hxU' : x ∈ U') :
    ∃ φ ψ : M → M, φ x = x ∧
      (∀ᶠ p in 𝓝 x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p ∧
        MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ p) ∧
      (∀ᶠ p in 𝓝 x, ψ (φ p) = p ∧ φ (ψ p) = p) ∧
      (∀ᶠ y in 𝓝 x, ∀ g, (GermIdeal.pullback (m := n) φ (homogenizedIdeal 𝔞 μ)).mem y g ↔
        (homogenizedIdeal 𝔞 μ).mem y g) ∧
      (∀ᶠ p in 𝓝 x, u (φ p) = v p) ∧
      (∀ᶠ y in 𝓝 x, y ∈ cosupport n univ 𝔞 μ → φ y = y) := by
  have hT := isCoherent_iterDerivIdeal h𝔞 (μ - 1)
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg => holomorphicAt_of_mem h𝔞 hg
  have hux : (tangentIdeal 𝔞 μ).mem x u := hu.mem x hxU
  have hvx : (tangentIdeal 𝔞 μ).mem x v := hv.mem x hxU'
  have hu0 : u x = 0 := MaximalContact.apply_eq_zero_of_mem_cosupport hhol hμ hx hux
  have hv0 : v x = 0 := MaximalContact.apply_eq_zero_of_mem_cosupport hhol hμ hx hvx
  obtain ⟨P⟩ := exists_coordinatePair (holomorphicAt_of_mem hT hux) (holomorphicAt_of_mem hT hvx)
    (by rw [hu0, hv0]) (hu.multiplicity_one x hxU hu0) (hv.multiplicity_one x hxU' hv0)
  refine ⟨P.d.coordMap, P.d'.coordMap, P.d.coordMap_self,
    (eventually_mdifferentiableAt_coordMap P.d).and (eventually_mdifferentiableAt_coordMap P.d'),
    P.left_inv.and P.right_inv, P.eventually_pullback_homogenizedIdeal h𝔞 hμ hux hvx, P.comp_d, ?_⟩
  filter_upwards [P.eventually_coordMap_eq_self_of_mem_cosupport h𝔞 hμ hux hvx] with y hy hyc
  exact (hy hyc).1

end

end Hironaka.HomogenizedGlueing
