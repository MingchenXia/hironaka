/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HomogenizedIdeal
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPresentation
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The glueing lemma for homogenized ideals (analytic form)

Source: Włodarczyk 2005, §2.10, Lemmas `le:homo0` and `le:homo` (Glueing Lemma) (1)–(3), for `E = ∅` (the only case
the source uses), φ_v: X̄ → X` become an open neighbourhood of `x` with `φ_v = id` and `φ_u = φ` a convergent
coordinate change.

* `eventually_mem`: a germ of a coherent ideal at `x` is a germ of it at every point near `x`;
  `eventually_pullback_le`: if `φ` is holomorphic near `x`, `φ x = x` and `φ^* 𝔟 ⊆ 𝔟` at `x`
  (coherent `𝔟`), then `φ^* 𝔟 ⊆ 𝔟` at every point near `x`.

Not here: part (4) of `le:homo` (the multiple test blow-ups of `(𝓗(𝔞), μ)` are `φ`-equivariant);
it needs the transport of test towers along local biholomorphisms.
-/

open Set Filter
open scoped Topology Manifold

namespace Hironaka.HomogenizedGlueing

open Hironaka.HolomorphicIdealSheaves GermIdealOrder DerivativeIdeal IdealWeightPowers HomogenizedIdeal

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

end Pair

end

end Hironaka.HomogenizedGlueing
