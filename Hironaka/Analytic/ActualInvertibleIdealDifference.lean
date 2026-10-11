/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.GermIdealTotalTransform

set_option autoImplicit false

/-! # Effective differences of actual invertible holomorphic ideals

Two nested invertible ideals have
an invertible actual colon ideal, and hence their difference is an
effective divisor on the same manifold.  No second principalization is
assumed.  The proof cancels germs rather than dividing at a zero.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.ActualInvertibleIdealDifference

open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  InvertibleIdealQuotient GermIdealTotalTransform

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Nested actual invertible ideals have an invertible actual colon ideal. -/
theorem isInvertible_colon {𝔞 𝔩 : GermIdeal n M}
    (h𝔞 : 𝔞.IsInvertible) (h𝔩 : 𝔩.IsInvertible) (hle : 𝔞.Le 𝔩) :
    (colon 𝔞 𝔩).IsInvertible := by
  intro x
  obtain ⟨U₁, hU₁, hxU₁, a, ha, hnonA, hgenA⟩ := h𝔞 x
  obtain ⟨U₂, hU₂, hxU₂, l, hl, hnonL, hgenL⟩ := h𝔩 x
  have hahol : ∀ y ∈ U₁, HolomorphicAt n a y := fun y hy =>
    holomorphicAt_of_mdifferentiableOn hU₁ ha hy
  have hlhol : ∀ y ∈ U₂, HolomorphicAt n l y := fun y hy =>
    holomorphicAt_of_mdifferentiableOn hU₂ hl hy
  have hamem : 𝔞.mem x a := (hgenA x hxU₁ a).mpr
    (isInSpanAt_self rfl (hahol x hxU₁))
  obtain ⟨-, q, hq, heq⟩ := isInSpanAt_eq_iff.mp
    ((hgenL x hxU₂ a).mp (hle x a hamem))
  have hmem : {y | y ∈ U₁ ∧ y ∈ U₂ ∧ HolomorphicAt n q y ∧ a y = q y * l y}
      ∈ 𝓝 x := by
    filter_upwards [hU₁.mem_nhds hxU₁, hU₂.mem_nhds hxU₂, hq.eventually, heq]
      with y h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hmem
  refine ⟨U, hU, hxU, q, ?_, ?_, ?_⟩
  · intro y hy
    exact (hUsub hy).2.2.1.mdifferentiableAt.mdifferentiableWithinAt
  · intro W hW hWU hWne
    obtain ⟨y, hy, hane⟩ := hnonA W hW (fun z hz => (hUsub (hWU hz)).1) hWne
    refine ⟨y, hy, ?_⟩
    intro hq0
    exact hane (by rw [(hUsub (hWU hy)).2.2.2, hq0, zero_mul])
  intro y hy f
  have hy₁ : y ∈ U₁ := (hUsub hy).1
  have hy₂ : y ∈ U₂ := (hUsub hy).2.1
  have hqy : HolomorphicAt n q y := (hUsub hy).2.2.1
  have heqU : a =ᶠ[𝓝 y] fun z => q z * l z := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact (hUsub hz).2.2.2
  constructor
  · intro hf
    obtain ⟨hfhol, hfc⟩ := mem_colon_iff.mp hf
    have hlmem : 𝔩.mem y l := (hgenL y hy₂ l).mpr
      (isInSpanAt_self rfl (hlhol y hy₂))
    obtain ⟨-, b, hb, hbeq⟩ := isInSpanAt_eq_iff.mp
      ((hgenA y hy₁ _).mp (hfc l hlmem))
    have hcancel : f =ᶠ[𝓝 y] fun z => b z * q z := by
      refine eventuallyEq_of_mul_eventuallyEq hU₂ hnonL hy₂ hfhol (hb.mul hqy) ?_
      filter_upwards [hbeq, heqU] with z hz hza
      calc l z * f z = b z * a z := hz
        _ = l z * (b z * q z) := by rw [hza]; ring
    exact isInSpanAt_of_eq_mul rfl hfhol hb hcancel
  · intro hf
    obtain ⟨hfhol, b, hb, hbeq⟩ := isInSpanAt_eq_iff.mp hf
    refine mem_colon_iff.mpr ⟨hfhol, fun g hg => ?_⟩
    obtain ⟨-, c, hc, hceq⟩ := isInSpanAt_eq_iff.mp ((hgenL y hy₂ g).mp hg)
    refine (hgenA y hy₁ _).mpr
      (isInSpanAt_of_eq_mul rfl
        ((GermIdeal.IsInvertible.holomorphicAt_mem h𝔩 hg).mul hfhol) (hc.mul hb) ?_)
    filter_upwards [hceq, hbeq, heqU] with z hzg hzf hza
    show g z * f z = (c z * b z) * a z
    rw [hzg, hzf, hza]
    ring

/-- An inclusion between actual divisor ideals produces an effective difference
on the same manifold, with equality of the actual product ideals. -/
theorem exists_effectiveDivisor_difference (D_A D_L : EffectiveDivisor n M)
    (hle : D_A.ideal.Le D_L.ideal) :
    ∃ F : EffectiveDivisor n M, D_A.ideal = D_L.ideal.mul F.ideal := by
  let F : EffectiveDivisor n M :=
    ⟨colon D_A.ideal D_L.ideal,
      isInvertible_colon D_A.isInvertible D_L.isInvertible hle⟩
  refine ⟨F, ?_⟩
  have hcoh := DivisorMetric.isCoherent_of_isInvertible D_A.isInvertible
  exact GermIdeal.ext (funext fun x => funext fun g => propext
    ⟨fun hg => le_mul_colon hcoh D_L.isInvertible hle x g hg,
      fun hg => mul_colon_le hcoh x g hg⟩)

end
end Hironaka.ActualInvertibleIdealDifference
