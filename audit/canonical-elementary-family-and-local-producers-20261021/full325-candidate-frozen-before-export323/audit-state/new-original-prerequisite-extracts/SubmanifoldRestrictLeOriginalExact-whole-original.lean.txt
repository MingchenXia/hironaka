import TranscendentalNakamaye.Pending.SubmanifoldIdealRestriction
import TranscendentalNakamaye.Pending.RelativePrincipalizationSpan

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The ambient restricted comparison, read as an inclusion of ideals on the submanifold

Source: Copy-4, `lem:relative-principalization`\ref{it:rp-restriction} and the proof of
`prop:principalization`, Step 1.

Every existing Step-1 module states `Res_W 𝔞 ⊆ Res_W 𝔟` **ambiently**, as
`RestrictLe W 𝔞 𝔟` (`Pending.RestrictedIdealWeight`:269): at every point of `W`, each germ of
`𝔞` agrees *on `W`* with a holomorphic combination of germs of `𝔟`.  That is the only
comparison available — no inclusion of the ambient ideals holds.  With the submanifold made a
manifold (`Pending.SubmanifoldChartedSpace`), the same statement is literally an inclusion of
ideal sheaves on `↥W`, and this file proves that direction:

  `RestrictLe W 𝔞 𝔟`  ⟹  `Res_W 𝔞 ≤ Res_W 𝔟`   (`restrictIdeal_le_of_restrictLe`)

so the ambient `RestrictLe` facts already proved — `lem:relative-principalization`(iii) in
`Pending.RelativePrincipalizationRestrictedWeight`, and both halves of `eq:def-cM` on `W` in
`Pending.RestrictedIdealQuotient` — become statements about ideals on the strict transform.

Coherence of `𝔞` is needed and is not decoration: `GermIdeal.mem` is an arbitrary predicate, so
without it a germ of `𝔞` need not be holomorphic and `IsInSpanAt` on `↥W`, which demands
holomorphy of the germ, could not be formed.

## The converse is NOT proved here, and is not stated as an interface

`Res_W 𝔞 ≤ Res_W 𝔟 ⟹ RestrictLe W 𝔞 𝔟` needs ambient *coefficients*: `IsInSpanOnAt` asks for
holomorphic functions on `X`, while a subtype-level combination only supplies germs holomorphic
on `↥W`.  The missing input is the extension lemma — every holomorphic germ on `W` is the
restriction of an ambient one, which in a `FlatData` chart is `y ↦ b̂ (proj_k (Φ (e y)))`.  It is
real work, it is provable with the machinery now on disk, and it is deliberately left unnamed
rather than introduced as a hypothesis (I-0471).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace TranscendentalNakamaye.Pending.SubmanifoldRestrictLe

open FirstPass FirstPass.HolomorphicIdealSheaves
open TranscendentalNakamaye.Pending.RestrictedIdealWeight
open TranscendentalNakamaye.Pending.RelativePrincipalizationSpan
open TranscendentalNakamaye.Pending.SubmanifoldIdealRestriction

noncomputable section

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}
  [ChartedSpace (ComplexModel k) W] [IsComplexManifold k W]

/-- A germ of a coherent ideal is holomorphic.  `GermIdeal.mem` alone does not say this. -/
theorem holomorphicAt_of_mem_of_isCoherent {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    {x : X} {g : X → ℂ} (hg : 𝔞.mem x g) : HolomorphicAt n g x := by
  obtain ⟨U, hU, hxU, N, sgen, hsgen, hiff⟩ := h𝔞 x
  exact ((hiff x hxU g).mp hg).1

variable (hval : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X))

include hval in
/-- **The ambient restricted comparison is an inclusion of ideals on the submanifold.**  Each
germ of `𝔞` at a point of `W` agrees on `W` with `∑ cᵢ tᵢ`, `tᵢ ∈ 𝔟`; restricting the identity
to `↥W` exhibits it as a combination of germs of `Res_W 𝔟`, and `IsInSpanAt.trans` propagates
this from the generators to an arbitrary germ of `Res_W 𝔞`. -/
theorem restrictIdeal_le_of_restrictLe {𝔞 𝔟 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hle : RestrictLe W 𝔞 𝔟) :
    (restrictIdeal (k := k) (W := W) 𝔞).Le (restrictIdeal (k := k) (W := W) 𝔟) := by
  intro p G hG
  have hG' : IsInSpanAt (n := k)
      (fun s => ∃ a, 𝔞.mem p.1 a ∧ s = a ∘ (Subtype.val : W → X)) p G := hG
  show IsInSpanAt (n := k)
    (fun s => ∃ b, 𝔟.mem p.1 b ∧ s = b ∘ (Subtype.val : W → X)) p G
  refine IsInSpanAt.trans ?_ hG'
  rintro s ⟨a, hamem, rfl⟩
  obtain ⟨N, t, c, ht, hc, heq⟩ := hle p.1 p.2 a hamem
  refine ⟨holomorphicAt_comp_val hval (holomorphicAt_of_mem_of_isCoherent h𝔞 hamem),
    N, fun i => fun q : W => t i q.1, fun i => fun q : W => c i q.1,
    fun i => ⟨t i, ht i, rfl⟩,
    fun i => holomorphicAt_comp_val hval (hc i), ?_⟩
  have hev := (continuous_subtype_val.continuousAt (x := p)).eventually
    (p := fun y => y ∈ W → a y = ∑ i, c i y * t i y) heq
  filter_upwards [hev] with q hq
  exact hq q.2

end

end TranscendentalNakamaye.Pending.SubmanifoldRestrictLe
