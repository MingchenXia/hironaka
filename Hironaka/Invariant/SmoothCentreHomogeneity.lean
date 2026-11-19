import Hironaka.MarkedIdeal.NormalDerivativeChart
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Homogeneity of a smooth centre: translations along a submanifold

Hironaka phase H3 (TN23-ENVELOPES), claimed on I-0981 C-0095 / I-0977 C-0134: the half of `hir:smooth-centre`
(`blueprint/src/hironaka.tex`) that is not about the invariant.  The design proves that a resolution invariant of
`(U, U, ∅, 𝓘_Z, 1)` is constant along a closed connected submanifold `Z` by homogeneity: near two close points `x, x'` of `Z`,
a translation along `Z` in a chart in which `Z` is a coordinate subspace is a biholomorphism between neighbourhoods of `x`
and `x'` which maps `x` to `x'` and preserves `Z`, hence pulls the marked ideal back to itself; properties (5) and (6) of
the invariant then compare the two values.  TN3's `SmoothCentreLocus` is the other half (the cosupport is `Z`, the domain).
Blueprint `mc:smooth-centre-translation` (`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005 (arXiv
`hiron.tex`), the functoriality of the resolution for étale morphisms (Proposition `pr:funct`, `pr:resol` (4)), applied to
the canonical resolution of a smooth centre, whose étale-local model is a coordinate subspace.

## Main results

* `add_mem_complexCoordinatePlane_iff`: translating by a vector of the coordinate plane `ℂᵏ × 0` preserves it.
* `exists_diffeomorph_opens_of_mapsTo`: holomorphic maps `φ : U → V`, `ψ : V → U` between open sets which are inverse to
  each other form a biholomorphism of the open submanifolds (Mathlib `Diffeomorph`).
* `exists_translation_of_regularAtDim` (**translations along a submanifold**): if `Z` is regular of dimension `k` at `x`,
  there is an open `W ∋ x` such that for every `x' ∈ Z ∩ W` there are open `U₁ ∋ x`, `U₂ ∋ x'` and a biholomorphism
  `Φ : U₁ ≅ U₂` with `Φ x = x'` and `Φ⁻¹(Z ∩ U₂) = Z ∩ U₁`.
* `pullback_pullback_val_vanishingIdeal`: for a biholomorphism `Φ : U₁ ≅ U₂` of open sets with `Φ⁻¹(Z ∩ U₂) = Z ∩ U₁`,
  `Φ^*(𝓘_Z|_{U₂}) = 𝓘_Z|_{U₁}`; `pullback_pullback_val_smoothCentreMarked`: the same for the marked ideal
  `(M, N, ∅, 𝓘_Z, d)` when `Φ` also preserves `N`.
* `exists_smoothCentre_homogeneity` (**the H3 half of `hir:smooth-centre`**): if `Z` is regular at `x`, there is an open
  `W ∋ x` such that every `x' ∈ Z ∩ W` has such a `Φ` with `Φ x = x'` and
  `Φ^*((M, M, ∅, 𝓘_Z, d)|_{U₂}) = (M, M, ∅, 𝓘_Z, d)|_{U₁}`.
* `exists_chart_transfer_of_regularAtDim`, `exists_smoothCentre_iso` (**the homogeneous local model**, claim I-0981 C-0141):
  the same for ANY two points at which `Z` has the same dimension (`Φ = ψ₂⁻¹ ∘ ψ₁` for flat charts `ψ₁`, `ψ₂` on a common
  ball), so that a resolution invariant is constant on a smooth centre of pure dimension, connected or not.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace Metric
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.SmoothCentreHomogeneity

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdealBiholomorphism NormalDerivativeChart BlowupFlatCoordinates

noncomputable section

variable {n : ℕ}

/-! ### The coordinate plane is a subgroup -/

theorem add_mem_complexCoordinatePlane_iff {k : ℕ} {z v : ComplexModel n} (hv : v ∈ complexCoordinatePlane n k) :
    z + v ∈ complexCoordinatePlane n k ↔ z ∈ complexCoordinatePlane n k := by
  constructor
  · intro h i hi
    have h1 := h i hi
    have h2 := hv i hi
    simp only [PiLp.add_apply] at h1
    rw [h2, add_zero] at h1
    exact h1
  · intro h i hi
    simp only [PiLp.add_apply]
    rw [h i hi, hv i hi, add_zero]

theorem neg_mem_complexCoordinatePlane {k : ℕ} {v : ComplexModel n} (hv : v ∈ complexCoordinatePlane n k) :
    -v ∈ complexCoordinatePlane n k := by
  intro i hi
  simp only [PiLp.neg_apply]
  rw [hv i hi, neg_zero]

/-! ### Biholomorphisms between open sets from inverse maps -/

section Diffeo

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Inverse holomorphic maps between open sets form a biholomorphism of the open submanifolds**: if `φ` maps the open
`U` into the open `V`, `ψ` maps `V` into `U`, both are holomorphic there and `ψ ∘ φ = id` on `U`, `φ ∘ ψ = id` on `V`, then
there is a biholomorphism `Φ : U ≅ V` (Mathlib `Diffeomorph` of the open submanifolds) with `Φ = φ` and `Φ⁻¹ = ψ`. -/
theorem exists_diffeomorph_opens_of_mapsTo {U V : Opens M} {φ ψ : M → M} (hφV : ∀ p ∈ U, φ p ∈ V)
    (hψU : ∀ q ∈ V, ψ q ∈ U)
    (hφd : ∀ p ∈ U, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (hψd : ∀ q ∈ V, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ q)
    (hl : ∀ p ∈ U, ψ (φ p) = p) (hr : ∀ q ∈ V, φ (ψ q) = q) :
    ∃ Φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V,
      (∀ p : U, ((Φ p : V) : M) = φ p) ∧ (∀ q : V, ((Φ.symm q : U) : M) = ψ q) := by
  have hφs : ∀ p ∈ U, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ p := fun p hp =>
    MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt'
      (Filter.mem_of_superset (U.isOpen.mem_nhds hp) fun q hq => hφd q hq)
  have hψs : ∀ q ∈ V, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ q := fun q hq =>
    MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt'
      (Filter.mem_of_superset (V.isOpen.mem_nhds hq) fun p hp => hψd p hp)
  have hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun p : U => (⟨φ p.1, hφV p.1 p.2⟩ : V)) :=
    BlowupRestrictOpen.contMDiff_opens_mk (fun p => (hφs p.1 p.2).comp p (contMDiff_subtype_val p))
      (fun p => hφV p.1 p.2)
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun q : V => (⟨ψ q.1, hψU q.1 q.2⟩ : U)) :=
    BlowupRestrictOpen.contMDiff_opens_mk (fun q => (hψs q.1 q.2).comp q (contMDiff_subtype_val q))
      (fun q => hψU q.1 q.2)
  exact ⟨⟨⟨fun p => ⟨φ p.1, hφV p.1 p.2⟩, fun q => ⟨ψ q.1, hψU q.1 q.2⟩,
      fun p => Subtype.ext (hl p.1 p.2), fun q => Subtype.ext (hr q.1 q.2)⟩, hf, hg⟩,
    fun _ => rfl, fun _ => rfl⟩

end Diffeo

/-! ### Translations along a submanifold -/

section Translation

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Translations along a submanifold** (the homogeneity of a smooth centre): if `Z` is regular of dimension `k` at `x`, there
is an open `W ∋ x` such that for every `x' ∈ Z ∩ W` there are open sets `U₁ ∋ x`, `U₂ ∋ x'` and a biholomorphism
`Φ : U₁ ≅ U₂` with `Φ x = x'` which maps `Z ∩ U₁` onto `Z ∩ U₂` (`Φ p ∈ Z ↔ p ∈ Z`).  In a flat chart `ψ` of `Z` at `x`
(`ψ x = 0`, `Z` the plane `ℂᵏ × 0` near `x`), `Φ = ψ⁻¹ ∘ (· + ψ x') ∘ ψ`. -/
theorem exists_translation_of_regularAtDim {Z : Set M} {x : M} {k : ℕ} (hZ : RegularAtDim (n := n) Z x k) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ ∀ x' ∈ Z ∩ W, ∃ (U₁ U₂ : Opens M)
      (Φ : CMfd.of (n := n) U₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U₂) (hx : x ∈ U₁),
      x' ∈ U₂ ∧ ((Φ ⟨x, hx⟩ : U₂) : M) = x' ∧ ∀ p : U₁, ((Φ p : U₂) : M) ∈ Z ↔ (p : M) ∈ Z := by
  set c := FlatChart.ofRegularAtDim hZ
  -- the good neighbourhood `A` of `x`
  obtain ⟨A, hAsub, hAo, hxA⟩ := mem_nhds_iff.mp
    ((c.eventually_mdifferentiableAt_ψ.and c.eventually_inv_ψ).and c.eventually_flat)
  have hψA : ∀ y ∈ A, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.ψ y := fun y hy =>
    (hAsub hy).1.1
  have hinvψ : ∀ y ∈ A, c.inv (c.ψ y) = y := fun y hy => (hAsub hy).1.2
  have hflat : ∀ y ∈ A, (y ∈ Z ↔ c.ψ y ∈ complexCoordinatePlane n k) := fun y hy => (hAsub hy).2
  -- the good ball around `0`
  have hB : ∀ᶠ w in 𝓝 (0 : ComplexModel n),
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.inv w ∧ c.ψ (c.inv w) = w ∧ c.inv w ∈ A :=
    c.eventually_mdifferentiableAt_inv.and (c.eventually_ψ_inv.and (c.tendsto_inv.eventually (hAo.mem_nhds hxA)))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hB
  set r := ρ / 2 with hr
  have hr0 : 0 < r := by positivity
  have h2r : ∀ w : ComplexModel n, ‖w‖ < 2 * r →
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.inv w ∧ c.ψ (c.inv w) = w ∧ c.inv w ∈ A :=
    fun w hw => hρsub (mem_ball_zero_iff.mpr (by rw [hr] at hw; linarith))
  have hψc : ContinuousOn c.ψ A := fun y hy => (hψA y hy).continuousAt.continuousWithinAt
  -- the open sets
  let UB : ComplexModel n → Opens M := fun v => ⟨A ∩ c.ψ ⁻¹' ball v r, hψc.isOpen_inter_preimage hAo isOpen_ball⟩
  refine ⟨UB 0, (UB 0).isOpen, ⟨hxA, by simp [c.ψ_self, hr0]⟩, fun x' hx' => ?_⟩
  obtain ⟨hx'Z, hx'A, hx'B⟩ := hx'
  set v := c.ψ x' with hv
  have hvP : v ∈ complexCoordinatePlane n k := (hflat x' hx'A).mp hx'Z
  have hvr : ‖v‖ < r := mem_ball_zero_iff.mp hx'B
  -- the translation and its inverse
  have hfwd : ∀ y ∈ UB 0, ‖c.ψ y + v‖ < 2 * r := fun y hy => by
    have h1 : ‖c.ψ y‖ < r := mem_ball_zero_iff.mp hy.2
    calc ‖c.ψ y + v‖ ≤ ‖c.ψ y‖ + ‖v‖ := norm_add_le _ _
      _ < 2 * r := by linarith
  have hbwd : ∀ q ∈ UB v, ‖c.ψ q - v‖ < 2 * r := fun q hq => by
    have h1 : ‖c.ψ q - v‖ < r := mem_ball_iff_norm.mp hq.2
    linarith
  obtain ⟨Φ, hΦ, -⟩ := exists_diffeomorph_opens_of_mapsTo (U := UB 0) (V := UB v)
    (φ := fun y => c.inv (c.ψ y + v)) (ψ := fun q => c.inv (c.ψ q - v))
    (fun y hy => ⟨(h2r _ (hfwd y hy)).2.2, by
      show c.ψ (c.inv (c.ψ y + v)) ∈ ball v r
      rw [(h2r _ (hfwd y hy)).2.1, mem_ball_iff_norm, add_sub_cancel_right]
      exact mem_ball_zero_iff.mp hy.2⟩)
    (fun q hq => ⟨(h2r _ (hbwd q hq)).2.2, by
      show c.ψ (c.inv (c.ψ q - v)) ∈ ball 0 r
      rw [(h2r _ (hbwd q hq)).2.1, mem_ball_zero_iff]
      exact mem_ball_iff_norm.mp hq.2⟩)
    (fun y hy => by
      have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (fun y => c.ψ y + v) y :=
        ((differentiableAt_id.add_const v).mdifferentiableAt).comp y (hψA y hy.1)
      have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (c.inv ∘ fun y => c.ψ y + v) y :=
        (h2r _ (hfwd y hy)).1.comp y h1
      exact h2)
    (fun q hq => by
      have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (fun q => c.ψ q - v) q :=
        ((differentiableAt_id.sub_const v).mdifferentiableAt).comp q (hψA q hq.1)
      have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (c.inv ∘ fun q => c.ψ q - v) q :=
        (h2r _ (hbwd q hq)).1.comp q h1
      exact h2)
    (fun y hy => by
      show c.inv (c.ψ (c.inv (c.ψ y + v)) - v) = y
      rw [(h2r _ (hfwd y hy)).2.1, add_sub_cancel_right, hinvψ y hy.1])
    (fun q hq => by
      show c.inv (c.ψ (c.inv (c.ψ q - v)) + v) = q
      rw [(h2r _ (hbwd q hq)).2.1, sub_add_cancel, hinvψ q hq.1])
  have hxU : x ∈ UB 0 := ⟨hxA, by simp [c.ψ_self, hr0]⟩
  refine ⟨UB 0, UB v, Φ, hxU, ⟨hx'A, by show c.ψ x' ∈ ball v r; rw [hv]; exact mem_ball_self hr0⟩, ?_, fun p => ?_⟩
  · rw [hΦ]
    show c.inv (c.ψ x + v) = x'
    rw [c.ψ_self, zero_add, hv, hinvψ x' hx'A]
  · rw [hΦ]
    have hpA : (p : M) ∈ A := p.2.1
    have hq := (h2r _ (hfwd p p.2))
    rw [hflat _ hq.2.2, hflat _ hpA, hq.2.1, add_mem_complexCoordinatePlane_iff hvP]

/-- **The homogeneous local model of a submanifold** (the two-point form of `exists_translation_of_regularAtDim`): if `Z` is
regular of the same dimension `k` at `x` and at `x'` (any two points, not necessarily close), there are open sets `U₁ ∋ x`,
`U₂ ∋ x'` and a biholomorphism `Φ : U₁ ≅ U₂` with `Φ x = x'` which maps `Z ∩ U₁` onto `Z ∩ U₂`.  With flat charts `ψ₁` of `Z`
at `x` and `ψ₂` at `x'` (`ψᵢ = 0` at the point, `Z` the plane `ℂᵏ × 0` near it), `Φ = ψ₂⁻¹ ∘ ψ₁` on a common ball. -/
theorem exists_chart_transfer_of_regularAtDim {Z : Set M} {x x' : M} {k : ℕ} (hZ : RegularAtDim (n := n) Z x k)
    (hZ' : RegularAtDim (n := n) Z x' k) :
    ∃ (U₁ U₂ : Opens M)
      (Φ : CMfd.of (n := n) U₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U₂) (hx : x ∈ U₁),
      x' ∈ U₂ ∧ ((Φ ⟨x, hx⟩ : U₂) : M) = x' ∧ ∀ p : U₁, ((Φ p : U₂) : M) ∈ Z ↔ (p : M) ∈ Z := by
  set c₁ := FlatChart.ofRegularAtDim hZ
  set c₂ := FlatChart.ofRegularAtDim hZ'
  -- the good neighbourhoods `A₁ ∋ x`, `A₂ ∋ x'`
  obtain ⟨A₁, hA₁sub, hA₁o, hxA₁⟩ := mem_nhds_iff.mp
    ((c₁.eventually_mdifferentiableAt_ψ.and c₁.eventually_inv_ψ).and c₁.eventually_flat)
  obtain ⟨A₂, hA₂sub, hA₂o, hxA₂⟩ := mem_nhds_iff.mp
    ((c₂.eventually_mdifferentiableAt_ψ.and c₂.eventually_inv_ψ).and c₂.eventually_flat)
  -- a common good ball around `0`
  have hB : ∀ᶠ w in 𝓝 (0 : ComplexModel n),
      (MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c₁.inv w ∧ c₁.ψ (c₁.inv w) = w ∧ c₁.inv w ∈ A₁) ∧
      (MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c₂.inv w ∧ c₂.ψ (c₂.inv w) = w ∧ c₂.inv w ∈ A₂) :=
    (c₁.eventually_mdifferentiableAt_inv.and
        (c₁.eventually_ψ_inv.and (c₁.tendsto_inv.eventually (hA₁o.mem_nhds hxA₁)))).and
      (c₂.eventually_mdifferentiableAt_inv.and
        (c₂.eventually_ψ_inv.and (c₂.tendsto_inv.eventually (hA₂o.mem_nhds hxA₂))))
  obtain ⟨r, hr0, hrsub⟩ := Metric.mem_nhds_iff.mp hB
  have hgood : ∀ w ∈ ball (0 : ComplexModel n) r,
      (MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c₁.inv w ∧ c₁.ψ (c₁.inv w) = w ∧ c₁.inv w ∈ A₁) ∧
      (MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c₂.inv w ∧ c₂.ψ (c₂.inv w) = w ∧ c₂.inv w ∈ A₂) :=
    fun w hw => hrsub hw
  have hψ₁c : ContinuousOn c₁.ψ A₁ := fun y hy => (hA₁sub hy).1.1.continuousAt.continuousWithinAt
  have hψ₂c : ContinuousOn c₂.ψ A₂ := fun y hy => (hA₂sub hy).1.1.continuousAt.continuousWithinAt
  let U₁ : Opens M := ⟨A₁ ∩ c₁.ψ ⁻¹' ball 0 r, hψ₁c.isOpen_inter_preimage hA₁o isOpen_ball⟩
  let U₂ : Opens M := ⟨A₂ ∩ c₂.ψ ⁻¹' ball 0 r, hψ₂c.isOpen_inter_preimage hA₂o isOpen_ball⟩
  obtain ⟨Φ, hΦ, -⟩ := exists_diffeomorph_opens_of_mapsTo (U := U₁) (V := U₂)
    (φ := fun y => c₂.inv (c₁.ψ y)) (ψ := fun q => c₁.inv (c₂.ψ q))
    (fun y hy => ⟨(hgood _ hy.2).2.2.2, by
      show c₂.ψ (c₂.inv (c₁.ψ y)) ∈ ball 0 r
      rw [(hgood _ hy.2).2.2.1]
      exact hy.2⟩)
    (fun q hq => ⟨(hgood _ hq.2).1.2.2, by
      show c₁.ψ (c₁.inv (c₂.ψ q)) ∈ ball 0 r
      rw [(hgood _ hq.2).1.2.1]
      exact hq.2⟩)
    (fun y hy => (hgood _ hy.2).2.1.comp y (hA₁sub hy.1).1.1)
    (fun q hq => (hgood _ hq.2).1.1.comp q (hA₂sub hq.1).1.1)
    (fun y hy => by
      show c₁.inv (c₂.ψ (c₂.inv (c₁.ψ y))) = y
      rw [(hgood _ hy.2).2.2.1, (hA₁sub hy.1).1.2])
    (fun q hq => by
      show c₂.inv (c₁.ψ (c₁.inv (c₂.ψ q))) = q
      rw [(hgood _ hq.2).1.2.1, (hA₂sub hq.1).1.2])
  have hxU : x ∈ U₁ := ⟨hxA₁, by simp [c₁.ψ_self, hr0]⟩
  have hx'U : x' ∈ U₂ := ⟨hxA₂, by simp [c₂.ψ_self, hr0]⟩
  refine ⟨U₁, U₂, Φ, hxU, hx'U, ?_, fun p => ?_⟩
  · rw [hΦ]
    show c₂.inv (c₁.ψ x) = x'
    rw [c₁.ψ_self, ← c₂.ψ_self, (hA₂sub hxA₂).1.2]
  · rw [hΦ]
    have hpA : (p : M) ∈ A₁ := p.2.1
    have hq := hgood _ p.2.2
    rw [(hA₂sub hq.2.2.2).2, (hA₁sub hpA).2, hq.2.2.1]

end Translation

/-! ### The vanishing ideal under a biholomorphism preserving `Z` -/

section Pullback

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The vanishing ideal restricted to an open set is the vanishing ideal of the trace: `𝓘_Z|_U = 𝓘_{Z ∩ U}`. -/
theorem pullback_val_vanishingIdeal (U : Opens M) (Z : Set M) :
    GermIdeal.pullback (m := n) (Subtype.val : U → M) (vanishingIdeal (n := n) Z) =
      vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' Z) := by
  have h := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) U (id : U → U) Z
  rw [show (Subtype.val ∘ (id : U → U)) = (Subtype.val : U → M) from rfl] at h
  rw [← h]
  exact GermIdeal.ext (funext fun _ => funext fun _ =>
    propext BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff)

/-- **The vanishing ideal under a biholomorphism of open sets preserving `Z`**: if `Φ : U₁ ≅ U₂` maps `Z ∩ U₁` onto
`Z ∩ U₂`, then `Φ^*(𝓘_Z|_{U₂}) = 𝓘_Z|_{U₁}`. -/
theorem pullback_pullback_val_vanishingIdeal {U₁ U₂ : Opens M} {Z : Set M}
    (Φ : CMfd.of (n := n) U₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U₂)
    (hΦ : ∀ p : U₁, ((Φ p : U₂) : M) ∈ Z ↔ (p : M) ∈ Z) :
    GermIdeal.pullback (m := n) Φ (GermIdeal.pullback (m := n) (Subtype.val : U₂ → M) (vanishingIdeal (n := n) Z)) =
      GermIdeal.pullback (m := n) (Subtype.val : U₁ → M) (vanishingIdeal (n := n) Z) := by
  rw [pullback_val_vanishingIdeal U₂ Z, pullback_val_vanishingIdeal U₁ Z]
  have hpre : (Φ : U₁ → U₂) ⁻¹' ((Subtype.val : U₂ → M) ⁻¹' Z) = (Subtype.val : U₁ → M) ⁻¹' Z := by
    ext p
    exact hΦ p
  have h := pullback_vanishingIdeal_preimage (φ := (Φ : U₁ → U₂)) (ψ := (Φ.symm : U₂ → U₁)) Φ.contMDiff
    Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply (g := (id : U₁ → U₁)) contMDiff_id
    ((Subtype.val : U₂ → M) ⁻¹' Z)
  rw [hpre] at h
  rw [show ((Φ : U₁ → U₂) ∘ (id : U₁ → U₁)) = (Φ : U₁ → U₂) from rfl] at h
  rw [← h]
  exact GermIdeal.ext (funext fun _ => funext fun _ =>
    propext BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff)

/-- **The marked ideal of a smooth centre under a biholomorphism preserving it**: if `Φ : U₁ ≅ U₂` maps `Z ∩ U₁` onto
`Z ∩ U₂` and `N ∩ U₁` onto `N ∩ U₂`, then `Φ^*((M, N, ∅, 𝓘_Z, d)|_{U₂}) = (M, N, ∅, 𝓘_Z, d)|_{U₁}`. -/
theorem pullback_pullback_val_smoothCentreMarked {U₁ U₂ : Opens M} {Z N : Set M} (d : ℕ)
    (Φ : CMfd.of (n := n) U₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U₂)
    (hΦ : ∀ p : U₁, ((Φ p : U₂) : M) ∈ Z ↔ (p : M) ∈ Z) (hΦN : ∀ p : U₁, ((Φ p : U₂) : M) ∈ N ↔ (p : M) ∈ N) :
    MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U₂ → M)
        (⟨N, [], vanishingIdeal (n := n) Z, d⟩ : MarkedIdeal n M)) =
      MarkedIdeal.pullback (Subtype.val : U₁ → M) (⟨N, [], vanishingIdeal (n := n) Z, d⟩ : MarkedIdeal n M) := by
  have hN : (Φ : U₁ → U₂) ⁻¹' ((Subtype.val : U₂ → M) ⁻¹' N) = (Subtype.val : U₁ → M) ⁻¹' N := by
    ext p
    exact hΦN p
  show (⟨(Φ : U₁ → U₂) ⁻¹' ((Subtype.val : U₂ → M) ⁻¹' N), [],
      GermIdeal.pullback (m := n) Φ (GermIdeal.pullback (m := n) (Subtype.val : U₂ → M) (vanishingIdeal (n := n) Z)),
      d⟩ : MarkedIdeal n U₁) =
    ⟨(Subtype.val : U₁ → M) ⁻¹' N, [], GermIdeal.pullback (m := n) (Subtype.val : U₁ → M) (vanishingIdeal (n := n) Z), d⟩
  rw [hN, pullback_pullback_val_vanishingIdeal Φ hΦ]

end Pullback

/-! ### The H3 half of `hir:smooth-centre` -/

section Homogeneity

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Homogeneity of a smooth centre** (the H3 half of `hir:smooth-centre`): if `Z` is regular of dimension `k` at `x`, there is
an open `W ∋ x` such that every `x' ∈ Z ∩ W` has open neighbourhoods `U₁ ∋ x`, `U₂ ∋ x'` and a biholomorphism `Φ : U₁ ≅ U₂`
with `Φ x = x'`, `Φ⁻¹(Z ∩ U₂) = Z ∩ U₁` and `Φ^*((M, M, ∅, 𝓘_Z, d)|_{U₂}) = (M, M, ∅, 𝓘_Z, d)|_{U₁}`.  With properties (5)
and (6) of a resolution invariant for the empty towers (`IsTowerIso Φ refl refl Φ`) this makes the invariant of
`(M, M, ∅, 𝓘_Z, d)` locally constant on `Z`. -/
theorem exists_smoothCentre_homogeneity {Z : Set M} {x : M} {k : ℕ} (hZ : RegularAtDim (n := n) Z x k) (d : ℕ) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ ∀ x' ∈ Z ∩ W, ∃ (U₁ U₂ : Opens M)
      (Φ : CMfd.of (n := n) U₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U₂) (hx : x ∈ U₁),
      x' ∈ U₂ ∧ ((Φ ⟨x, hx⟩ : U₂) : M) = x' ∧ (∀ p : U₁, ((Φ p : U₂) : M) ∈ Z ↔ (p : M) ∈ Z) ∧
      MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U₂ → M)
          (⟨univ, [], vanishingIdeal (n := n) Z, d⟩ : MarkedIdeal n M)) =
        MarkedIdeal.pullback (Subtype.val : U₁ → M) (⟨univ, [], vanishingIdeal (n := n) Z, d⟩ : MarkedIdeal n M) := by
  obtain ⟨W, hWo, hxW, hW⟩ := exists_translation_of_regularAtDim hZ
  refine ⟨W, hWo, hxW, fun x' hx' => ?_⟩
  obtain ⟨U₁, U₂, Φ, hx, hx', hΦx, hΦ⟩ := hW x' hx'
  exact ⟨U₁, U₂, Φ, hx, hx', hΦx, hΦ,
    pullback_pullback_val_smoothCentreMarked d Φ hΦ (fun _ => by simp only [mem_univ])⟩

/-- **The homogeneous local model of a smooth centre** (two points of the same local dimension, not necessarily close): if `Z`
is regular of dimension `k` at `x` and at `x'`, there are open `U₁ ∋ x`, `U₂ ∋ x'` and a biholomorphism `Φ : U₁ ≅ U₂` with
`Φ x = x'`, `Φ⁻¹(Z ∩ U₂) = Z ∩ U₁` and `Φ^*((M, M, ∅, 𝓘_Z, d)|_{U₂}) = (M, M, ∅, 𝓘_Z, d)|_{U₁}`
(`exists_chart_transfer_of_regularAtDim`). -/
theorem exists_smoothCentre_iso {Z : Set M} {x x' : M} {k : ℕ} (hZ : RegularAtDim (n := n) Z x k)
    (hZ' : RegularAtDim (n := n) Z x' k) (d : ℕ) :
    ∃ (U₁ U₂ : Opens M)
      (Φ : CMfd.of (n := n) U₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U₂) (hx : x ∈ U₁),
      x' ∈ U₂ ∧ ((Φ ⟨x, hx⟩ : U₂) : M) = x' ∧ (∀ p : U₁, ((Φ p : U₂) : M) ∈ Z ↔ (p : M) ∈ Z) ∧
      MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U₂ → M)
          (⟨univ, [], vanishingIdeal (n := n) Z, d⟩ : MarkedIdeal n M)) =
        MarkedIdeal.pullback (Subtype.val : U₁ → M) (⟨univ, [], vanishingIdeal (n := n) Z, d⟩ : MarkedIdeal n M) := by
  obtain ⟨U₁, U₂, Φ, hx, hx', hΦx, hΦ⟩ := exists_chart_transfer_of_regularAtDim hZ hZ'
  exact ⟨U₁, U₂, Φ, hx, hx', hΦx, hΦ,
    pullback_pullback_val_smoothCentreMarked d Φ hΦ (fun _ => by simp only [mem_univ])⟩

end Homogeneity

end

end Hironaka.SmoothCentreHomogeneity
