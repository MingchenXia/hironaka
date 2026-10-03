/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.NormalDerivativeChart
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupExistenceCodimOne
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdeals
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Homogeneity of a smooth centre: translations along a submanifold

The half of `hir:smooth-centre` that is not about the invariant. The design proves that a resolution invariant of
`(U, U, ∅, 𝓘_Z, 1)` is constant along a closed connected submanifold `Z` by homogeneity: near two close points `x,
x'` of `Z`, a translation along `Z` in a chart in which `Z` is a coordinate subspace is a biholomorphism between
neighbourhoods of `x` and `x'` which maps `x` to `x'` and preserves `Z`, hence pulls the marked ideal back to
itself; properties (5) and (6) of the invariant then compare the two values. `SmoothCentreLocus` is the other half
(the cosupport is `Z`, the domain). Source: Włodarczyk 2005 (arXiv `hiron.tex`), the functoriality of the resolution
for étale morphisms (Proposition `pr:funct`, `pr:resol` (4)), applied to the canonical resolution of a smooth
centre, whose étale-local model is a coordinate subspace.

## Main results

* `exists_diffeomorph_opens_of_mapsTo`: holomorphic maps `φ : U → V`, `ψ : V → U` between open sets which are inverse to
  each other form a biholomorphism of the open submanifolds (Mathlib `Diffeomorph`).
* `pullback_pullback_val_vanishingIdeal`: for a biholomorphism `Φ : U₁ ≅ U₂` of open sets with `Φ⁻¹(Z ∩ U₂) = Z ∩ U₁`,
  `Φ^*(𝓘_Z|_{U₂}) = 𝓘_Z|_{U₁}`; `pullback_pullback_val_smoothCentreMarked`: the same for the marked ideal
  `(M, N, ∅, 𝓘_Z, d)` when `Φ` also preserves `N`.
* `exists_chart_transfer_of_regularAtDim`, `exists_smoothCentre_iso` (**the homogeneous local model**): the same for
  ANY two points at which `Z` has the same dimension (`Φ = ψ₂⁻¹ ∘ ψ₁` for flat charts `ψ₁`, `ψ₂` on a common ball),
  so that a resolution invariant is constant on a smooth centre of pure dimension, connected or not.
-/

open Set Filter TopologicalSpace Metric
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.SmoothCentreHomogeneity

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdealBiholomorphism NormalDerivativeChart BlowupFlatCoordinates

noncomputable section

variable {n : ℕ}

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

/-- **The homogeneous local model of a submanifold**: if `Z` is regular of the same dimension `k` at `x` and at `x'`
(any two points, not necessarily close), there are open sets `U₁ ∋ x`, `U₂ ∋ x'` and a biholomorphism `Φ: U₁ ≅ U₂`
with `Φ x = x'` which maps `Z ∩ U₁` onto `Z ∩ U₂`. With flat charts `ψ₁` of `Z` at `x` and `ψ₂` at `x'` (`ψᵢ = 0` at
the point, `Z` the plane `ℂᵏ × 0` near it), `Φ = ψ₂⁻¹ ∘ ψ₁` on a common ball. -/
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

/-! -/

section Homogeneity

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

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
