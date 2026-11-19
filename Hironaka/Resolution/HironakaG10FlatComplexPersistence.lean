import Hironaka.Resolution.HironakaG10FlatGeneralizedInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Direct exactness of a family of complexes persists, with holomorphic generalized inverses

Douady 1966, §2 n° 3, Prop. 3 (used in §7 Prop. 6 and §8): a holomorphic family of complexes of
Banach spaces `0 → E_p → ⋯ → E₀` which is exact (in degrees `≥ 1`) and direct at `s₀` stays so near
`s₀`, with a local holomorphic splitting. This module proves the descending-induction step, with
directness carried by generalized inverses (`HironakaG10FlatGeneralizedInverse`).

Let `E₂ →d₂(s) E₁ →d₁(s) E₀` be families of bounded operators with `d₁(s) d₂(s) = 0`, and `R₂(s)` a
generalized inverse of `d₂(s)` (`d₂ R₂ d₂ = d₂`) near `s₀`; let `P(s) = d₂(s) R₂(s)` (a projection
onto `im d₂(s)`), `Q₀ = 1 − P(s₀)`, and `S₀` a generalized inverse of `d₁(s₀)`. Put
`M(s) = Q₀ S₀ d₁(s) (1 − P(s)) + P(s)` (`stepOp`) and `R₁(s) = M(s)⁻¹ Q₀ S₀` (`stepInv`).

* `stepOp_self`: if `ker d₁(s₀) ⊆ im d₂(s₀)`, then `M(s₀) = 1`.
* `stepInv_spec`: whenever `M(s)` is invertible, `ker d₁(s) = im d₂(s)` and `d₁ R₁ d₁ = d₁` at `s`.
* `eventually_step`: if `d₁` and `P` are continuous at `s₀`, then near `s₀` the complex is exact at
  `E₁` and `R₁(s)` is a generalized inverse of `d₁(s)`;
  `differentiableAt_stepInv` / `continuousAt_stepInv`: `R₁` is holomorphic (continuous) wherever
  `d₁`, `d₂`, `R₂` are and `M` is invertible; `eventually_differentiableAt_stepInv`.

Applied from the top degree down (at the top, `d₂ = 0`, `R₂ = 0`), this gives for a finite resolution
direct exact at `s₀` exactness and holomorphic generalized inverses in every degree near `s₀`.
BP: hironaka-g10-flat-complex-persistence.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FlatComplexPersistence
noncomputable section

variable {E₂ E₁ E₀ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [NormedAddCommGroup E₁]
  [NormedSpace ℂ E₁] [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]

/-- The comparison operator `M = Q₀ S₀ d₁ (1 − P) + P`. -/
def stepOp (Q₀ : E₁ →L[ℂ] E₁) (S₀ : E₀ →L[ℂ] E₁) (d₁ : E₁ →L[ℂ] E₀) (P : E₁ →L[ℂ] E₁) :
    E₁ →L[ℂ] E₁ :=
  Q₀.comp (S₀.comp (d₁.comp (ContinuousLinearMap.id ℂ E₁ - P))) + P

/-- The candidate generalized inverse `R₁ = M⁻¹ Q₀ S₀`. -/
def stepInv (Q₀ : E₁ →L[ℂ] E₁) (S₀ : E₀ →L[ℂ] E₁) (d₁ : E₁ →L[ℂ] E₀) (P : E₁ →L[ℂ] E₁) :
    E₀ →L[ℂ] E₁ :=
  (stepOp Q₀ S₀ d₁ P).inverse.comp (Q₀.comp S₀)

theorem stepOp_apply (Q₀ : E₁ →L[ℂ] E₁) (S₀ : E₀ →L[ℂ] E₁) (d₁ : E₁ →L[ℂ] E₀)
    (P : E₁ →L[ℂ] E₁) (x : E₁) : stepOp Q₀ S₀ d₁ P x = Q₀ (S₀ (d₁ (x - P x))) + P x := rfl

variable {d₂ : E₂ →L[ℂ] E₁} {R₂ : E₁ →L[ℂ] E₂} {d₁ : E₁ →L[ℂ] E₀}

theorem proj_idem (hR₂ : ∀ x, d₂ (R₂ (d₂ x)) = d₂ x) (x : E₁) :
    d₂ (R₂ (d₂ (R₂ x))) = d₂ (R₂ x) := hR₂ (R₂ x)

/-- **At `s₀` the comparison operator is the identity.** -/
theorem stepOp_self (hR₂ : ∀ x, d₂ (R₂ (d₂ x)) = d₂ x) (hex : ∀ x, d₁ x = 0 → ∃ u, d₂ u = x)
    {S₀ : E₀ →L[ℂ] E₁} (hS₀ : ∀ x, d₁ (S₀ (d₁ x)) = d₁ x) :
    stepOp (ContinuousLinearMap.id ℂ E₁ - d₂.comp R₂) S₀ d₁ (d₂.comp R₂) =
      ContinuousLinearMap.id ℂ E₁ := by
  have claim : ∀ y, S₀ (d₁ y) - d₂ (R₂ (S₀ (d₁ y))) = y - d₂ (R₂ y) := by
    intro y
    -- `S₀ d₁ y − y ∈ ker d₁ = im d₂` is fixed by `P`
    have hk : d₁ (S₀ (d₁ y) - y) = 0 := by rw [map_sub, hS₀, sub_self]
    obtain ⟨u, hu⟩ := hex _ hk
    have h2 : d₂ (R₂ (S₀ (d₁ y))) - d₂ (R₂ y) = S₀ (d₁ y) - y := by
      rw [← map_sub, ← map_sub, ← hu, hR₂]
    rw [← sub_eq_zero, show S₀ (d₁ y) - d₂ (R₂ (S₀ (d₁ y))) - (y - d₂ (R₂ y)) =
      (S₀ (d₁ y) - y) - (d₂ (R₂ (S₀ (d₁ y))) - d₂ (R₂ y)) by abel, h2, sub_self]
  ext x
  rw [stepOp_apply]
  show S₀ (d₁ (x - d₂ (R₂ x))) - d₂ (R₂ (S₀ (d₁ (x - d₂ (R₂ x))))) + d₂ (R₂ x) = x
  rw [claim, map_sub, map_sub, proj_idem hR₂, sub_self, sub_zero, sub_add_cancel]

/-- **Exactness and a generalized inverse wherever the comparison operator is invertible.** -/
theorem stepInv_spec (hR₂ : ∀ x, d₂ (R₂ (d₂ x)) = d₂ x) (hcomp : ∀ u, d₁ (d₂ u) = 0)
    {Q₀ : E₁ →L[ℂ] E₁} {S₀ : E₀ →L[ℂ] E₁} (hM : (stepOp Q₀ S₀ d₁ (d₂.comp R₂)).IsInvertible) :
    (∀ x, d₁ x = 0 → ∃ u, d₂ u = x) ∧
      ∀ x, d₁ (stepInv Q₀ S₀ d₁ (d₂.comp R₂) (d₁ x)) = d₁ x := by
  obtain ⟨e, he⟩ := hM
  have hinj : ∀ a b, stepOp Q₀ S₀ d₁ (d₂.comp R₂) a = stepOp Q₀ S₀ d₁ (d₂.comp R₂) b → a = b := by
    intro a b hab
    rw [← he] at hab
    exact e.injective hab
  have hdP : ∀ x, d₁ (d₂ (R₂ x)) = 0 := fun x => hcomp _
  -- `M (x − P x) = Q₀ S₀ d₁ x`
  have hMQ : ∀ x, stepOp Q₀ S₀ d₁ (d₂.comp R₂) (x - d₂ (R₂ x)) = Q₀ (S₀ (d₁ x)) := by
    intro x
    rw [stepOp_apply]
    show Q₀ (S₀ (d₁ (x - d₂ (R₂ x) - d₂ (R₂ (x - d₂ (R₂ x)))))) + d₂ (R₂ (x - d₂ (R₂ x))) = _
    have h0 : d₂ (R₂ (x - d₂ (R₂ x))) = 0 := by rw [map_sub, map_sub, proj_idem hR₂, sub_self]
    rw [h0, sub_zero, add_zero, map_sub, hdP, sub_zero]
  refine ⟨fun x hx => ⟨R₂ x, ?_⟩, fun x => ?_⟩
  · have h : stepOp Q₀ S₀ d₁ (d₂.comp R₂) (x - d₂ (R₂ x)) = stepOp Q₀ S₀ d₁ (d₂.comp R₂) 0 := by
      rw [hMQ, hx, map_zero, map_zero, map_zero]
    exact (sub_eq_zero.mp (hinj _ _ h)).symm
  · have hu : stepInv Q₀ S₀ d₁ (d₂.comp R₂) (d₁ x) = x - d₂ (R₂ x) := by
      apply hinj
      rw [hMQ]
      show stepOp Q₀ S₀ d₁ (d₂.comp R₂) ((stepOp Q₀ S₀ d₁ (d₂.comp R₂)).inverse
        (Q₀ (S₀ (d₁ x)))) = _
      rw [← he, ContinuousLinearMap.inverse_equiv]
      exact e.apply_symm_apply _
    rw [hu, map_sub, hdP, sub_zero]

/-! ## Families -/

section Family
variable {X : Type*} [TopologicalSpace X] {d₂ : X → E₂ →L[ℂ] E₁} {R₂ : X → E₁ →L[ℂ] E₂}
  {d₁ : X → E₁ →L[ℂ] E₀} {s₀ : X}

/-- The projection `P(s) = d₂(s) R₂(s)`. -/
abbrev projFam (d₂ : X → E₂ →L[ℂ] E₁) (R₂ : X → E₁ →L[ℂ] E₂) (s : X) : E₁ →L[ℂ] E₁ :=
  (d₂ s).comp (R₂ s)

/-- The generalized inverse family `R₁(s) = M(s)⁻¹ Q₀ S₀`, `Q₀ = 1 − P(s₀)`. -/
def stepInvFam (d₂ : X → E₂ →L[ℂ] E₁) (R₂ : X → E₁ →L[ℂ] E₂) (d₁ : X → E₁ →L[ℂ] E₀) (s₀ : X)
    (S₀ : E₀ →L[ℂ] E₁) (s : X) : E₀ →L[ℂ] E₁ :=
  stepInv (ContinuousLinearMap.id ℂ E₁ - projFam d₂ R₂ s₀) S₀ (d₁ s) (projFam d₂ R₂ s)

/-- **Persistence step** (Douady §2 Prop. 3, descending induction): near `s₀` the complex is exact
at `E₁` and `R₁(s)` is a generalized inverse of `d₁(s)`. -/
theorem eventually_step [CompleteSpace E₁] (hd₁ : ContinuousAt d₁ s₀)
    (hP : ContinuousAt (projFam d₂ R₂) s₀)
    (hR₂ : ∀ᶠ s in 𝓝 s₀, ∀ x, d₂ s (R₂ s (d₂ s x)) = d₂ s x)
    (hcomp : ∀ᶠ s in 𝓝 s₀, ∀ u, d₁ s (d₂ s u) = 0)
    (hex : ∀ x, d₁ s₀ x = 0 → ∃ u, d₂ s₀ u = x)
    {S₀ : E₀ →L[ℂ] E₁} (hS₀ : ∀ x, d₁ s₀ (S₀ (d₁ s₀ x)) = d₁ s₀ x) :
    ∀ᶠ s in 𝓝 s₀, (stepOp (ContinuousLinearMap.id ℂ E₁ - projFam d₂ R₂ s₀) S₀ (d₁ s)
        (projFam d₂ R₂ s)).IsInvertible ∧ (∀ x, d₁ s x = 0 → ∃ u, d₂ s u = x) ∧
      ∀ x, d₁ s (stepInvFam d₂ R₂ d₁ s₀ S₀ s (d₁ s x)) = d₁ s x := by
  set Q₀ := ContinuousLinearMap.id ℂ E₁ - projFam d₂ R₂ s₀
  have hcont : ContinuousAt (fun s => stepOp Q₀ S₀ (d₁ s) (projFam d₂ R₂ s)) s₀ := by
    unfold stepOp
    exact (continuousAt_const.clm_comp (continuousAt_const.clm_comp
      (hd₁.clm_comp (continuousAt_const.sub hP)))).add hP
  have hself : stepOp Q₀ S₀ (d₁ s₀) (projFam d₂ R₂ s₀) = ContinuousLinearMap.id ℂ E₁ :=
    stepOp_self hR₂.self_of_nhds hex hS₀
  have hmem : range ((↑) : (E₁ ≃L[ℂ] E₁) → E₁ →L[ℂ] E₁) ∈
      𝓝 (stepOp Q₀ S₀ (d₁ s₀) (projFam d₂ R₂ s₀)) := by
    rw [hself, ← ContinuousLinearEquiv.coe_refl]
    exact ContinuousLinearEquiv.nhds _
  filter_upwards [hcont hmem, hR₂, hcomp] with s hs hRs hcs
  have hinv : (stepOp Q₀ S₀ (d₁ s) (projFam d₂ R₂ s)).IsInvertible := by
    obtain ⟨e, he⟩ := hs
    exact ⟨e, he⟩
  exact ⟨hinv, stepInv_spec hRs hcs hinv⟩

/-- **Holomorphy of the generalized inverse family** at a point where `M` is invertible. -/
theorem differentiableAt_stepInvFam [CompleteSpace E₁] {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] {d₂ : Y → E₂ →L[ℂ] E₁} {R₂ : Y → E₁ →L[ℂ] E₂} {d₁ : Y → E₁ →L[ℂ] E₀}
    {s₀ s : Y} {S₀ : E₀ →L[ℂ] E₁} (hd₁ : DifferentiableAt ℂ d₁ s)
    (hd₂ : DifferentiableAt ℂ d₂ s) (hR₂' : DifferentiableAt ℂ R₂ s)
    (hinv : (stepOp (ContinuousLinearMap.id ℂ E₁ - projFam d₂ R₂ s₀) S₀ (d₁ s)
        (projFam d₂ R₂ s)).IsInvertible) :
    DifferentiableAt ℂ (stepInvFam d₂ R₂ d₁ s₀ S₀) s := by
  have hP : DifferentiableAt ℂ (projFam d₂ R₂) s := hd₂.clm_comp hR₂'
  have hM : DifferentiableAt ℂ (fun t => stepOp (ContinuousLinearMap.id ℂ E₁ - projFam d₂ R₂ s₀)
      S₀ (d₁ t) (projFam d₂ R₂ t)) s := by
    unfold stepOp
    exact ((differentiableAt_const _).clm_comp ((differentiableAt_const _).clm_comp
      (hd₁.clm_comp ((differentiableAt_const _).sub hP)))).add hP
  have hI : DifferentiableAt ℂ (ContinuousLinearMap.inverse ∘ fun t => stepOp
      (ContinuousLinearMap.id ℂ E₁ - projFam d₂ R₂ s₀) S₀ (d₁ t) (projFam d₂ R₂ t)) s :=
    DifferentiableAt.comp (g := ContinuousLinearMap.inverse) s
      ((hinv.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero) hM
  exact hI.clm_comp (differentiableAt_const _)

/-- **Continuity of the generalized inverse family** at a point where `M` is invertible. -/
theorem continuousAt_stepInvFam [CompleteSpace E₁] {s : X} {S₀ : E₀ →L[ℂ] E₁}
    (hd₁ : ContinuousAt d₁ s) (hP : ContinuousAt (projFam d₂ R₂) s)
    (hinv : (stepOp (ContinuousLinearMap.id ℂ E₁ - projFam d₂ R₂ s₀) S₀ (d₁ s)
        (projFam d₂ R₂ s)).IsInvertible) :
    ContinuousAt (stepInvFam d₂ R₂ d₁ s₀ S₀) s := by
  have hM : ContinuousAt (fun t => stepOp (ContinuousLinearMap.id ℂ E₁ - projFam d₂ R₂ s₀)
      S₀ (d₁ t) (projFam d₂ R₂ t)) s := by
    unfold stepOp
    exact (continuousAt_const.clm_comp (continuousAt_const.clm_comp
      (hd₁.clm_comp (continuousAt_const.sub hP)))).add hP
  have hI : ContinuousAt (ContinuousLinearMap.inverse ∘ fun t => stepOp
      (ContinuousLinearMap.id ℂ E₁ - projFam d₂ R₂ s₀) S₀ (d₁ t) (projFam d₂ R₂ t)) s :=
    ContinuousAt.comp (g := ContinuousLinearMap.inverse)
      (hinv.contDiffAt_map_inverse (n := 0)).continuousAt hM
  exact hI.clm_comp continuousAt_const

/-- **The persistence step with holomorphic data**: if `d₁`, `d₂`, `R₂` are holomorphic near `s₀`,
`R₂(s)` is a generalized inverse of `d₂(s)` and `d₁ d₂ = 0` near `s₀`, and at `s₀` the complex is
exact at `E₁` with `d₁(s₀)` direct, then near `s₀` the complex is exact at `E₁` and `R₁` is a
holomorphic family of generalized inverses of `d₁`. -/
theorem eventually_step_holomorphic [CompleteSpace E₁] {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] {d₂ : Y → E₂ →L[ℂ] E₁} {R₂ : Y → E₁ →L[ℂ] E₂} {d₁ : Y → E₁ →L[ℂ] E₀}
    {s₀ : Y} (hd₁ : ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ d₁ s)
    (hd₂ : ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ d₂ s) (hR₂' : ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ R₂ s)
    (hR₂ : ∀ᶠ s in 𝓝 s₀, ∀ x, d₂ s (R₂ s (d₂ s x)) = d₂ s x)
    (hcomp : ∀ᶠ s in 𝓝 s₀, ∀ u, d₁ s (d₂ s u) = 0)
    (hex : ∀ x, d₁ s₀ x = 0 → ∃ u, d₂ s₀ u = x)
    {S₀ : E₀ →L[ℂ] E₁} (hS₀ : ∀ x, d₁ s₀ (S₀ (d₁ s₀ x)) = d₁ s₀ x) :
    ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ (stepInvFam d₂ R₂ d₁ s₀ S₀) s ∧
      (∀ x, d₁ s x = 0 → ∃ u, d₂ s u = x) ∧
      ∀ x, d₁ s (stepInvFam d₂ R₂ d₁ s₀ S₀ s (d₁ s x)) = d₁ s x := by
  have hP : ContinuousAt (projFam d₂ R₂) s₀ :=
    (hd₂.self_of_nhds.clm_comp hR₂'.self_of_nhds).continuousAt
  filter_upwards [eventually_step hd₁.self_of_nhds.continuousAt hP hR₂ hcomp hex hS₀, hd₁, hd₂,
    hR₂'] with s hs h1 h2 h3
  exact ⟨differentiableAt_stepInvFam h1 h2 h3 hs.1, hs.2⟩

end Family

end
end Hironaka.HironakaG10FlatComplexPersistence
