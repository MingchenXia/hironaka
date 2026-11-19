import Hironaka.Analytic.FormPullbackFunctorial

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `(f ∘ g)^* a = g^* (f^* a)` between manifolds of different dimensions

Source: standard (pullback of differential forms is functorial); needed for Copy-4,
`prop:principalization`, Step 4
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1880-1906`):
`φ' = (π|_W)^* φ_{K,ℓ} + τ ψ_{E_rel}|_W` is a potential for `(π^*θ - ½δ₀ π^*ω)|_W` on the strict
transform `W`, while `φ_{K,ℓ}` is a potential on `V` for `θ|_V - δ₀ ω|_V`.  Comparing the two forms
on `W` is `(π|_W)^* (ι_V^* a) = ι_W^* (π^* a)`, a functoriality statement for maps
`W → V → X` and `W → Y → X` between manifolds of DIFFERENT dimensions.

`Hironaka.SmoothRealForm.pullback_comp_geometricallyEq` (human-only `FirstPass/`) states the law
for three manifolds of the same dimension.  Its proof does not use the equality of dimensions; this
module repeats it with the three dimensions independent:

* `pullback_comp_geometricallyEq` — `(f ∘ g)^* a = g^* (f^* a)` geometrically, `Z → Y → X` of
  dimensions `j`, `k`, `n`;
* `pullback_pullback_geometricallyEq_of_comp_eq` — if `f₁ ∘ g₁ = f₂ ∘ g₂` then
  `g₁^* (f₁^* a) = g₂^* (f₂^* a)` geometrically (the commutative square `W → V → X`,
  `W → Y → X`).

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.FormPullbackCompMixed

open Hironaka.HolomorphicMaps

noncomputable section

variable {p j k n : ℕ}
  {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel j) Z] [IsComplexManifold j Z]

/-- **`(f ∘ g)^* a = g^* (f^* a)` geometrically**, for `g : Z → Y`, `f : Y → X` holomorphic
between manifolds of dimensions `j`, `k`, `n`.  Same proof as
`Hironaka.SmoothRealForm.pullback_comp_geometricallyEq`: the chain rule for the coordinate
representatives, and the intermediate chart chosen by `g^*` is the preferred chart at `g x`,
where `f^* a` reads its coefficients. -/
theorem pullback_comp_geometricallyEq {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel j) 𝓘(ℂ, ComplexModel k) ∞ g)
    (a : SmoothRealForm n X p) :
    (SmoothRealForm.pullback (hf.comp hg) a).GeometricallyEq
      (SmoothRealForm.pullback hg (SmoothRealForm.pullback hf a)) := by
  intro e z hz
  set x : Z := e.val.symm z with hx
  set d₂ := complexChartAt (n := k) (g x) with hd₂
  set d₁ := complexChartAt (n := n) (f (g x)) with hd₁
  have hgx : g x ∈ d₂.val.source := mem_complexChartAt_source _
  have hfgx : f (g x) ∈ d₁.val.source := mem_complexChartAt_source _
  set w : ComplexModel k := coordinateMap g e d₂ z with hw
  have hwx : d₂.val.symm w = g x := by
    rw [hw]
    exact d₂.val.left_inv hgx
  have hzdom : z ∈ coordinateDomain g e d₂ := ⟨hz, by
    simpa only [mem_preimage, ← hx] using hgx⟩
  have hwdom : w ∈ coordinateDomain f d₂ d₁ :=
    ⟨d₂.val.map_source hgx, by simpa only [mem_preimage, hwx] using hfgx⟩
  have heq : coordinateMap (f ∘ g) e d₁ =ᶠ[𝓝 z]
      (coordinateMap f d₂ d₁) ∘ (coordinateMap g e d₂) := by
    filter_upwards [(coordinateDomain_isOpen hg e d₂).mem_nhds hzdom] with y hy
    show d₁.val (f (g (e.val.symm y))) =
      d₁.val (f (d₂.val.symm (d₂.val (g (e.val.symm y)))))
    rw [d₂.val.left_inv hy.2]
  have hchain : fderiv ℝ (coordinateMap (f ∘ g) e d₁) z =
      (fderiv ℝ (coordinateMap f d₂ d₁) w).comp
        (fderiv ℝ (coordinateMap g e d₂) z) := by
    rw [heq.fderiv_eq]
    exact fderiv_comp z
      ((coordinateMap_contDiffAt_real hf d₂ d₁ hwdom).differentiableAt (by simp))
      ((coordinateMap_contDiffAt_real hg e d₂ hzdom).differentiableAt (by simp))
  have hpoint : coordinateMap f d₂ d₁ w = coordinateMap (f ∘ g) e d₁ z := by
    show d₁.val (f (d₂.val.symm w)) = d₁.val (f (g (e.val.symm z)))
    rw [hwx]
  ext v
  show (a.coeff d₁ (coordinateMap (f ∘ g) e d₁ z))
      (fun i => fderiv ℝ (coordinateMap (f ∘ g) e d₁) z (v i)) = _
  rw [hchain]
  show _ = ((SmoothRealForm.pullback hf a).coeff d₂ w)
      (fun i => fderiv ℝ (coordinateMap g e d₂) z (v i))
  have hinner : (SmoothRealForm.pullback hf a).coeff d₂ w =
      (a.coeff d₁ (coordinateMap f d₂ d₁ w)).compContinuousLinearMap
        (fderiv ℝ (coordinateMap f d₂ d₁) w) := by
    show SmoothRealForm.chartPullbackCoeff a f d₂
      (complexChartAt (n := n) (f (d₂.val.symm w))) w = _
    rw [hwx, ← hd₁]
    rfl
  rw [hinner, hpoint]
  rfl

/-- The pullback only depends on the map. -/
theorem pullback_congr {F G : Z → X} (hF : ContMDiff 𝓘(ℂ, ComplexModel j) 𝓘(ℂ, ComplexModel n) ∞ F)
    (hG : ContMDiff 𝓘(ℂ, ComplexModel j) 𝓘(ℂ, ComplexModel n) ∞ G) (h : F = G)
    (a : SmoothRealForm n X p) :
    SmoothRealForm.pullback hF a = SmoothRealForm.pullback hG a := by
  subst h
  rfl

variable {k' : ℕ} {Y'' : Type*} [TopologicalSpace Y'']
  [ChartedSpace (ComplexModel k') Y''] [IsComplexManifold k' Y'']

/-- **A commutative square pulls back consistently**: if `f₁ ∘ g₁ = f₂ ∘ g₂ : Z → X` with
`g₁ : Z → Y`, `f₁ : Y → X`, `g₂ : Z → Y''`, `f₂ : Y'' → X` holomorphic, then
`g₁^* (f₁^* a) = g₂^* (f₂^* a)` geometrically.  For Copy-4 Step 4: `Z = W`, `Y = V`,
`Y'' = Y`, `g₁ = π|_W`, `f₁ = ι_V`, `g₂ = ι_W`, `f₂ = π`. -/
theorem pullback_pullback_geometricallyEq_of_comp_eq {f₁ : Y → X} {g₁ : Z → Y}
    {f₂ : Y'' → X} {g₂ : Z → Y''}
    (hf₁ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f₁)
    (hg₁ : ContMDiff 𝓘(ℂ, ComplexModel j) 𝓘(ℂ, ComplexModel k) ∞ g₁)
    (hf₂ : ContMDiff 𝓘(ℂ, ComplexModel k') 𝓘(ℂ, ComplexModel n) ∞ f₂)
    (hg₂ : ContMDiff 𝓘(ℂ, ComplexModel j) 𝓘(ℂ, ComplexModel k') ∞ g₂)
    (hcomm : f₁ ∘ g₁ = f₂ ∘ g₂) (a : SmoothRealForm n X p) :
    (SmoothRealForm.pullback hg₁ (SmoothRealForm.pullback hf₁ a)).GeometricallyEq
      (SmoothRealForm.pullback hg₂ (SmoothRealForm.pullback hf₂ a)) := by
  have h1 := (pullback_comp_geometricallyEq hf₁ hg₁ a).symm
  have h2 := pullback_comp_geometricallyEq hf₂ hg₂ a
  rw [pullback_congr (hf₁.comp hg₁) (hf₂.comp hg₂) hcomm a] at h1
  exact h1.trans h2

end

end Hironaka.FormPullbackCompMixed
