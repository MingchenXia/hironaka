/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupSpaceTangent
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The blowup along a smooth centre as a set, and its charts

Source: Demailly, *Complex analytic and differential geometry*, VII.12.1--12.2 (`agbook.tex` lines 20218--20306).

Second module of the construction of the blowup. Demailly's blowup of `X` along `C` is, as a set, `(X \ C) ⊔ P(NC)`.
Here a point is a pair `(x, L)` with `L ⊆ ℂⁿ = T_xX` a subspace: `L = 0` when `x ∉ C`, and `L = T_xC + ℂξ` with `ξ ∉
T_xC` when `x ∈ C` (`BlowupSpace`). For a function `f` and a point `p = (x, L)`, `extVal f p` is `f x` off `C` and
`d_xf(ξ_p)` on `C`, for a chosen generator `ξ_p` of `L` modulo `T_xC`; Demailly's extension `(f/g)~` is the quotient
`extVal f / extVal g`.

* `FlatChart`: a flattening chart `(y₀, k, Φ)` of `C` together with a normal index `j ≥ k`;
* `flatChart c`: Demailly's chart `τ̃ⱼ` as a `PartialEquiv` from its domain
  `{p | π p ∈ flatDomain Φ, extVal τⱼ p ≠ 0}` onto `σⱼ⁻¹(Φ.target)` (`σⱼ = monomial k j`), with
  `monomial_flatChart` (`σⱼ ∘ τ̃ⱼ = Φ ∘ e₀ ∘ π`) and `blowupProj_flatChart_symm`
  (`π ∘ τ̃ⱼ⁻¹ = e₀⁻¹ ∘ Φ⁻¹ ∘ σⱼ`);
* `offChart x₀`: for `x₀ ∉ C`, the chart of `X` at `x₀` restricted to `X \ C`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupConstruction

open Hironaka.HolomorphicIdealSheaves BlowupFlatCoordinates BlowupMonomialCharts BlowupSpaceTangent

noncomputable section

open scoped Classical

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {C : Set X}

/-! ### The point set -/

variable (n) in
/-- `(x, L)` is a point of the blowup: `L = 0` off `C`, and `L` is a line modulo `T_xC` on `C`. -/
def IsBlowupPoint (C : Set X) (x : X) (L : Submodule ℂ (ComplexModel n)) : Prop :=
  (x ∉ C ∧ L = ⊥) ∨ (x ∈ C ∧ ∃ ξ, ξ ∉ tangentSpace n C x ∧ L = tangentSpace n C x ⊔ ℂ ∙ ξ)

variable (n) in
/-- **The blowup of `X` along `C`, as a set** (Demailly VII.12.1). -/
def BlowupSpace (C : Set X) : Type u :=
  {p : X × Submodule ℂ (ComplexModel n) // IsBlowupPoint n C p.1 p.2}

namespace BlowupSpace

/-- The base point `π(p)`. -/
def base (p : BlowupSpace n C) : X := p.1.1

/-- The subspace `L` of `p = (x, L)`. -/
def dir (p : BlowupSpace n C) : Submodule ℂ (ComplexModel n) := p.1.2

theorem ext {p q : BlowupSpace n C} (h₁ : p.base = q.base) (h₂ : p.dir = q.dir) : p = q :=
  Subtype.ext (Prod.ext h₁ h₂)

theorem isBlowupPoint (p : BlowupSpace n C) : IsBlowupPoint n C p.base p.dir := p.2

theorem dir_eq_bot {p : BlowupSpace n C} (h : p.base ∉ C) : p.dir = ⊥ :=
  (p.isBlowupPoint.resolve_right fun h' => h h'.1).2

theorem exists_dir {p : BlowupSpace n C} (h : p.base ∈ C) :
    ∃ ξ, ξ ∉ tangentSpace n C p.base ∧ p.dir = tangentSpace n C p.base ⊔ ℂ ∙ ξ :=
  (p.isBlowupPoint.resolve_left fun h' => h'.1 h).2

/-- A chosen generator of `L` modulo `T_xC` (zero off `C`). -/
def dirVec (p : BlowupSpace n C) : ComplexModel n :=
  if h : p.base ∈ C then Classical.choose (exists_dir h) else 0

theorem dirVec_not_mem {p : BlowupSpace n C} (h : p.base ∈ C) :
    p.dirVec ∉ tangentSpace n C p.base := by
  rw [dirVec, dif_pos h]; exact (Classical.choose_spec (exists_dir h)).1

theorem dir_eq_sup_dirVec {p : BlowupSpace n C} (h : p.base ∈ C) :
    p.dir = tangentSpace n C p.base ⊔ ℂ ∙ p.dirVec := by
  rw [dirVec, dif_pos h]; exact (Classical.choose_spec (exists_dir h)).2

end BlowupSpace

open BlowupSpace

variable (n C) in
/-- The projection `π : X̃ → X`. -/
def blowupProj (p : BlowupSpace n C) : X := p.base

/-- The point over `x ∉ C`. -/
def offPoint (x : X) (hx : x ∉ C) : BlowupSpace n C := ⟨(x, ⊥), Or.inl ⟨hx, rfl⟩⟩

/-- The point `(x, T_xC + ℂξ)` over `x ∈ C`. -/
def excPoint (x : X) (hx : x ∈ C) (ξ : ComplexModel n) (hξ : ξ ∉ tangentSpace n C x) :
    BlowupSpace n C :=
  ⟨(x, tangentSpace n C x ⊔ ℂ ∙ ξ), Or.inr ⟨hx, ξ, hξ, rfl⟩⟩

@[simp] theorem base_offPoint (x : X) (hx : x ∉ C) : (offPoint (n := n) x hx).base = x := rfl

@[simp] theorem base_excPoint (x : X) (hx : x ∈ C) (ξ : ComplexModel n)
    (hξ : ξ ∉ tangentSpace n C x) : (excPoint x hx ξ hξ).base = x := rfl

/-- Over a point off `C` there is exactly one point. -/
theorem eq_of_base_eq_of_not_mem {p q : BlowupSpace n C} (hpq : p.base = q.base)
    (h : p.base ∉ C) : p = q :=
  BlowupSpace.ext hpq ((dir_eq_bot h).trans (dir_eq_bot (hpq ▸ h)).symm)

/-! ### Extended values -/

/-- `f^♭(p)`: `f x` off `C`, and `d_xf(ξ_p)` on `C`. -/
def extVal (f : X → ℂ) (p : BlowupSpace n C) : ℂ :=
  if p.base ∈ C then germDiff n f p.base p.dirVec else f p.base

theorem extVal_of_not_mem {f : X → ℂ} {p : BlowupSpace n C} (h : p.base ∉ C) :
    extVal f p = f p.base := by rw [extVal, if_neg h]

theorem extVal_of_mem {f : X → ℂ} {p : BlowupSpace n C} (h : p.base ∈ C) :
    extVal f p = germDiff n f p.base p.dirVec := by rw [extVal, if_pos h]

/-- On `C`, the extended values of the germs of `𝓘_C` are, up to one common nonzero factor, the
differentials along any generator of `L` modulo `T_xC`. -/
theorem exists_extVal_eq_mul {p : BlowupSpace n C} (h : p.base ∈ C) {ξ : ComplexModel n}
    (hL : p.dir = tangentSpace n C p.base ⊔ ℂ ∙ ξ) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ f, (vanishingIdeal (n := n) C).mem p.base f →
      extVal f p = a * germDiff n f p.base ξ := by
  obtain ⟨a, ha, hmem⟩ := exists_sub_smul_mem_of_sup_span_eq (dirVec_not_mem h)
    ((dir_eq_sup_dirVec h).symm.trans hL)
  exact ⟨a, ha, fun f hf => by rw [extVal_of_mem h]; exact germDiff_apply_of_sub_smul_mem hf hmem⟩

theorem exists_extVal_excPoint_eq_mul {x : X} (hx : x ∈ C) {ξ : ComplexModel n}
    (hξ : ξ ∉ tangentSpace n C x) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ f, (vanishingIdeal (n := n) C).mem x f →
      extVal f (excPoint x hx ξ hξ) = a * germDiff n f x ξ :=
  exists_extVal_eq_mul (p := excPoint x hx ξ hξ) hx rfl

/-! ### Flattening charts -/

variable (n C) in
/-- A flattening chart of `C` at `y₀` (in the preferred chart `e₀` at `y₀`, `Φ` maps `C` onto
`ℂᵏ × 0`), together with a normal index `j ≥ k`. -/
structure FlatChart where
  y₀ : X
  k : ℕ
  Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)
  hsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target
  hflat : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) y₀).source →
    chartAt (ComplexModel n) y₀ x ∈ Φ.source →
      (x ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ x) ∈ complexCoordinatePlane n k)
  j : Fin n
  hj : k ≤ j.1

namespace FlatChart

variable (c : FlatChart n C)

/-- The flat coordinates `τᵢ = (Φ ∘ e₀)ᵢ`. -/
abbrev τ (i : Fin n) : X → ℂ := flatCoord c.Φ i

/-- The flat domain. -/
abbrev dom : Set X := flatDomain c.Φ

theorem τ_eq_zero {x : X} (hx : x ∈ c.dom) (hxC : x ∈ C) {i : Fin n} (hi : c.k ≤ i.1) :
    c.τ i x = 0 :=
  flatCoord_eq_zero c.hsrc c.hflat hx hxC hi

theorem τ_mem_vanishingIdeal {x : X} (hx : x ∈ c.dom) {i : Fin n} (hi : c.k ≤ i.1) :
    (vanishingIdeal (n := n) C).mem x (c.τ i) :=
  flatCoord_mem_vanishingIdeal c.Φ c.hflat hi hx

/-- The point of `X` over `w` in the `j`-th monomial chart: `e₀⁻¹ (Φ⁻¹ (σⱼ w))`. -/
def pt (w : ComplexModel n) : X :=
  (chartAt (ComplexModel n) c.y₀).symm (c.Φ.invFun (monomial c.k c.j w))

/-- The target `σⱼ⁻¹(Φ.target)`. -/
def target : Set (ComplexModel n) := monomial c.k c.j ⁻¹' c.Φ.target

theorem isOpen_target : IsOpen c.target :=
  c.Φ.isOpen_target.preimage (contDiff_monomial c.k c.j).continuous

theorem pt_mem_dom {w : ComplexModel n} (hw : w ∈ c.target) : c.pt w ∈ c.dom :=
  (flatInverse_mem c.Φ hw c.hsrc).1

theorem flat_pt {w : ComplexModel n} (hw : w ∈ c.target) :
    c.Φ.toFun (chartAt (ComplexModel n) c.y₀ (c.pt w)) = monomial c.k c.j w :=
  (flatInverse_mem c.Φ hw c.hsrc).2

theorem τ_pt {w : ComplexModel n} (hw : w ∈ c.target) (i : Fin n) :
    c.τ i (c.pt w) = monomial c.k c.j w i := by
  simp only [τ, flatCoord, c.flat_pt hw]

theorem pt_mem_iff {w : ComplexModel n} (hw : w ∈ c.target) : c.pt w ∈ C ↔ w c.j = 0 := by
  rw [c.hflat (c.pt_mem_dom hw).1 (c.pt_mem_dom hw).2, c.flat_pt hw]
  constructor
  · intro h
    simpa [monomial_apply] using h c.j c.hj
  · intro h i hi
    rw [monomial_apply]
    split_ifs with h'
    · rw [h, mul_zero]
    · have : i = c.j := by
        by_contra hne; exact h' ⟨hi, hne⟩
      rw [this, h]

/-- The normal vector `v` of the inverse chart: `v_j = 1`, `vᵢ = wᵢ` for normal `i ≠ j`, `0` on
the tangential coordinates. -/
def normalVec (w : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 fun i => if i = c.j then 1 else if c.k ≤ i.1 then w i else 0

theorem normalVec_j (w : ComplexModel n) : c.normalVec w c.j = 1 := by simp [normalVec]

/-- A point of the blowup used as a junk value off the target. -/
def junk : BlowupSpace n C :=
  if h : c.y₀ ∈ C then
    excPoint c.y₀ h (flatVec c.Φ c.y₀ (c.normalVec 0))
      (flatVec_not_mem_tangentSpace c.hsrc c.hflat (mem_flatDomain_self c.Φ) h c.hj
        (by rw [normalVec_j]; exact one_ne_zero))
  else offPoint c.y₀ h

/-- The inverse of the `j`-th monomial chart. -/
def invFun (w : ComplexModel n) : BlowupSpace n C :=
  if hx : c.pt w ∈ C then
    if hξ : flatVec c.Φ (c.pt w) (c.normalVec w) ∈ tangentSpace n C (c.pt w) then c.junk
    else excPoint (c.pt w) hx _ hξ
  else offPoint (c.pt w) hx

/-- Demailly's chart `τ̃ⱼ`. -/
def toFun (p : BlowupSpace n C) : ComplexModel n :=
  WithLp.toLp 2 fun i =>
    if c.k ≤ i.1 ∧ i ≠ c.j then extVal (c.τ i) p / extVal (c.τ c.j) p else c.τ i p.base

/-- The domain of `τ̃ⱼ`. -/
def source : Set (BlowupSpace n C) := {p | p.base ∈ c.dom ∧ extVal (c.τ c.j) p ≠ 0}

theorem invFun_of_ne {w : ComplexModel n} (hw : w ∈ c.target) (hj : w c.j ≠ 0) :
    c.invFun w = offPoint (c.pt w) (fun h => hj ((c.pt_mem_iff hw).mp h)) := by
  rw [invFun, dif_neg]

theorem flatVec_normalVec_not_mem {w : ComplexModel n} (hw : w ∈ c.target) (hj : w c.j = 0) :
    flatVec c.Φ (c.pt w) (c.normalVec w) ∉ tangentSpace n C (c.pt w) :=
  flatVec_not_mem_tangentSpace c.hsrc c.hflat (c.pt_mem_dom hw) ((c.pt_mem_iff hw).mpr hj) c.hj
    (by rw [normalVec_j]; exact one_ne_zero)

theorem invFun_of_eq {w : ComplexModel n} (hw : w ∈ c.target) (hj : w c.j = 0) :
    c.invFun w = excPoint (c.pt w) ((c.pt_mem_iff hw).mpr hj) _ (c.flatVec_normalVec_not_mem hw hj) := by
  rw [invFun, dif_pos ((c.pt_mem_iff hw).mpr hj), dif_neg (c.flatVec_normalVec_not_mem hw hj)]

theorem base_invFun {w : ComplexModel n} (hw : w ∈ c.target) : (c.invFun w).base = c.pt w := by
  by_cases hj : w c.j = 0
  · rw [c.invFun_of_eq hw hj]; rfl
  · rw [c.invFun_of_ne hw hj]; rfl

/-- `σⱼ ∘ τ̃ⱼ = Φ ∘ e₀ ∘ π` on the domain of the chart. -/
theorem monomial_toFun {p : BlowupSpace n C} (hp : p ∈ c.source) :
    monomial c.k c.j (c.toFun p) = c.Φ.toFun (chartAt (ComplexModel n) c.y₀ p.base) := by
  ext i
  rw [monomial_apply]
  have hτ : ∀ l, c.τ l p.base = c.Φ.toFun (chartAt (ComplexModel n) c.y₀ p.base) l := fun _ => rfl
  by_cases hi : c.k ≤ i.1 ∧ i ≠ c.j
  · rw [if_pos hi]
    simp only [toFun, if_pos hi, PiLp.toLp_apply]
    have hjj : ¬ (c.k ≤ c.j.1 ∧ c.j ≠ c.j) := fun h => h.2 rfl
    rw [if_neg hjj]
    by_cases hC : p.base ∈ C
    · rw [c.τ_eq_zero hp.1 hC c.hj, mul_zero, ← hτ, c.τ_eq_zero hp.1 hC hi.1]
    · have hne : extVal (c.τ c.j) p ≠ 0 := hp.2
      rw [extVal_of_not_mem hC] at hne
      rw [extVal_of_not_mem hC, extVal_of_not_mem hC, div_mul_cancel₀ _ hne, ← hτ]
  · rw [if_neg hi]
    simp only [toFun, if_neg hi, PiLp.toLp_apply]
    rfl

theorem eq_excPoint {p : BlowupSpace n C} {x : X} (hx : x ∈ C) {ξ : ComplexModel n}
    (hξ : ξ ∉ tangentSpace n C x) (hb : p.base = x) (hd : p.dir = tangentSpace n C x ⊔ ℂ ∙ ξ) :
    excPoint x hx ξ hξ = p :=
  BlowupSpace.ext hb.symm hd.symm

theorem toFun_apply_j (p : BlowupSpace n C) : c.toFun p c.j = c.τ c.j p.base := by
  have hjj : ¬ (c.k ≤ c.j.1 ∧ c.j ≠ c.j) := fun h => h.2 rfl
  simp only [toFun, PiLp.toLp_apply, if_neg hjj]

theorem toFun_apply_normal (p : BlowupSpace n C) {i : Fin n} (hi : c.k ≤ i.1) (hij : i ≠ c.j) :
    c.toFun p i = extVal (c.τ i) p / extVal (c.τ c.j) p := by
  simp only [toFun, PiLp.toLp_apply, if_pos (And.intro hi hij)]

theorem toFun_apply_of_not (p : BlowupSpace n C) {i : Fin n} (hi : ¬ (c.k ≤ i.1 ∧ i ≠ c.j)) :
    c.toFun p i = c.τ i p.base := by
  simp only [toFun, PiLp.toLp_apply, if_neg hi]

theorem map_source {p : BlowupSpace n C} (hp : p ∈ c.source) : c.toFun p ∈ c.target := by
  show monomial c.k c.j (c.toFun p) ∈ c.Φ.target
  rw [c.monomial_toFun hp]
  exact c.Φ.mapsTo_toFun hp.1.2

theorem pt_toFun {p : BlowupSpace n C} (hp : p ∈ c.source) : c.pt (c.toFun p) = p.base := by
  rw [pt, c.monomial_toFun hp]
  exact flatInverse_flat c.Φ hp.1

theorem toFun_j_eq_zero_iff {p : BlowupSpace n C} (hp : p ∈ c.source) :
    c.toFun p c.j = 0 ↔ p.base ∈ C := by
  rw [c.toFun_apply_j]
  constructor
  · intro h
    by_contra hC
    exact hp.2 (by rw [extVal_of_not_mem hC]; exact h)
  · intro hC
    exact c.τ_eq_zero hp.1 hC c.hj

theorem monomial_apply_of_not {w : ComplexModel n} {i : Fin n} (hi : ¬ (c.k ≤ i.1 ∧ i ≠ c.j)) :
    monomial c.k c.j w i = w i := by
  rw [monomial_apply, if_neg hi]

theorem map_target {w : ComplexModel n} (hw : w ∈ c.target) : c.invFun w ∈ c.source := by
  refine ⟨by rw [c.base_invFun hw]; exact c.pt_mem_dom hw, ?_⟩
  by_cases hj : w c.j = 0
  · have hx := (c.pt_mem_iff hw).mpr hj
    obtain ⟨a, ha, hext⟩ := exists_extVal_excPoint_eq_mul (C := C) hx
      (c.flatVec_normalVec_not_mem hw hj)
    rw [c.invFun_of_eq hw hj, hext _ (c.τ_mem_vanishingIdeal (c.pt_mem_dom hw) c.hj),
      germDiff_flatCoord_flatVec c.hsrc (c.pt_mem_dom hw), normalVec_j, mul_one]
    exact ha
  · have hx : c.pt w ∉ C := fun h => hj ((c.pt_mem_iff hw).mp h)
    rw [c.invFun_of_ne hw hj, extVal_of_not_mem hx]
    show c.τ c.j (c.pt w) ≠ 0
    rw [c.τ_pt hw, c.monomial_apply_of_not (fun h => h.2 rfl)]
    exact hj

theorem left_inv {p : BlowupSpace n C} (hp : p ∈ c.source) : c.invFun (c.toFun p) = p := by
  have hw := c.map_source hp
  have hpt := c.pt_toFun hp
  by_cases hC : p.base ∈ C
  · have hj : c.toFun p c.j = 0 := (c.toFun_j_eq_zero_iff hp).mpr hC
    rw [c.invFun_of_eq hw hj]
    refine eq_excPoint _ _ hpt.symm ?_
    rw [dir_eq_sup_dirVec hC]
    have ha : extVal (c.τ c.j) p ≠ 0 := hp.2
    rw [extVal_of_mem hC] at ha
    have hmem : p.dirVec - germDiff n (c.τ c.j) p.base p.dirVec •
        flatVec c.Φ (c.pt (c.toFun p)) (c.normalVec (c.toFun p)) ∈ tangentSpace n C p.base := by
      rw [mem_tangentSpace_iff c.hsrc c.hflat hp.1 hC]
      intro i hi
      rw [map_sub, map_smul, hpt, germDiff_flatCoord_flatVec c.hsrc hp.1, smul_eq_mul]
      simp only [normalVec, PiLp.toLp_apply]
      by_cases hij : i = c.j
      · subst hij; simp
      · rw [if_neg hij, if_pos hi, c.toFun_apply_normal p hi hij, extVal_of_mem hC,
          extVal_of_mem hC]
        field_simp
        ring
    rw [hpt] at hmem ⊢
    exact sup_span_eq_of_sub_smul_mem ha hmem
  · have hj : c.toFun p c.j ≠ 0 := fun h => hC ((c.toFun_j_eq_zero_iff hp).mp h)
    rw [c.invFun_of_ne hw hj]
    exact eq_of_base_eq_of_not_mem hpt (by rw [base_offPoint, hpt]; exact hC)

theorem right_inv {w : ComplexModel n} (hw : w ∈ c.target) : c.toFun (c.invFun w) = w := by
  ext i
  by_cases hi : c.k ≤ i.1 ∧ i ≠ c.j
  · rw [c.toFun_apply_normal _ hi.1 hi.2]
    by_cases hj : w c.j = 0
    · have hx := (c.pt_mem_iff hw).mpr hj
      obtain ⟨a, ha, hext⟩ := exists_extVal_excPoint_eq_mul (C := C) hx
        (c.flatVec_normalVec_not_mem hw hj)
      rw [c.invFun_of_eq hw hj, hext _ (c.τ_mem_vanishingIdeal (c.pt_mem_dom hw) hi.1),
        hext _ (c.τ_mem_vanishingIdeal (c.pt_mem_dom hw) c.hj),
        germDiff_flatCoord_flatVec c.hsrc (c.pt_mem_dom hw),
        germDiff_flatCoord_flatVec c.hsrc (c.pt_mem_dom hw), normalVec_j]
      simp only [normalVec, PiLp.toLp_apply, if_neg hi.2, if_pos hi.1]
      field_simp
    · have hx : c.pt w ∉ C := fun h => hj ((c.pt_mem_iff hw).mp h)
      rw [c.invFun_of_ne hw hj, extVal_of_not_mem hx, extVal_of_not_mem hx]
      show c.τ i (c.pt w) / c.τ c.j (c.pt w) = w i
      rw [c.τ_pt hw, c.τ_pt hw, c.monomial_apply_of_not (fun h => h.2 rfl), monomial_apply,
        if_pos hi]
      field_simp
  · rw [c.toFun_apply_of_not _ hi, c.base_invFun hw, c.τ_pt hw, c.monomial_apply_of_not hi]

/-- **Demailly's chart `τ̃ⱼ`** as a partial equivalence. -/
def toPartialEquiv : PartialEquiv (BlowupSpace n C) (ComplexModel n) where
  toFun := c.toFun
  invFun := c.invFun
  source := c.source
  target := c.target
  map_source' _ hp := c.map_source hp
  map_target' _ hw := c.map_target hw
  left_inv' _ hp := c.left_inv hp
  right_inv' _ hw := c.right_inv hw

/-- `π ∘ τ̃ⱼ⁻¹ = e₀⁻¹ ∘ Φ⁻¹ ∘ σⱼ` on the target. -/
theorem blowupProj_invFun {w : ComplexModel n} (hw : w ∈ c.target) :
    blowupProj n C (c.invFun w) = c.pt w :=
  c.base_invFun hw

end FlatChart

/-! ### Charts off the centre -/

/-- A chart of `X` at a point off `C`, used on `X \ C` (`n` is the dimension of the model). -/
structure OffChart (n : ℕ) (C : Set X) : Type u where
  x₀ : X
  hx₀ : x₀ ∉ C

namespace OffChart

variable (o : OffChart n C)

/-- The chart `e` of `X` at `x₀`. -/
abbrev e : OpenPartialHomeomorph X (ComplexModel n) := chartAt (ComplexModel n) o.x₀

/-- The chart `p ↦ e (π p)` on `π⁻¹(e.source \ C)`. -/
def toPartialEquiv : PartialEquiv (BlowupSpace n C) (ComplexModel n) where
  toFun p := o.e p.base
  invFun z := if h : o.e.symm z ∈ C then offPoint o.x₀ o.hx₀ else offPoint (o.e.symm z) h
  source := {p | p.base ∈ o.e.source ∧ p.base ∉ C}
  target := o.e.target ∩ o.e.symm ⁻¹' Cᶜ
  map_source' p hp := ⟨o.e.map_source hp.1, by
    show o.e.symm (o.e p.base) ∉ C
    rw [o.e.left_inv hp.1]; exact hp.2⟩
  map_target' z hz := by
    have h : o.e.symm z ∉ C := hz.2
    simp only [dif_neg h]
    exact ⟨o.e.map_target hz.1, h⟩
  left_inv' p hp := by
    have h : o.e.symm (o.e p.base) ∉ C := by rw [o.e.left_inv hp.1]; exact hp.2
    simp only [dif_neg h]
    exact eq_of_base_eq_of_not_mem (o.e.left_inv hp.1) (by rw [base_offPoint, o.e.left_inv hp.1]; exact hp.2)
  right_inv' z hz := by
    have h : o.e.symm z ∉ C := hz.2
    simp only [dif_neg h, base_offPoint]
    exact o.e.right_inv hz.1

theorem source_eq : o.toPartialEquiv.source = {p | p.base ∈ o.e.source ∧ p.base ∉ C} := rfl

theorem target_eq : o.toPartialEquiv.target = o.e.target ∩ o.e.symm ⁻¹' Cᶜ := rfl

theorem apply_eq (p : BlowupSpace n C) : o.toPartialEquiv p = o.e p.base := rfl

theorem symm_apply_of_not_mem {z : ComplexModel n} (h : o.e.symm z ∉ C) :
    o.toPartialEquiv.symm z = offPoint (o.e.symm z) h := by
  show (if h : o.e.symm z ∈ C then offPoint o.x₀ o.hx₀ else offPoint (o.e.symm z) h) = _
  rw [dif_neg h]

end OffChart

end

end Hironaka.BlowupConstruction
