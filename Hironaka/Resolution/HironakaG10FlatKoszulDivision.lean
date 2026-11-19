import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Direct exactness of the Koszul complex of a divisor (Douady 1966, §7 Prop. 5 Cor., Banach core)

Abstract Banach-space form of the step "a sheaf killed by a Weierstrass polynomial `W` (e.g. a
coordinate `ζ = w − a`) and pulled back from the base is privileged as soon as its restriction to
the base is" (Douady 1966, §7 n° 2, Corollaire de la Proposition 5).

A **division datum** `DivData E F` on a Banach space `E` (think `E = B(K' × D̄)^ι`,
`F = B(K')^{ι × b}`) consists of continuous linear maps `μ : E → E` (multiplication by `W`),
`rem : E → F`, `sec : F → E`, `quot : E → E` with `rem ∘ sec = id`, `rem ∘ μ = 0`, `quot ∘ μ = id`
and `x = μ (quot x) + sec (rem x)` (`HironakaG10FlatPolydiscPushforward`: `remVec`, `polyVec`).
A map `f : E → E'` is **compatible** with `f' : F → F'` (`DivHom`) if it commutes with `μ`,
`rem` and `sec` (pulled-back matrices).

For a complex `E₂ →g E₁ →f E₀` of compatible maps with remainder complex `F₂ →g' F₁ →f' F₀`, the
Koszul total complex of `μ` is

`E₂ × E₁ --d₂--> E₁ × E₀ --d₁--> E₀`, `d₂ (u, v) = (g u − μ v, f v)`, `d₁ (x, y) = f x + μ y`.

* `koszulD₁_koszulD₂`: `d₁ ∘ d₂ = 0`;
* `exists_koszulD₂_eq` (**exactness**): if `F₂ → F₁ → F₀` is exact at `F₁`, the Koszul complex is
  exact at `E₁ × E₀`;
* `mem_range_koszulD₁_iff`: `u ∈ im d₁ ↔ rem u ∈ im f'`; hence `isClosed_range_koszulD₁` and
  `closedComplemented_range_koszulD₁` from the same properties of `im f'`;
* `closedComplemented_ker_koszulD₁`: `ker d₁` is complemented if `ker f'` is;
* `closedComplemented_ker_koszulD₂`: `ker d₂` is complemented if `ker g'` is.

So the start of resolution `(d₂, d₁)` is exact and direct whenever `(g', f')` is: privilege passes
from the base to the hypersurface `W = 0`. BP: hironaka-g10-flat-koszul-division.tex. -/
set_option autoImplicit false
namespace Hironaka.HironakaG10FlatKoszulDivision
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- A division datum: `E = μ E ⊕ sec F` with remainder `rem` and quotient `quot`. -/
structure DivData (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] where
  μ : E →L[ℂ] E
  rem : E →L[ℂ] F
  sec : F →L[ℂ] E
  quot : E →L[ℂ] E
  rem_sec : ∀ r, rem (sec r) = r
  rem_μ : ∀ x, rem (μ x) = 0
  quot_μ : ∀ x, quot (μ x) = x
  decomp : ∀ x, x = μ (quot x) + sec (rem x)

namespace DivData
variable (D : DivData E F)

theorem μ_injective : Function.Injective D.μ := fun x y h => by
  rw [← D.quot_μ x, h, D.quot_μ]

theorem quot_sec (r : F) : D.quot (D.sec r) = 0 := by
  have h := D.decomp (D.sec r)
  rw [D.rem_sec] at h
  have h0 : D.μ (D.quot (D.sec r)) = 0 := by
    have := congrArg (· - D.sec r) h
    simpa using this.symm
  rw [← D.quot_μ (D.quot (D.sec r)), h0, map_zero]

theorem eq_μ_of_rem_eq_zero {x : E} (hx : D.rem x = 0) : x = D.μ (D.quot x) := by
  conv_lhs => rw [D.decomp x, hx, map_zero, add_zero]

end DivData

variable {E₂ E₁ E₀ F₂ F₁ F₀ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [NormedAddCommGroup F₀] [NormedSpace ℂ F₀]

/-- `f : E → E'` is compatible with `f' : F → F'`: it commutes with `μ`, `rem` and `sec`. -/
structure DivHom (D : DivData E₁ F₁) (D' : DivData E₀ F₀) (f : E₁ →L[ℂ] E₀) (f' : F₁ →L[ℂ] F₀) :
    Prop where
  comm_μ : ∀ x, f (D.μ x) = D'.μ (f x)
  comm_rem : ∀ x, D'.rem (f x) = f' (D.rem x)
  comm_sec : ∀ r, f (D.sec r) = D'.sec (f' r)

/-- The first Koszul differential `d₁ (x, y) = f x + μ y`. -/
def koszulD₁ (D₀ : DivData E₀ F₀) (f : E₁ →L[ℂ] E₀) : E₁ × E₀ →L[ℂ] E₀ :=
  f.coprod D₀.μ

/-- The second Koszul differential `d₂ (u, v) = (g u − μ v, f v)`. -/
def koszulD₂ (D₁ : DivData E₁ F₁) (g : E₂ →L[ℂ] E₁) (f : E₁ →L[ℂ] E₀) :
    E₂ × E₁ →L[ℂ] E₁ × E₀ :=
  (g.coprod (-D₁.μ)).prod (f.comp (ContinuousLinearMap.snd ℂ E₂ E₁))

theorem koszulD₁_apply (D₀ : DivData E₀ F₀) (f : E₁ →L[ℂ] E₀) (z : E₁ × E₀) :
    koszulD₁ D₀ f z = f z.1 + D₀.μ z.2 := rfl

theorem koszulD₂_apply (D₁ : DivData E₁ F₁) (g : E₂ →L[ℂ] E₁) (f : E₁ →L[ℂ] E₀) (z : E₂ × E₁) :
    koszulD₂ D₁ g f z = (g z.1 - D₁.μ z.2, f z.2) := by
  simp only [koszulD₂, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd']
  rw [sub_eq_add_neg]
  rfl

variable {D₂ : DivData E₂ F₂} {D₁ : DivData E₁ F₁} {D₀ : DivData E₀ F₀}
  {g : E₂ →L[ℂ] E₁} {f : E₁ →L[ℂ] E₀} {g' : F₂ →L[ℂ] F₁} {f' : F₁ →L[ℂ] F₀}

/-- `d₁ ∘ d₂ = 0`. -/
theorem koszulD₁_koszulD₂ (hf : DivHom D₁ D₀ f f') (hfg : ∀ u, f (g u) = 0) (z : E₂ × E₁) :
    koszulD₁ D₀ f (koszulD₂ D₁ g f z) = 0 := by
  rw [koszulD₂_apply, koszulD₁_apply]
  dsimp only
  rw [map_sub, hfg, hf.comm_μ]
  abel

/-- **Exactness of the Koszul complex** at `E₁ × E₀`, from exactness of the remainder complex at
`F₁`. -/
theorem exists_koszulD₂_eq (hg : DivHom D₂ D₁ g g') (hf : DivHom D₁ D₀ f f')
    (hfg : ∀ u, f (g u) = 0) (hex : ∀ r, f' r = 0 → ∃ t, g' t = r) (z : E₁ × E₀)
    (hz : koszulD₁ D₀ f z = 0) : ∃ w, koszulD₂ D₁ g f w = z := by
  obtain ⟨x, y⟩ := z
  rw [koszulD₁_apply] at hz
  dsimp only at hz
  -- the remainder of `x` is a cycle of the remainder complex
  have hrem : f' (D₁.rem x) = 0 := by
    have := congrArg D₀.rem hz
    rwa [map_add, D₀.rem_μ, add_zero, hf.comm_rem, map_zero] at this
  obtain ⟨t, ht⟩ := hex _ hrem
  -- `x = μ x' + g (sec t)`
  set x' := D₁.quot x
  have hx : x = D₁.μ x' + g (D₂.sec t) := by
    rw [hg.comm_sec, ht]
    exact D₁.decomp x
  -- `f x' + y = 0`
  have hy : f x' + y = 0 := by
    apply D₀.μ_injective
    rw [map_add, ← hf.comm_μ, map_zero, ← hz, hx, map_add, hfg]
    abel
  refine ⟨(D₂.sec t, -x'), ?_⟩
  rw [koszulD₂_apply]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [map_neg, sub_neg_eq_add, hx, add_comm]
  · dsimp only
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_right hy).symm

/-- **The image of `d₁`**: `u ∈ im d₁ ↔ rem u ∈ im f'`. -/
theorem mem_range_koszulD₁_iff (hf : DivHom D₁ D₀ f f') (u : E₀) :
    u ∈ LinearMap.range (koszulD₁ D₀ f : E₁ × E₀ →ₗ[ℂ] E₀) ↔
      D₀.rem u ∈ LinearMap.range (f' : F₁ →ₗ[ℂ] F₀) := by
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    refine ⟨D₁.rem x, ?_⟩
    show f' (D₁.rem x) = D₀.rem (f x + D₀.μ y)
    rw [map_add, D₀.rem_μ, add_zero, hf.comm_rem]
  · rintro ⟨r, hr⟩
    have hr' : f' r = D₀.rem u := hr
    have h0 : D₀.rem (u - f (D₁.sec r)) = 0 := by
      rw [map_sub, hf.comm_sec, D₀.rem_sec, hr', sub_self]
    refine ⟨(D₁.sec r, D₀.quot (u - f (D₁.sec r))), ?_⟩
    show f (D₁.sec r) + D₀.μ (D₀.quot (u - f (D₁.sec r))) = u
    rw [← D₀.eq_μ_of_rem_eq_zero h0]
    abel

/-- A continuous projection onto `S` makes `S` closed-complemented. -/
theorem closedComplemented_of_proj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Submodule ℂ E) (P : E →L[ℂ] E) (hP : ∀ x, P x ∈ S) (hPS : ∀ x ∈ S, P x = x) :
    S.ClosedComplemented :=
  ⟨P.codRestrict S hP, fun x => Subtype.ext (hPS x x.2)⟩

/-- Projection data of a closed-complemented submodule. -/
theorem exists_proj_of_closedComplemented {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Submodule ℂ E} (h : S.ClosedComplemented) :
    ∃ P : E →L[ℂ] E, (∀ x, P x ∈ S) ∧ ∀ x ∈ S, P x = x := by
  obtain ⟨p, hp⟩ := h
  exact ⟨S.subtypeL.comp p, fun x => (p x).2, fun x hx => congrArg Subtype.val (hp ⟨x, hx⟩)⟩

/-- **Closed image**: `im d₁` is closed if `im f'` is. -/
theorem isClosed_range_koszulD₁ (hf : DivHom D₁ D₀ f f')
    (h : IsClosed (LinearMap.range (f' : F₁ →ₗ[ℂ] F₀) : Set F₀)) :
    IsClosed (LinearMap.range (koszulD₁ D₀ f : E₁ × E₀ →ₗ[ℂ] E₀) : Set E₀) := by
  have : (LinearMap.range (koszulD₁ D₀ f : E₁ × E₀ →ₗ[ℂ] E₀) : Set E₀) =
      D₀.rem ⁻¹' (LinearMap.range (f' : F₁ →ₗ[ℂ] F₀) : Set F₀) :=
    Set.ext fun u => mem_range_koszulD₁_iff hf u
  rw [this]
  exact h.preimage D₀.rem.continuous

/-- **Complemented image**: `im d₁` is complemented if `im f'` is. -/
theorem closedComplemented_range_koszulD₁ (hf : DivHom D₁ D₀ f f')
    (h : (LinearMap.range (f' : F₁ →ₗ[ℂ] F₀)).ClosedComplemented) :
    (LinearMap.range (koszulD₁ D₀ f : E₁ × E₀ →ₗ[ℂ] E₀)).ClosedComplemented := by
  obtain ⟨p, hp, hpS⟩ := exists_proj_of_closedComplemented h
  -- `P u = u − sec (rem u − p (rem u))`
  refine closedComplemented_of_proj _
    (ContinuousLinearMap.id ℂ E₀ - D₀.sec.comp (D₀.rem - p.comp D₀.rem)) (fun u => ?_)
    (fun u hu => ?_)
  · rw [mem_range_koszulD₁_iff hf]
    have : D₀.rem ((ContinuousLinearMap.id ℂ E₀ - D₀.sec.comp (D₀.rem - p.comp D₀.rem)) u) =
        p (D₀.rem u) := by
      show D₀.rem (u - D₀.sec (D₀.rem u - p (D₀.rem u))) = p (D₀.rem u)
      rw [map_sub, D₀.rem_sec]
      abel
    rw [this]
    exact hp _
  · have hu' := (mem_range_koszulD₁_iff hf u).mp hu
    show u - D₀.sec (D₀.rem u - p (D₀.rem u)) = u
    rw [hpS _ hu', sub_self, map_zero, sub_zero]

/-- **Complemented kernel of `d₁`**, if `ker f'` is complemented. -/
theorem closedComplemented_ker_koszulD₁ (hf : DivHom D₁ D₀ f f')
    (h : (LinearMap.ker (f' : F₁ →ₗ[ℂ] F₀)).ClosedComplemented) :
    (LinearMap.ker (koszulD₁ D₀ f : E₁ × E₀ →ₗ[ℂ] E₀)).ClosedComplemented := by
  obtain ⟨p, hp, hpS⟩ := exists_proj_of_closedComplemented h
  -- `x̃ = x − sec (rem x − p (rem x))`, `P (x, y) = (x̃, −quot (f x̃))`
  let T : E₁ →L[ℂ] E₁ := ContinuousLinearMap.id ℂ E₁ - D₁.sec.comp (D₁.rem - p.comp D₁.rem)
  have hT : ∀ x, T x = x - D₁.sec (D₁.rem x - p (D₁.rem x)) := fun x => rfl
  have hremT : ∀ x, D₁.rem (T x) = p (D₁.rem x) := by
    intro x
    rw [hT, map_sub, D₁.rem_sec]
    abel
  have hfT : ∀ x, D₀.rem (f (T x)) = 0 := by
    intro x
    rw [hf.comm_rem, hremT]
    exact hp _
  let P : E₁ × E₀ →L[ℂ] E₁ × E₀ :=
    (T.comp (ContinuousLinearMap.fst ℂ E₁ E₀)).prod
      (-(D₀.quot.comp (f.comp (T.comp (ContinuousLinearMap.fst ℂ E₁ E₀)))))
  have hP : ∀ z : E₁ × E₀, P z = (T z.1, -D₀.quot (f (T z.1))) := fun z => rfl
  refine closedComplemented_of_proj _ P (fun z => ?_) (fun z hz => ?_)
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hP, koszulD₁_apply]
    dsimp only
    rw [map_neg, ← D₀.eq_μ_of_rem_eq_zero (hfT z.1), add_neg_cancel]
  · obtain ⟨x, y⟩ := z
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, koszulD₁_apply] at hz
    dsimp only at hz
    have hrem : D₁.rem x ∈ LinearMap.ker (f' : F₁ →ₗ[ℂ] F₀) := by
      have := congrArg D₀.rem hz
      rw [map_add, D₀.rem_μ, add_zero, hf.comm_rem, map_zero] at this
      exact this
    have hTx : T x = x := by
      rw [hT, hpS _ hrem, sub_self, map_zero, sub_zero]
    rw [hP]
    dsimp only
    rw [hTx]
    have hfx : f x = D₀.μ (-y) := by
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_left hz
    rw [hfx, D₀.quot_μ, neg_neg]

/-- **Complemented kernel of `d₂`**, if `ker g'` is complemented. -/
theorem closedComplemented_ker_koszulD₂ (hg : DivHom D₂ D₁ g g') (hfg : ∀ u, f (g u) = 0)
    (h : (LinearMap.ker (g' : F₂ →ₗ[ℂ] F₁)).ClosedComplemented) :
    (LinearMap.ker (koszulD₂ D₁ g f : E₂ × E₁ →ₗ[ℂ] E₁ × E₀)).ClosedComplemented := by
  obtain ⟨p, hp, hpS⟩ := exists_proj_of_closedComplemented h
  -- `ũ = u − sec (rem u − p (rem u))`, `P (u, v) = (ũ, g (quot u))`
  let T : E₂ →L[ℂ] E₂ := ContinuousLinearMap.id ℂ E₂ - D₂.sec.comp (D₂.rem - p.comp D₂.rem)
  have hT : ∀ u, T u = u - D₂.sec (D₂.rem u - p (D₂.rem u)) := fun u => rfl
  have hremT : ∀ u, D₂.rem (T u) = p (D₂.rem u) := by
    intro u
    rw [hT, map_sub, D₂.rem_sec]
    abel
  have hquotT : ∀ u, D₂.quot (T u) = D₂.quot u := by
    intro u
    rw [hT, map_sub, D₂.quot_sec, sub_zero]
  -- elements of `ker d₂`
  have hker : ∀ u v, g u - D₁.μ v = 0 → g' (D₂.rem u) = 0 ∧ v = g (D₂.quot u) := by
    intro u v huv
    have hgu : g u = D₁.μ (g (D₂.quot u)) + D₁.sec (g' (D₂.rem u)) := by
      conv_lhs => rw [D₂.decomp u]
      rw [map_add, hg.comm_μ, hg.comm_sec]
    have h1 : g' (D₂.rem u) = 0 := by
      have := congrArg D₁.rem huv
      rw [map_sub, D₁.rem_μ, sub_zero, hg.comm_rem, map_zero] at this
      exact this
    refine ⟨h1, ?_⟩
    apply D₁.μ_injective
    rw [← sub_eq_zero.mp huv, hgu, h1, map_zero, add_zero]
  let P : E₂ × E₁ →L[ℂ] E₂ × E₁ :=
    (T.comp (ContinuousLinearMap.fst ℂ E₂ E₁)).prod
      (g.comp (D₂.quot.comp (ContinuousLinearMap.fst ℂ E₂ E₁)))
  have hP : ∀ z : E₂ × E₁, P z = (T z.1, g (D₂.quot z.1)) := fun z => rfl
  refine closedComplemented_of_proj _ P (fun z => ?_) (fun z hz => ?_)
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hP, koszulD₂_apply]
    dsimp only
    have hgp : g' (p (D₂.rem z.1)) = 0 := hp _
    have hgT : g (T z.1) = D₁.μ (g (D₂.quot z.1)) := by
      conv_lhs => rw [D₂.decomp (T z.1)]
      rw [map_add, hg.comm_μ, hg.comm_sec, hremT, hgp, map_zero, add_zero, hquotT]
    rw [hgT, sub_self, hfg]
    rfl
  · obtain ⟨u, v⟩ := z
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, koszulD₂_apply] at hz
    have h1 := congrArg Prod.fst hz
    dsimp only at h1
    obtain ⟨hrem, hv⟩ := hker u v h1
    have hTu : T u = u := by
      rw [hT, hpS _ hrem, sub_self, map_zero, sub_zero]
    rw [hP]
    dsimp only
    rw [hTu, hv]

end
end Hironaka.HironakaG10FlatKoszulDivision
