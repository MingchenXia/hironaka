/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.CoordinateSystem
import Hironaka.Scheme.Smooth.DifferentialBasis
import Hironaka.Scheme.Smooth.EtaleCoordinates
import Hironaka.Scheme.Smooth.EtaleLocal

/-!
# Two coordinate systems on one affine open

Kollár completes two given functions `x_1, x_1'` at `p` by common local coordinates
`x_2, …, x_n`, the last of them chosen generally, so that `x_1, x_2, …, x_n` and
`x_1', x_2, …, x_n` "are both local coordinate systems" ([Kol07, 95], the proof of Theorem 92);
Włodarczyk likewise takes `u_2, …, u_n` such that `u, u_2, …, u_n` and `v, u_2, …, u_n` "form two
sets of parameters on `U`" ([Wlo05, Lemma 2.9.5], step (0) of the proof). The "general choice"
is made where the theorem is proved
(`Hironaka/Resolution/Algebraic/MaximalContact/Theorem92.lean`); here both systems are hypotheses:
at a closed point `p` of `X` smooth of relative dimension `n` over the perfect field `k`, `u` and
`u` with its `i`-th member replaced by `v` are regular systems of parameters of `𝒪_{X,p}`. Then
(`exists_etaleCoordinates_pair`) there is one affine open `U ∋ p` carrying two coordinate systems
whose sections have germs `u` and `update u i v` at `p` and agree away from the `i`-th.

The argument, an assembly of the étale-coordinate lemmas: lift `v, u_0, …, u_{n-1}` to sections
of an affine open `V ∋ p` (`exists_affineOpen_germ_eq`); the differentials of each regular system
of parameters form a basis of `κ(p) ⊗ Ω[𝒪_{X,p}⁄k]`
(`exists_basis_tensor_kaehlerDifferential_of_span_eq_maximalIdeal`), so each lifted system is
étale on an affine open `U_1`, resp. `U_2`, around `p` (`exists_etale_toAffineSpace_of_basis`); a
basic open `U ⊆ U_1 ∩ U_2` around `p` is affine and étaleness restricts to it
(`etale_toAffineSpace_restrict`). Restrictions compose (Mathlib's
`TopCat.Presheaf.restrict_restrict`) and preserve germs (`germ_res_apply`).
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory IsLocalRing KaehlerDifferential TensorProduct

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

variable (f : X ⟶ Spec (.of k)) [PerfectField k] (n : ℕ) [SmoothOfRelativeDimension n f]

/-- At a closed point `p`, two regular systems of parameters `u` and `update u i v` of `𝒪_{X,p}`
differing in one member spread out to two coordinate systems on a common affine open `U ∋ p`,
with the prescribed germs at `p` and equal sections away from the `i`-th ([Kol07, 95]; the proof
of [Wlo05, Lemma 2.9.5]). -/
theorem exists_etaleCoordinates_pair {p : X} (hp : IsClosed ({p} : Set X))
    (u : Fin n → X.presheaf.stalk p) (i : Fin n) (v : X.presheaf.stalk p)
    (hu : maximalIdeal (X.presheaf.stalk p) = Ideal.span (Set.range u))
    (hv : maximalIdeal (X.presheaf.stalk p) = Ideal.span (Set.range (Function.update u i v))) :
    ∃ (U : X.affineOpens) (hpU : p ∈ U.1) (c c' : EtaleCoordinates f n U),
      (∀ j, X.presheaf.germ U.1 p hpU (c.v j) = u j) ∧
      (∀ j, X.presheaf.germ U.1 p hpU (c'.v j) = Function.update u i v j) ∧
      ∀ j, j ≠ i → c'.v j = c.v j := by
  classical
  let _ := f.stalkAlgebra p
  -- lifts of `v, u_0, …, u_{n-1}` to sections of an affine open `V ∋ p`
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hpV₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  obtain ⟨V, hpV, -, w, hw⟩ := exists_affineOpen_germ_eq ⟨V₀, hV₀⟩ hpV₀ (Fin.cons v u)
  set u₁ : Fin n → Γ(X, V.1) := fun j => w j.succ with hu1def
  set v₁ : Γ(X, V.1) := w 0 with hv1def
  have hu1_germ : ∀ j, X.presheaf.germ V.1 p hpV (u₁ j) = u j := fun j =>
    (hw j.succ).trans (Fin.cons_succ (α := fun _ => X.presheaf.stalk p) v u j)
  have hv1_germ : X.presheaf.germ V.1 p hpV v₁ = v :=
    (hw 0).trans (Fin.cons_zero (α := fun _ => X.presheaf.stalk p) v u)
  have hu2_germ : ∀ j, X.presheaf.germ V.1 p hpV (Function.update u₁ i v₁ j) =
      Function.update u i v j := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, Function.update_self, hv1_germ]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, hu1_germ]
  -- the differentials of both systems form bases at `p`
  obtain ⟨b, hb⟩ := exists_basis_tensor_kaehlerDifferential_of_span_eq_maximalIdeal f n hp u hu
  obtain ⟨b', hb'⟩ := exists_basis_tensor_kaehlerDifferential_of_span_eq_maximalIdeal f n hp
    (Function.update u i v) hv
  have hb₁ : ∃ b : Module.Basis (Fin n) (ResidueField (X.presheaf.stalk p))
      (ResidueField (X.presheaf.stalk p) ⊗[X.presheaf.stalk p] Ω[X.presheaf.stalk p⁄k]),
      ∀ j, b j = 1 ⊗ₜ D k (X.presheaf.stalk p) (X.presheaf.germ V.1 p hpV (u₁ j)) :=
    ⟨b, fun j => by rw [hb j, hu1_germ]⟩
  have hb₂ : ∃ b : Module.Basis (Fin n) (ResidueField (X.presheaf.stalk p))
      (ResidueField (X.presheaf.stalk p) ⊗[X.presheaf.stalk p] Ω[X.presheaf.stalk p⁄k]),
      ∀ j, b j = 1 ⊗ₜ D k (X.presheaf.stalk p)
        (X.presheaf.germ V.1 p hpV (Function.update u₁ i v₁ j)) :=
    ⟨b', fun j => by rw [hb' j, hu2_germ]⟩
  -- étale coordinates on affine opens `U₁, U₂ ⊆ V` around `p`
  obtain ⟨U₁, hpU₁, hU₁V, hE₁⟩ := exists_etale_toAffineSpace_of_basis f n V hpV u₁ hb₁
  obtain ⟨U₂, hpU₂, hU₂V, hE₂⟩ :=
    exists_etale_toAffineSpace_of_basis f n V hpV (Function.update u₁ i v₁) hb₂
  -- a basic open of `U₁` inside `U₂` around `p`
  obtain ⟨t, htU₂, hpt⟩ := U₁.2.exists_basicOpen_le (V := U₂.1) ⟨p, hpU₂⟩ hpU₁
  let U : X.affineOpens := ⟨X.basicOpen t, U₁.2.basicOpen t⟩
  have hUU₁ : U.1 ≤ U₁.1 := X.basicOpen_le t
  have hUU₂ : U.1 ≤ U₂.1 := htU₂
  have hUV : U.1 ≤ V.1 := hUU₁.trans hU₁V
  have hpU : p ∈ U.1 := hpt
  -- restrictions to `U` through `U₁` or `U₂` are the restriction from `V`
  have hres : ∀ {W : X.Opens} (h₁ : U.1 ≤ W) (h₂ : W ≤ V.1) (s : Γ(X, V.1)),
      X.presheaf.map (homOfLE h₁).op (X.presheaf.map (homOfLE h₂).op s) =
        X.presheaf.map (homOfLE hUV).op s :=
    fun h₁ h₂ s => TopCat.Presheaf.restrict_restrict h₁ h₂ s
  -- the two coordinate systems, restricted to `U`
  have hE₁' : Etale (toAffineSpace f U.1 fun j => X.presheaf.map (homOfLE hUV).op (u₁ j)) := by
    have := etale_toAffineSpace_restrict f hUU₁ (fun j => X.presheaf.map (homOfLE hU₁V).op (u₁ j))
    have e : (fun j => X.presheaf.map (homOfLE hUU₁).op (X.presheaf.map (homOfLE hU₁V).op (u₁ j))) =
        fun j => X.presheaf.map (homOfLE hUV).op (u₁ j) :=
      funext fun j => hres hUU₁ hU₁V (u₁ j)
    rwa [e] at this
  have hE₂' : Etale (toAffineSpace f U.1
      (Function.update (fun j => X.presheaf.map (homOfLE hUV).op (u₁ j)) i
        (X.presheaf.map (homOfLE hUV).op v₁))) := by
    have := etale_toAffineSpace_restrict f hUU₂
      (fun j => X.presheaf.map (homOfLE hU₂V).op (Function.update u₁ i v₁ j))
    have e : (fun j => X.presheaf.map (homOfLE hUU₂).op
        (X.presheaf.map (homOfLE hU₂V).op (Function.update u₁ i v₁ j))) =
        Function.update (fun j => X.presheaf.map (homOfLE hUV).op (u₁ j)) i
          (X.presheaf.map (homOfLE hUV).op v₁) := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Function.update_self]
        exact hres hUU₂ hU₂V v₁
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        exact hres hUU₂ hU₂V (u₁ j)
    rwa [e] at this
  refine ⟨U, hpU, ⟨fun j => X.presheaf.map (homOfLE hUV).op (u₁ j), hE₁'⟩,
    ⟨Function.update (fun j => X.presheaf.map (homOfLE hUV).op (u₁ j)) i
      (X.presheaf.map (homOfLE hUV).op v₁), hE₂'⟩, fun j => ?_, fun j => ?_, fun j hj => ?_⟩
  · exact (X.presheaf.germ_res_apply (homOfLE hUV) p hpU (u₁ j)).trans (hu1_germ j)
  · dsimp only
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, Function.update_self]
      exact (X.presheaf.germ_res_apply (homOfLE hUV) p hpU v₁).trans hv1_germ
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      exact (X.presheaf.germ_res_apply (homOfLE hUV) p hpU (u₁ j)).trans (hu1_germ j)
  · dsimp only
    exact Function.update_of_ne hj _ _

end AlgebraicGeometry
