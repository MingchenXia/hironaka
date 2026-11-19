import Hironaka.Resolution.HironakaG11InvAmbientIso

/-!
# Flattening coordinates of an embedded germ onto its coordinate tangent dimension

Lane G11B (run 0080, round 2), G11 route step 4 for the Hilbert--Samuel route (`ROUTE-r2.md` §4): the first half of the
minimal-window constructor.  For `S ⊆ ℂⁿ`, `c₀ ∈ ℂⁿ` and `k` the dimension of the coordinate tangent space
`HironakaG11InvAmbientIso.vanishingTangent S c₀`, there is a local biholomorphism `Φ` near `c₀` (inside any prescribed open
neighbourhood) carrying `S` into the coordinate plane `ℂᵏ × 0`: all coordinates `j ≥ k` of `Φ` vanish on `S` near `c₀`.
Source: the classical construction of a minimal embedding (Grauert--Remmert; Bierstone--Milman 1997 §1).

Proof: a linear map `L` with values in `ℂᵏ × 0`, injective on the tangent space (a basis of the tangent space read through
the projection along a complement), corrected by a map `H` vanishing on `S` (`exists_vanishing_correction`), so that
`d(L + H)` is injective; inverse function theorem on the open set where `H` vanishes on `S`.

* **`exists_flattening`**.  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11InvMinimalWindow

open HironakaG11InvAmbientIso

noncomputable section

variable {n : ℕ}

/-- A linear map into `ℂᵏ × 0`, injective on a subspace `T` of dimension `k`. -/
private theorem exists_linear_flat (T : Submodule ℂ (ComplexModel n)) :
    ∃ L : ComplexModel n →L[ℂ] ComplexModel n,
      (∀ v, ∀ j : Fin n, Module.finrank ℂ T ≤ j.val → L v j = 0) ∧ ∀ v ∈ T, L v = 0 → v = 0 := by
  set k := Module.finrank ℂ T with hkdef
  have hk : k ≤ n := by
    have := Submodule.finrank_le T
    simpa using this
  obtain ⟨W, hTW⟩ := T.exists_isCompl
  let b : Module.Basis (Fin k) ℂ T := Module.finBasisOfFinrankEq ℂ T rfl
  let P : ComplexModel n →ₗ[ℂ] T :=
    LinearMap.fst ℂ T W ∘ₗ (Submodule.prodEquivOfIsCompl T W hTW).symm.toLinearMap
  have hP : ∀ v (hv : v ∈ T), P v = ⟨v, hv⟩ := by
    intro v hv
    show ((Submodule.prodEquivOfIsCompl T W hTW).symm v).1 = ⟨v, hv⟩
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left T W hTW ⟨v, hv⟩]
  let coeff : Fin k → ComplexModel n →ₗ[ℂ] ℂ := fun i => Finsupp.lapply i ∘ₗ b.repr.toLinearMap ∘ₗ P
  let L₀ : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    ∑ i, (coeff i).smulRight (EuclideanSpace.single (Fin.castLE hk i) (1 : ℂ))
  have hL₀ : ∀ v j, L₀ v j = ∑ i, coeff i v * (if j = Fin.castLE hk i then 1 else 0) := by
    intro v j
    simp only [L₀]
    simp
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.single_apply]
    split_ifs <;> simp
  refine ⟨LinearMap.toContinuousLinearMap L₀, fun v j hj => ?_, fun v hv h0 => ?_⟩
  · show L₀ v j = 0
    rw [hL₀]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : j ≠ Fin.castLE hk i := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    simp [hne]
  · have hc : ∀ i, coeff i v = 0 := by
      intro i
      have h1 : L₀ v (Fin.castLE hk i) = coeff i v := by
        rw [hL₀, Finset.sum_eq_single i]
        · simp
        · intro i' _ hi'
          have hne : Fin.castLE hk i ≠ Fin.castLE hk i' := fun h => hi' (Fin.castLE_injective hk h).symm
          simp [hne]
        · simp
      have h2 : L₀ v = 0 := h0
      rw [← h1, h2]; rfl
    have hrepr : b.repr (P v) = 0 := by
      ext i
      exact hc i
    have hPv : P v = 0 := b.repr.injective (by rw [hrepr, map_zero])
    rw [hP v hv] at hPv
    exact congrArg Subtype.val hPv

/-- **Flattening coordinates onto the tangent dimension**: for `S ⊆ ℂⁿ`, `c₀`, an open `N₀ ∋ c₀` and
`k = dim vanishingTangent S c₀`, there is a local biholomorphism `Φ` at `c₀` with source inside `N₀` such that every
coordinate `j ≥ k` of `Φ` vanishes on `S ∩ source`. -/
theorem exists_flattening (S : Set (ComplexModel n)) {c₀ : ComplexModel n} {N₀ : Set (ComplexModel n)}
    (hN₀ : IsOpen N₀) (hc₀ : c₀ ∈ N₀) :
    ∃ Φ : LocalHolomorphicEquivAt (n := n) c₀, Φ.source ⊆ N₀ ∧
      ∀ x ∈ Φ.source, x ∈ S → ∀ j : Fin n,
        Module.finrank ℂ (vanishingTangent S c₀) ≤ j.val → Φ.toFun x j = 0 := by
  obtain ⟨L, hLflat, hLinj⟩ := exists_linear_flat (vanishingTangent S c₀)
  obtain ⟨H, hHd, hHz, hinj⟩ := exists_vanishing_correction S c₀ L hLinj
  obtain ⟨t, ht, htopen, hc₀t⟩ := eventually_nhds_iff.mp (hHd.and hHz)
  let F : ComplexModel n → ComplexModel n := fun x => L x + H x
  have hFdiff : DifferentiableOn ℂ F (N₀ ∩ t) := fun x hx =>
    (L.differentiableAt.add (ht x hx.2).1).differentiableWithinAt
  have hFinj : Function.Injective (fderiv ℂ F c₀) := by
    have h1 : fderiv ℂ F c₀ = L + fderiv ℂ H c₀ := by
      rw [fderiv_fun_add L.differentiableAt (ht c₀ hc₀t).1, L.fderiv]
    rw [h1]
    exact hinj
  obtain ⟨Φ, hΦsrc, hΦF, -⟩ := exists_localHolomorphicEquivAt (hN₀.inter htopen) ⟨hc₀, hc₀t⟩ hFdiff hFinj
  refine ⟨Φ, fun x hx => (hΦsrc hx).1, fun x hx hxS j hj => ?_⟩
  rw [hΦF]
  show (L x + H x) j = 0
  rw [(ht x (hΦsrc hx).2).2 hxS, add_zero]
  exact hLflat x j hj

end

end Hironaka.HironakaG11InvMinimalWindow
