import Hironaka.Resolution.HironakaG10FlatFrischBlockComplement
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Finite-rank Frisch flattener: the Schur ideal is a persistent universal flattener

For a block presentation `f (m, n) = (α m + γ n, β m + δ n)` with `γ` invertible,
the cokernel of `f` is literally `N₀ / range (β - δ γ⁻¹ α)`. Over a LOCAL ring,
if the Schur complement is residually zero, the cokernel is flat EXACTLY when the
Schur complement vanishes (flatness gives `K = 𝔪K` for its finitely generated range
`K`, Nakayama gives `K = 0`).

Universal and PERSISTENT form (relative dimension zero case of Frisch 1968,
Lemme 5): for a block matrix over ANY commutative ring `S` with `γ` invertible,
ONE ideal `J ⊆ S` (the entries of the Schur complement), chosen before all base
changes, has the property that for EVERY local ring `R` and EVERY ring map
`ψ : S → R` whose closed point lies on `V(J)` (i.e. `ψ(J) ⊆ 𝔪_R`; e.g. the germ
map at ANY nearby point of the flat piece, composed with any analytic map), the
base-changed cokernel is flat over `R` exactly when `ψ(J) = 0`. No flatness,
complement or inverse packet beyond the invertibility of the `γ` block is supplied.
Positive relative dimension (Banach `B(K)` / privileged polydiscs) is NOT covered.
BP FIRST: hironaka-g10-flat-frisch-finite-flattener.tex. -/
set_option autoImplicit false

namespace Hironaka.HironakaG10FlatFrischFiniteFlattener

open Hironaka.HironakaG10FlatFrischBlockComplement

section Modules
variable {R : Type*} [CommRing R] {M₁ N₁ M₀ N₀ : Type*}
  [AddCommGroup M₁] [AddCommGroup N₁] [AddCommGroup M₀] [AddCommGroup N₀]
  [Module R M₁] [Module R N₁] [Module R M₀] [Module R N₀]
  (α : M₁ →ₗ[R] M₀) (β : M₁ →ₗ[R] N₀) (δ : N₁ →ₗ[R] N₀) (e : N₁ ≃ₗ[R] M₀)

/-- The Schur complement `β - δ γ⁻¹ α`. -/
def schurMap : M₁ →ₗ[R] N₀ := β - δ ∘ₗ (e.symm : M₀ →ₗ[R] N₁) ∘ₗ α

/-- The reduction map `(a, b) ↦ [b - δ γ⁻¹ a]` onto `N₀ / range (Schur)`. -/
def reductionMap : M₀ × N₀ →ₗ[R] N₀ ⧸ LinearMap.range (schurMap α β δ e) :=
  (LinearMap.range (schurMap α β δ e)).mkQ ∘ₗ
    (LinearMap.snd R M₀ N₀ - δ ∘ₗ (e.symm : M₀ →ₗ[R] N₁) ∘ₗ LinearMap.fst R M₀ N₀)

theorem reductionMap_apply (x : M₀ × N₀) :
    reductionMap α β δ e x =
      Submodule.Quotient.mk (x.2 - δ (e.symm x.1)) := rfl

theorem reductionMap_surjective : Function.Surjective (reductionMap α β δ e) := by
  intro y
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
  exact ⟨(0, b), by simp [reductionMap_apply]⟩

/-- The kernel of the reduction map is EXACTLY the image of the block map. -/
theorem ker_reductionMap :
    LinearMap.ker (reductionMap α β δ e) = LinearMap.range (blockMap α β (e : N₁ →ₗ[R] M₀) δ) := by
  ext x
  rw [LinearMap.mem_ker, reductionMap_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range,
    LinearMap.mem_range]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨(m, e.symm (x.1 - α m)), ?_⟩
    rw [blockMap_apply]
    ext
    · simp
    · change β m + δ (e.symm (x.1 - α m)) = x.2
      have hm' : β m - δ (e.symm (α m)) = x.2 - δ (e.symm x.1) := hm
      rw [map_sub, map_sub]
      rw [sub_eq_sub_iff_add_eq_add] at hm'
      calc β m + (δ (e.symm x.1) - δ (e.symm (α m)))
          = (β m + δ (e.symm x.1)) - δ (e.symm (α m)) := by abel
        _ = (x.2 + δ (e.symm (α m))) - δ (e.symm (α m)) := by rw [hm']
        _ = x.2 := by abel
  · rintro ⟨y, rfl⟩
    refine ⟨y.1, ?_⟩
    rw [blockMap_apply]
    change β y.1 - δ (e.symm (α y.1)) =
      (β y.1 + δ y.2) - δ (e.symm (α y.1 + e y.2))
    rw [map_add, map_add, LinearEquiv.symm_apply_apply]
    abel

/-- The cokernel of the block presentation is literally `N₀ / range (Schur)`. -/
noncomputable def cokernelEquiv :
    ((M₀ × N₀) ⧸ LinearMap.range (blockMap α β (e : N₁ →ₗ[R] M₀) δ)) ≃ₗ[R]
      (N₀ ⧸ LinearMap.range (schurMap α β δ e)) :=
  (Submodule.quotEquivOfEq _ _ (ker_reductionMap α β δ e).symm).trans
    ((reductionMap α β δ e).quotKerEquivOfSurjective (reductionMap_surjective α β δ e))

/-- Finite-rank local flattening criterion: over a LOCAL ring, with `M₁` finite,
`N₀` flat and the Schur complement residually zero, the cokernel is flat EXACTLY
when the Schur complement vanishes. -/
theorem flat_cokernel_iff [IsLocalRing R] [Module.Finite R M₁] [Module.Flat R N₀]
    (hres : LinearMap.range (schurMap α β δ e) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R N₀)) :
    Module.Flat R ((M₀ × N₀) ⧸ LinearMap.range (blockMap α β (e : N₁ →ₗ[R] M₀) δ)) ↔
      schurMap α β δ e = 0 := by
  rw [Module.Flat.equiv_iff (cokernelEquiv α β δ e)]
  set K := LinearMap.range (schurMap α β δ e)
  constructor
  · intro hflat
    have hK : K = IsLocalRing.maximalIdeal R • K := by
      have h := LinearMap.ker_inf_smul_top_eq_smul_of_flat (IsLocalRing.maximalIdeal R) K.mkQ
        K.mkQ_surjective
      rw [Submodule.ker_mkQ, inf_eq_left.mpr hres] at h
      exact h
    have hfg : (LinearMap.range (schurMap α β δ e)).FG := by
      rw [LinearMap.range_eq_map]
      exact (Module.Finite.fg_top (R := R) (M := M₁)).map _
    have hbot : K = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) K hfg
        hK.le (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    exact LinearMap.range_eq_bot.mp hbot
  · intro hS
    have hbot : K = ⊥ := LinearMap.range_eq_bot.mpr hS
    exact Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot K hbot)

end Modules

section Matrices
variable {S R : Type*} [CommRing S] [CommRing R]
  {ι₁ κ₁ ι₀ κ₀ : Type*} [Fintype ι₁] [Fintype κ₁] [Fintype ι₀] [Fintype κ₀]
  [DecidableEq ι₁] [DecidableEq κ₁] [DecidableEq ι₀] [DecidableEq κ₀]

omit [Fintype κ₀] [DecidableEq κ₀] in
/-- The Schur map of the base-changed block matrix is the base change of the Schur matrix. -/
theorem schurMap_baseChange (ψ : S →+* R) (α : Matrix ι₀ ι₁ S) (β : Matrix κ₀ ι₁ S)
    (γ : Matrix ι₀ κ₁ S) (δ : Matrix κ₀ κ₁ S) (γinv : Matrix κ₁ ι₀ S)
    (h₁ : γ * γinv = 1) (h₂ : γinv * γ = 1) :
    schurMap (Matrix.toLin' (α.map ψ)) (Matrix.toLin' (β.map ψ)) (Matrix.toLin' (δ.map ψ))
        (baseChangedGammaEquiv ψ γ γinv h₁ h₂) =
      Matrix.toLin' ((β - δ * γinv * α).map ψ) := by
  rw [schurMap]
  change Matrix.toLin' (β.map ψ) -
      Matrix.toLin' (δ.map ψ) ∘ₗ Matrix.toLin' (γinv.map ψ) ∘ₗ Matrix.toLin' (α.map ψ) = _
  rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← map_sub, ← Matrix.map_mul, ← Matrix.map_mul,
    Matrix.mul_assoc, Matrix.map_sub ψ (map_sub ψ)]

/-- Universal PERSISTENT finite-rank flattener: ONE ideal `J` of `S` (the Schur
ideal), chosen before all base changes; for EVERY local ring `R` and EVERY ring map
`ψ : S → R` with `ψ(J) ⊆ 𝔪_R`, the base-changed cokernel is flat over `R` exactly
when `ψ(J) = 0`. -/
theorem flat_matrixCokernel_iff (α : Matrix ι₀ ι₁ S) (β : Matrix κ₀ ι₁ S)
    (γ : Matrix ι₀ κ₁ S) (δ : Matrix κ₀ κ₁ S) (γinv : Matrix κ₁ ι₀ S)
    (h₁ : γ * γinv = 1) (h₂ : γinv * γ = 1) [IsLocalRing R] (ψ : S →+* R)
    (hψ : Ideal.map ψ (schurIdeal α β δ γinv) ≤ IsLocalRing.maximalIdeal R) :
    Module.Flat R (((ι₀ → R) × (κ₀ → R)) ⧸ LinearMap.range (matrixBlockMap ψ α β γ δ)) ↔
      Ideal.map ψ (schurIdeal α β δ γinv) = ⊥ := by
  let E := baseChangedGammaEquiv ψ γ γinv h₁ h₂
  have hγ : (E : (κ₁ → R) →ₗ[R] (ι₀ → R)) = Matrix.toLin' (γ.map ψ) := rfl
  have hblock : matrixBlockMap ψ α β γ δ =
      blockMap (Matrix.toLin' (α.map ψ)) (Matrix.toLin' (β.map ψ))
        (E : (κ₁ → R) →ₗ[R] (ι₀ → R)) (Matrix.toLin' (δ.map ψ)) := by
    rw [hγ]; rfl
  have hentry (k : κ₀) (i : ι₁) :
      ψ ((β - δ * γinv * α) k i) ∈ Ideal.map ψ (schurIdeal α β δ γinv) :=
    Ideal.mem_map_of_mem ψ (Ideal.subset_span ⟨(k, i), rfl⟩)
  have hres : LinearMap.range (schurMap (Matrix.toLin' (α.map ψ)) (Matrix.toLin' (β.map ψ))
      (Matrix.toLin' (δ.map ψ)) E) ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (κ₀ → R)) := by
    rw [schurMap_baseChange ψ α β γ δ γinv h₁ h₂]
    rintro _ ⟨v, rfl⟩
    rw [Matrix.toLin'_apply]
    have hcol : ∀ k : κ₀, (Matrix.mulVec ((β - δ * γinv * α).map ψ) v) k ∈ IsLocalRing.maximalIdeal R := by
      intro k
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_right _ _ (hψ (by simpa only [Matrix.map_apply] using hentry k i))
    have hdecomp : (Matrix.mulVec ((β - δ * γinv * α).map ψ) v) =
        ∑ k : κ₀, (Matrix.mulVec ((β - δ * γinv * α).map ψ) v) k • Pi.single k (1 : R) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hdecomp]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (hcol k) Submodule.mem_top
  rw [hblock, flat_cokernel_iff _ _ _ E hres, schurMap_baseChange ψ α β γ δ γinv h₁ h₂,
    schurIdeal, Ideal.map_span, Ideal.span_eq_bot]
  constructor
  · intro h
    have h0 : (β - δ * γinv * α).map ψ = 0 := Matrix.toLin'.injective (by rw [h, map_zero])
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    have hp := congrFun (congrFun h0 p.1) p.2
    simpa only [Matrix.map_apply, Matrix.zero_apply] using hp
  · intro h
    have h0 : (β - δ * γinv * α).map ψ = 0 := by
      ext k i
      simpa only [Matrix.map_apply, Matrix.zero_apply] using h _ ⟨_, ⟨(k, i), rfl⟩, rfl⟩
    rw [h0, map_zero]

/-- Flatness over the flat piece itself: over the quotient by the Schur ideal (a
local ring when `S` is local and `J` proper) the cokernel is flat. -/
theorem flat_matrixCokernel_quotient (α : Matrix ι₀ ι₁ S) (β : Matrix κ₀ ι₁ S)
    (γ : Matrix ι₀ κ₁ S) (δ : Matrix κ₀ κ₁ S) (γinv : Matrix κ₁ ι₀ S)
    (h₁ : γ * γinv = 1) (h₂ : γinv * γ = 1)
    [IsLocalRing (S ⧸ schurIdeal α β δ γinv)] :
    Module.Flat (S ⧸ schurIdeal α β δ γinv)
      (((ι₀ → S ⧸ schurIdeal α β δ γinv) × (κ₀ → S ⧸ schurIdeal α β δ γinv)) ⧸
        LinearMap.range (matrixBlockMap (Ideal.Quotient.mk (schurIdeal α β δ γinv)) α β γ δ)) := by
  have hbot : Ideal.map (Ideal.Quotient.mk (schurIdeal α β δ γinv)) (schurIdeal α β δ γinv) = ⊥ :=
    Ideal.map_quotient_self _
  exact (flat_matrixCokernel_iff α β γ δ γinv h₁ h₂ _ (by rw [hbot]; exact bot_le)).mpr hbot

end Matrices

end Hironaka.HironakaG10FlatFrischFiniteFlattener
