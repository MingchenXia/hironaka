import Hironaka.Analytic.Unibranch.HironakaG10LfMatsumura
import Mathlib.RingTheory.Flat.Stability

/-!
# Flatness from flat graded pieces (Frisch, Th. (II,1)(ii); lane G10LF, sub-item G5.d of `hGF`)

Let `B → C` be a ring homomorphism with `C` Noetherian, `M` a finite `C`-module and `J` an ideal of `C`
contained in the Jacobson radical. Then:
* `flat_of_exact`: extensions of flat modules are flat;
* `flat_quotient_pow_of_flat_graded`: if every graded piece `Jᵏ M / Jᵏ⁺¹ M` is `B`-flat, so is every
  truncation `M / Jⁿ M`;
* `flat_of_forall_flat_quotient_pow`: if every truncation `M / Jⁿ M` is `B`-flat, then `M` is `B`-flat
  (Krull's intersection theorem over `C` on the finite `C`-modules `M ⊗_B I`, `I` a finitely generated ideal);
* **`flat_of_flat_graded`**: all graded pieces flat ⇒ `M` flat.

No hypothesis on `B` (any commutative ring). Pure algebra, no named input.
BP: hironaka-g10lf-generic-freeness.tex.
-/

set_option autoImplicit false

open Function TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10LfGradedFlat

/-- **Extensions of flat modules are flat.** -/
theorem flat_of_exact {R : Type*} [CommRing R] {M' M M'' : Type*} [AddCommGroup M'] [Module R M']
    [AddCommGroup M] [Module R M] [AddCommGroup M''] [Module R M''] (f : M' →ₗ[R] M)
    (g : M →ₗ[R] M'') (hf : Injective f) (hg : Surjective g) (hfg : Exact f g)
    [Module.Flat R M'] [Module.Flat R M''] : Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hy : I.subtype.lTensor M'' (g.rTensor I x) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.comp_apply, hx, map_zero]
  have hy0 : g.rTensor I x = 0 :=
    (Module.Flat.lTensor_preserves_injective_linearMap (M := M'') _ Subtype.val_injective)
      (hy.trans (map_zero _).symm)
  obtain ⟨x', rfl⟩ := (rTensor_exact I hfg hg x).1 hy0
  have h1 : f.rTensor R (I.subtype.lTensor M' x') = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, hx]
  have h2 : I.subtype.lTensor M' x' = 0 :=
    (Module.Flat.rTensor_preserves_injective_linearMap (M := R) f hf) (h1.trans (map_zero _).symm)
  have h3 : x' = 0 :=
    (Module.Flat.lTensor_preserves_injective_linearMap (M := M') _ Subtype.val_injective)
      (h2.trans (map_zero _).symm)
  rw [h3, map_zero]

variable {B C M : Type*} [CommRing B] [CommRing C] [Algebra B C] [AddCommGroup M] [Module C M]
  [Module B M] [IsScalarTower B C M]

/-- The `k`-th graded piece `Jᵏ M / Jᵏ⁺¹ M`. -/
abbrev gradedPiece (J : Ideal C) (k : ℕ) : Type _ :=
  ↥(J ^ k • (⊤ : Submodule C M)) ⧸
    Submodule.comap (J ^ k • (⊤ : Submodule C M)).subtype (J ^ (k + 1) • (⊤ : Submodule C M))

omit [Algebra B C] [Module B M] [IsScalarTower B C M] in
theorem pow_succ_smul_le (J : Ideal C) (k : ℕ) :
    J ^ (k + 1) • (⊤ : Submodule C M) ≤ J ^ k • (⊤ : Submodule C M) :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ k))

/-- **Truncations from graded pieces.** -/
theorem flat_quotient_pow_of_flat_graded (J : Ideal C)
    (h : ∀ k, Module.Flat B (gradedPiece (M := M) J k)) (n : ℕ) :
    Module.Flat B (M ⧸ (J ^ n • (⊤ : Submodule C M))) := by
  induction n with
  | zero =>
    have : Subsingleton (M ⧸ (J ^ 0 • (⊤ : Submodule C M))) := by
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.Quotient.subsingleton_iff.2 rfl
    infer_instance
  | succ n ih =>
    have := h n
    let N := J ^ n • (⊤ : Submodule C M)
    let N' := J ^ (n + 1) • (⊤ : Submodule C M)
    have hle : N' ≤ N := pow_succ_smul_le J n
    let f : gradedPiece (M := M) J n →ₗ[B] M ⧸ N' :=
      ((Submodule.comap N.subtype N').mapQ N' N.subtype le_rfl).restrictScalars B
    let g : M ⧸ N' →ₗ[B] M ⧸ N := (N'.mapQ N LinearMap.id hle).restrictScalars B
    have hf : Injective f := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      change Submodule.Quotient.mk (N.subtype y) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero] at hy
      change Submodule.Quotient.mk y = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact hy
    have hg : Surjective g := by
      intro z
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective N z
      exact ⟨Submodule.Quotient.mk m, rfl⟩
    have hfg : Exact f g := by
      intro z
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective N' z
      change Submodule.Quotient.mk m = (0 : M ⧸ N) ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hm
        exact ⟨Submodule.Quotient.mk ⟨m, hm⟩, rfl⟩
      · rintro ⟨y, hy⟩
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
        change Submodule.Quotient.mk (N.subtype y) = Submodule.Quotient.mk m at hy
        rw [Submodule.Quotient.eq] at hy
        have h1 : m = (y : M) - ((y : M) - m) := by abel
        rw [h1]
        exact N.sub_mem y.2 (hle hy)
    exact flat_of_exact f g hf hg hfg

/-- `M ⊗ (Jⁿ M)`-images lie in `Jⁿ (M ⊗_B I)`. -/
theorem mem_smul_top_of_mem_range_rTensor (J : Ideal C) (n : ℕ) (I : Ideal B) (x : M ⊗[B] I)
    (hx : x ∈ LinearMap.range ((J ^ n • (⊤ : Submodule C M)).subtype.restrictScalars B |>.rTensor I)) :
    x ∈ J ^ n • (⊤ : Submodule C (M ⊗[B] I)) := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul m i =>
    obtain ⟨m, hm⟩ := m
    rw [LinearMap.rTensor_tmul]
    change m ⊗ₜ[B] i ∈ _
    refine Submodule.smul_induction_on (p := fun m : M => m ⊗ₜ[B] i ∈
      J ^ n • (⊤ : Submodule C (M ⊗[B] I))) hm ?_ ?_
    · intro c hc m' _
      rw [← TensorProduct.smul_tmul']
      exact Submodule.smul_mem_smul hc Submodule.mem_top
    · intro m₁ m₂ h₁ h₂
      rw [TensorProduct.add_tmul]
      exact Submodule.add_mem _ h₁ h₂
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add]
    exact Submodule.add_mem _ h₁ h₂

/-- **Flatness from flat truncations** (Krull). -/
theorem flat_of_forall_flat_quotient_pow [IsNoetherianRing C] [Module.Finite C M] (J : Ideal C)
    (hJ : J ≤ Ideal.jacobson ⊥)
    (h : ∀ n, Module.Flat B (M ⧸ (J ^ n • (⊤ : Submodule C M)))) : Module.Flat B M := by
  rw [Module.Flat.iff_lTensor_injective]
  intro I hI
  have : Module.Finite B I := Module.Finite.iff_fg.2 hI
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : ∀ n, x ∈ J ^ n • (⊤ : Submodule C (M ⊗[B] I)) := by
    intro n
    have := h n
    let π : M →ₗ[B] M ⧸ (J ^ n • (⊤ : Submodule C M)) :=
      (J ^ n • (⊤ : Submodule C M)).mkQ.restrictScalars B
    have hπ : Surjective π := by
      intro z
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (J ^ n • (⊤ : Submodule C M)) z
      exact ⟨m, rfl⟩
    have hexπ : Exact ((J ^ n • (⊤ : Submodule C M)).subtype.restrictScalars B) π := by
      intro y
      change Submodule.Quotient.mk y = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, fun ⟨z, hz⟩ => hz ▸ z.2⟩
    have h1 : I.subtype.lTensor _ (π.rTensor I x) = 0 := by
      rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
        LinearMap.comp_apply, hx, map_zero]
    have h2 : π.rTensor I x = 0 :=
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
        (h1.trans (map_zero _).symm)
    exact mem_smul_top_of_mem_range_rTensor J n I x ((rTensor_exact I hexπ hπ x).1 h2)
  have hfin : Module.Finite C (M ⊗[B] I) :=
    Module.Finite.equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange B C C M I)
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson J (M := M ⊗[B] I) hJ
  have hx' : x ∈ (⨅ i : ℕ, J ^ i • ⊤ : Submodule C (M ⊗[B] I)) := Submodule.mem_iInf _ |>.2 hmem
  rw [hK] at hx'
  exact (Submodule.mem_bot C).1 hx'

/-- **Frisch (II,1)(ii): flat graded pieces ⇒ flat.** -/
theorem flat_of_flat_graded [IsNoetherianRing C] [Module.Finite C M] (J : Ideal C)
    (hJ : J ≤ Ideal.jacobson ⊥) (h : ∀ k, Module.Flat B (gradedPiece (M := M) J k)) :
    Module.Flat B M :=
  flat_of_forall_flat_quotient_pow J hJ (flat_quotient_pow_of_flat_graded J h)

end Hironaka.Analytic.Unibranch.HironakaG10LfGradedFlat
