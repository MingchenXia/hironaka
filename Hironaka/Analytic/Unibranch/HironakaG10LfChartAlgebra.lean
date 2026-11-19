import Hironaka.Analytic.Unibranch.HironakaG10LfMatsumura
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Item 1b, algebra: flatness of a base-changed cokernel and its special fibre (lane G10LF)

Setting: `A → R` a flat local homomorphism of Noetherian local rings, `I ≤ 𝔪_A`, `B = A ⧸ I`,
`F : R^b → R^a`, `G : R^c → R^b` matrices with `F G ≡ 0` and `ker F ⊆ im G` modulo `I R`
(an exact start of `coker F` modulo `I`). Then
**`flat_quotient_baseChange_coker_iff`**: `B ⊗_A coker F` is flat over `B` iff the start is exact
modulo `𝔪_A R` (the special fibre), i.e. `F v ∈ 𝔪_A R^a ⇒ v ∈ G R^c + 𝔪_A R^b`.

Ingredients (no `Tor`):
* `flat_quotient_baseChange_of_lTensor_injective`: the local flatness criterion for `B ⊗_A X`, `X` a
  finite `R`-module (Krull's theorem over `R` on `X ⊗_A J ≅ (B ⊗_A X) ⊗_B J`), from the Tor-free
  machinery of `HironakaG10LfMatsumura`;
* `lTensor_quotient_injective_iff`: `k ⊗ Z → k ⊗ P` injective iff `Z ∩ 𝔪P ⊆ 𝔪Z` (`k = B/𝔪`);
* mathlib's `lTensor_injective_of_exact_of_exact_of_rTensor_injective` (balancing of `Tor₁`).

BP: hironaka-g10lf-local-flatness.tex. No named input.
-/

set_option autoImplicit false

open Function TensorProduct IsLocalRing Hironaka.Analytic.Unibranch.HironakaG10LfMatsumura
open scoped Matrix

namespace Hironaka.Analytic.Unibranch.HironakaG10LfChartAlgebra

universe uB uM

/-! ### The criterion with an abstract separation hypothesis -/

section Separated

variable {B : Type uB} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  (M : Type uM) [AddCommGroup M] [Module B M]

/-- **Local flatness criterion, separated form.** If `𝔪 ⊗ M → M` is injective and every `M ⊗ J` is
`𝔪`-adically separated along the images of `M ⊗ 𝔪ᵏJ`, then `M` is flat. -/
theorem flat_of_lTensor_injective_of_separated (h : Injective ((maximalIdeal B).subtype.lTensor M))
    (hsep : ∀ (J : Ideal B) (x : M ⊗[B] J), (∀ k, x ∈ LinearMap.range
      ((maximalIdeal B ^ k • (⊤ : Submodule B J)).subtype.lTensor M)) → x = 0) :
    Module.Flat B M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, hc⟩ := exists_comap_pow_le (maximalIdeal B) J
  apply hsep J x
  intro k
  obtain ⟨w, rfl⟩ := mem_range_of_lTensor_eq_zero M h J (k + c) x hx
  refine ⟨(Submodule.inclusion (hc k)).lTensor M w, ?_⟩
  rw [← LinearMap.lTensor_comp_apply, Submodule.subtype_comp_inclusion]

end Separated

/-! ### Base change to a quotient of the base -/

section BaseChange

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

theorem tmul_mem_of_mem_smul_top {X : Type*} [AddCommGroup X] [Module R X] [Module A X]
    [IsScalarTower A R X] (I 𝔞 : Ideal A) (J : Ideal (A ⧸ I)) (k : ℕ) (x : X) (s : J)
    (hs : s ∈ (𝔞.map (Ideal.Quotient.mk I)) ^ k • (⊤ : Submodule (A ⧸ I) J)) :
    x ⊗ₜ[A] s ∈ (𝔞.map (algebraMap A R)) ^ k • (⊤ : Submodule R (X ⊗[A] J)) := by
  refine Submodule.smul_induction_on (p := fun s : J => x ⊗ₜ[A] s ∈
    (𝔞.map (algebraMap A R)) ^ k • (⊤ : Submodule R (X ⊗[A] J))) hs ?_ ?_
  · intro β hβ s' _
    rw [← Ideal.map_pow] at hβ
    obtain ⟨α, hα, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hβ
    have h1 : (Ideal.Quotient.mk I α) • s' = α • s' := by
      rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    rw [h1, TensorProduct.tmul_smul, ← algebraMap_smul R α (x ⊗ₜ[A] s')]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hα
  · intro s₁ s₂ h₁ h₂
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _ h₁ h₂

variable [IsLocalRing A] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing R]
  [IsLocalHom (algebraMap A R)]

/-- **Local flatness criterion for `B ⊗_A X`** (`B = A ⧸ I`, `X` a finite `R`-module): if
`𝔪_B ⊗ (B ⊗_A X) → B ⊗_A X` is injective, then `B ⊗_A X` is flat over `B`. -/
theorem flat_quotient_baseChange_of_lTensor_injective {X : Type*} [AddCommGroup X] [Module R X]
    [Module A X] [IsScalarTower A R X] [Module.Finite R X] (I : Ideal A) [IsLocalRing (A ⧸ I)]
    (h : Injective ((maximalIdeal (A ⧸ I)).subtype.lTensor ((A ⧸ I) ⊗[A] X))) :
    Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] X) := by
  apply flat_of_lTensor_injective_of_separated _ h
  intro J x hx
  let e₁ := TensorProduct.comm (A ⧸ I) ((A ⧸ I) ⊗[A] X) J
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) J X
  let e₃ := TensorProduct.comm A J X
  let e : ((A ⧸ I) ⊗[A] X) ⊗[A ⧸ I] J ≃+ X ⊗[A] J :=
    ((e₁.trans e₂).toAddEquiv).trans e₃.toAddEquiv
  have he : ∀ (b : A ⧸ I) (x' : X) (s : J), e ((b ⊗ₜ[A] x') ⊗ₜ[A ⧸ I] s) = x' ⊗ₜ[A] (b • s) := by
    intro b x' s
    rfl
  have hm : maximalIdeal (A ⧸ I) = (maximalIdeal A).map (Ideal.Quotient.mk I) :=
    (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  have hmem : ∀ k, e x ∈ ((maximalIdeal A).map (algebraMap A R)) ^ k •
      (⊤ : Submodule R (X ⊗[A] J)) := by
    intro k
    obtain ⟨w, hw⟩ := hx k
    rw [← hw]
    clear hw hx
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
    | tmul m s =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
      induction m using TensorProduct.induction_on with
      | zero => rw [TensorProduct.zero_tmul, map_zero]; exact Submodule.zero_mem _
      | tmul b x' =>
        rw [he]
        apply tmul_mem_of_mem_smul_top I (maximalIdeal A) J k x'
        rw [← hm]
        exact Submodule.smul_mem _ b s.2
      | add m₁ m₂ h₁ h₂ =>
        rw [TensorProduct.add_tmul, map_add]
        exact Submodule.add_mem _ h₁ h₂
    | add w₁ w₂ h₁ h₂ =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ h₁ h₂
  have hfinB : Module.Finite A (A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A I).toLinearMap Ideal.Quotient.mk_surjective
  have hfinJ : Module.Finite A J := Module.Finite.trans (A ⧸ I) J
  have hfin : Module.Finite R (X ⊗[A] J) :=
    Module.Finite.equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A R R X J)
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing ((maximalIdeal A).map (algebraMap A R))
    (M := X ⊗[A] J) (ne_top_of_lt (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A R)))
  have hx' : e x ∈ (⨅ i : ℕ, ((maximalIdeal A).map (algebraMap A R)) ^ i •
      ⊤ : Submodule R (X ⊗[A] J)) := Submodule.mem_iInf _ |>.2 hmem
  rw [hK] at hx'
  exact e.injective (((Submodule.mem_bot R).1 hx').trans (map_zero e).symm)

end BaseChange

/-! ### `k ⊗ Z → k ⊗ P` injective iff `Z ∩ 𝔪P ⊆ 𝔪Z` -/

section QLemma

variable {B : Type*} [CommRing B] (𝔪 : Ideal B)

theorem lTensor_quotient_injective_iff {Z P : Type*} [AddCommGroup Z] [Module B Z] [AddCommGroup P]
    [Module B P] (ι : Z →ₗ[B] P) :
    Injective (ι.lTensor (B ⧸ 𝔪)) ↔
      ∀ z, ι z ∈ 𝔪 • (⊤ : Submodule B P) → z ∈ 𝔪 • (⊤ : Submodule B Z) := by
  let eZ := TensorProduct.quotTensorEquivQuotSMul Z 𝔪
  let eP := TensorProduct.quotTensorEquivQuotSMul P 𝔪
  have hle : 𝔪 • (⊤ : Submodule B Z) ≤ (𝔪 • (⊤ : Submodule B P)).comap ι := by
    rw [Submodule.smul_le]
    intro r hr z _
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  let q : (Z ⧸ 𝔪 • (⊤ : Submodule B Z)) →ₗ[B] (P ⧸ 𝔪 • (⊤ : Submodule B P)) :=
    Submodule.mapQ _ _ ι hle
  have hnat : ∀ w, eP (ι.lTensor (B ⧸ 𝔪) w) = q (eZ w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | tmul r z =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [LinearMap.lTensor_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
        TensorProduct.quotTensorEquivQuotSMul_mk_tmul, Submodule.mapQ_apply, map_smul]
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  constructor
  · intro hinj z hz
    have h0 : ι.lTensor (B ⧸ 𝔪) (eZ.symm (Submodule.Quotient.mk z)) = 0 := by
      apply eP.injective
      rw [hnat, LinearEquiv.apply_symm_apply, Submodule.mapQ_apply, map_zero,
        Submodule.Quotient.mk_eq_zero]
      exact hz
    have h1 := hinj (h0.trans (map_zero _).symm)
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h1
    exact h1
  · intro hQ
    rw [injective_iff_map_eq_zero]
    intro w hw
    have h1 : q (eZ w) = 0 := by rw [← hnat, hw, map_zero]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (eZ w)
    rw [← hz, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    apply eZ.injective
    rw [map_zero, ← hz, Submodule.Quotient.mk_eq_zero]
    exact hQ z h1

theorem mem_smul_top_range_iff {Q P : Type*} [AddCommGroup Q] [Module B Q] [AddCommGroup P]
    [Module B P] (g : Q →ₗ[B] P) (z : LinearMap.range g) :
    z ∈ 𝔪 • (⊤ : Submodule B (LinearMap.range g)) ↔ ∃ q ∈ 𝔪 • (⊤ : Submodule B Q), g q = z := by
  have hmap : (𝔪 • (⊤ : Submodule B (LinearMap.range g))).map (LinearMap.range g).subtype =
      (𝔪 • (⊤ : Submodule B Q)).map g := by
    rw [Submodule.map_smul'', Submodule.map_smul'', Submodule.map_subtype_top,
      LinearMap.range_eq_map]
  constructor
  · intro hz
    have h1 : (z : P) ∈ (𝔪 • (⊤ : Submodule B Q)).map g := by
      rw [← hmap]
      exact Submodule.mem_map_of_mem hz
    obtain ⟨q, hq, hqz⟩ := h1
    exact ⟨q, hq, hqz⟩
  · rintro ⟨q, hq, hqz⟩
    have h1 : (z : P) ∈ (𝔪 • (⊤ : Submodule B (LinearMap.range g))).map
        (LinearMap.range g).subtype := by
      rw [hmap]
      exact ⟨q, hq, hqz⟩
    obtain ⟨z', hz', hzz'⟩ := h1
    rwa [← Subtype.ext hzz']

end QLemma

/-! ### Vectors over `R`, and the map `v ↦ 1 ⊗ v` into `B ⊗_A R^n` -/

section Vectors

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

theorem mem_smul_top_pi_iff (J : Ideal A) {n : ℕ} (v : Fin n → R) :
    v ∈ (J • ⊤ : Submodule A (Fin n → R)) ↔ ∀ j, v j ∈ J.map (algebraMap A R) := by
  constructor
  · intro hv
    refine Submodule.smul_induction_on
      (p := fun v : Fin n → R => ∀ j, v j ∈ J.map (algebraMap A R)) hv ?_ ?_
    · intro α hα y _ j
      rw [Pi.smul_apply, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hα)
    · intro y₁ y₂ h₁ h₂ j
      rw [Pi.add_apply]
      exact Ideal.add_mem _ (h₁ j) (h₂ j)
  · intro hv
    have hR : ∀ (r : R) (w : Fin n → R), w ∈ (J • ⊤ : Submodule A (Fin n → R)) →
        r • w ∈ (J • ⊤ : Submodule A (Fin n → R)) := by
      intro r w hw
      refine Submodule.smul_induction_on
        (p := fun w => r • w ∈ (J • ⊤ : Submodule A (Fin n → R))) hw ?_ ?_
      · intro α hα y _
        rw [smul_comm r α y]
        exact Submodule.smul_mem_smul hα Submodule.mem_top
      · intro w₁ w₂ h₁ h₂
        rw [smul_add]
        exact Submodule.add_mem _ h₁ h₂
    have hsingle : ∀ (j : Fin n) (x : R), x ∈ J.map (algebraMap A R) →
        (Pi.single j x : Fin n → R) ∈ (J • ⊤ : Submodule A (Fin n → R)) := by
      intro j x hx
      have hx' : x ∈ Submodule.span R (algebraMap A R '' (J : Set A)) := hx
      clear hx
      induction hx' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨α, hα, rfl⟩ := hx
        have h1 : (Pi.single j (algebraMap A R α) : Fin n → R) =
            α • (Pi.single j 1 : Fin n → R) := by
          rw [← Pi.single_smul, Algebra.smul_def, mul_one]
        rw [h1]
        exact Submodule.smul_mem_smul hα Submodule.mem_top
      | zero => rw [Pi.single_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Pi.single_add]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        rw [Pi.single_smul]
        exact hR r _ hx
    rw [← Finset.univ_sum_single v]
    exact Submodule.sum_mem _ fun j _ => hsingle j (v j) (hv j)

variable (I : Ideal A)

/-- `v ↦ 1 ⊗ v`. -/
abbrev one_tmul (n : ℕ) : (Fin n → R) →ₗ[A] (A ⧸ I) ⊗[A] (Fin n → R) :=
  TensorProduct.mk A (A ⧸ I) (Fin n → R) 1

theorem one_tmul_surjective (n : ℕ) : Surjective (one_tmul (R := R) I n) := by
  intro p
  induction p using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul b v =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨a • v, ?_⟩
    change (1 : A ⧸ I) ⊗ₜ[A] (a • v) = _
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      Ideal.Quotient.algebraMap_eq]
  | add p q hp hq =>
    obtain ⟨v, hv⟩ := hp
    obtain ⟨w, hw⟩ := hq
    exact ⟨v + w, by rw [map_add, hv, hw]⟩

theorem one_tmul_eq_zero_iff (n : ℕ) (v : Fin n → R) :
    one_tmul I n v = 0 ↔ ∀ j, v j ∈ I.map (algebraMap A R) := by
  rw [← mem_smul_top_pi_iff, ← Submodule.Quotient.mk_eq_zero,
    ← TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, LinearEquiv.map_eq_zero_iff]
  rfl

theorem one_tmul_mem_smul_iff {J : Ideal A} (hIJ : I ≤ J) (n : ℕ) (v : Fin n → R) :
    one_tmul I n v ∈ (J.map (Ideal.Quotient.mk I) •
      (⊤ : Submodule (A ⧸ I) ((A ⧸ I) ⊗[A] (Fin n → R)))) ↔
      ∀ j, v j ∈ J.map (algebraMap A R) := by
  rw [← mem_smul_top_pi_iff]
  constructor
  · intro hv
    have key : ∀ p ∈ (J.map (Ideal.Quotient.mk I) •
        (⊤ : Submodule (A ⧸ I) ((A ⧸ I) ⊗[A] (Fin n → R)))),
        ∃ u ∈ (J • ⊤ : Submodule A (Fin n → R)), one_tmul I n u = p := by
      intro p hp
      refine Submodule.smul_induction_on (p := fun p => ∃ u ∈ (J • ⊤ : Submodule A (Fin n → R)),
        one_tmul I n u = p) hp ?_ ?_
      · intro β hβ q _
        obtain ⟨α, hα, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hβ
        obtain ⟨y, rfl⟩ := one_tmul_surjective I n q
        refine ⟨α • y, Submodule.smul_mem_smul hα Submodule.mem_top, ?_⟩
        rw [map_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
      · rintro p₁ p₂ ⟨u₁, hu₁, rfl⟩ ⟨u₂, hu₂, rfl⟩
        exact ⟨u₁ + u₂, Submodule.add_mem _ hu₁ hu₂, map_add _ _ _⟩
    obtain ⟨u, hu, huv⟩ := key _ hv
    have h0 : one_tmul I n (v - u) = 0 := by rw [map_sub, huv, sub_self]
    rw [one_tmul_eq_zero_iff, ← mem_smul_top_pi_iff] at h0
    have h1 : v - u ∈ (J • ⊤ : Submodule A (Fin n → R)) :=
      SetLike.le_def.1 (Submodule.smul_mono_left hIJ) h0
    have h2 := Submodule.add_mem _ h1 hu
    rwa [sub_add_cancel] at h2
  · intro hv
    refine Submodule.smul_induction_on (p := fun v => one_tmul I n v ∈
      (J.map (Ideal.Quotient.mk I) • (⊤ : Submodule (A ⧸ I) ((A ⧸ I) ⊗[A] (Fin n → R))))) hv ?_ ?_
    · intro α hα y _
      rw [map_smul, ← algebraMap_smul (A ⧸ I) α (one_tmul I n y), Ideal.Quotient.algebraMap_eq]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hα) Submodule.mem_top
    · intro y₁ y₂ h₁ h₂
      rw [map_add]
      exact Submodule.add_mem _ h₁ h₂

end Vectors

/-! ### The main algebraic statement -/

section Generic

variable {B : Type*} [CommRing B] [IsLocalRing B]

/-- **Flatness of `M = coker` along a flat presentation, in terms of the special fibre.** Let
`Pb →FB Pa →qB M → 0` be exact with `Pa` flat over the local ring `B`, and assume the local flatness
criterion for `M` (`hcrit`). Then `M` is flat iff `FB p ∈ 𝔪 Pa ⇒ FB p ∈ FB (𝔪 Pb)`. -/
theorem flat_iff_smul_condition {Pb Pa M : Type*} [AddCommGroup Pb] [Module B Pb] [AddCommGroup Pa]
    [Module B Pa] [AddCommGroup M] [Module B M] [Module.Flat B Pa]
    (FB : Pb →ₗ[B] Pa) (qB : Pa →ₗ[B] M) (hexB : Exact FB qB) (hqB : Surjective qB)
    (hcrit : Injective ((maximalIdeal B).subtype.lTensor M) → Module.Flat B M) :
    Module.Flat B M ↔ ∀ p, FB p ∈ maximalIdeal B • (⊤ : Submodule B Pa) →
      ∃ p' ∈ maximalIdeal B • (⊤ : Submodule B Pb), FB p = FB p' := by
  let Z := LinearMap.range FB
  have hexZ : Exact Z.subtype qB := by
    intro y
    rw [hexB y]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨⟨FB p, ⟨p, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨_, ⟨p, rfl⟩⟩, rfl⟩
      exact ⟨p, rfl⟩
  have hQiff : (∀ p, FB p ∈ maximalIdeal B • (⊤ : Submodule B Pa) →
      ∃ p' ∈ maximalIdeal B • (⊤ : Submodule B Pb), FB p = FB p') ↔
      ∀ z : Z, Z.subtype z ∈ maximalIdeal B • (⊤ : Submodule B Pa) →
        z ∈ maximalIdeal B • (⊤ : Submodule B Z) := by
    constructor
    · rintro hQ ⟨_, ⟨p, rfl⟩⟩ hz
      obtain ⟨p', hp', hpp'⟩ := hQ p hz
      exact (mem_smul_top_range_iff _ FB _).2 ⟨p', hp', hpp'.symm⟩
    · intro hQ p hp
      obtain ⟨p', hp', hpp'⟩ := (mem_smul_top_range_iff _ FB _).1 (hQ ⟨FB p, ⟨p, rfl⟩⟩ hp)
      exact ⟨p', hp', hpp'.symm⟩
  rw [hQiff, ← lTensor_quotient_injective_iff]
  constructor
  · intro hflat
    exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
      (LinearMap.exact_subtype_mkQ (maximalIdeal B)) (Submodule.mkQ_surjective _) hexZ hqB
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  · intro hinjZ
    have hrinj : Injective (Z.subtype.rTensor (B ⧸ maximalIdeal B)) := by
      rw [← LinearMap.comm_comp_lTensor_comp_comm_eq, LinearMap.coe_comp, LinearMap.coe_comp]
      exact (TensorProduct.comm _ _ _).injective.comp
        (hinjZ.comp (TensorProduct.comm _ _ _).injective)
    exact hcrit (lTensor_injective_of_exact_of_exact_of_rTensor_injective hexZ hqB
      (LinearMap.exact_subtype_mkQ (maximalIdeal B)) (Submodule.mkQ_surjective _) hrinj
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective))

end Generic

section Main

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
  [IsLocalRing A] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing R]
  [IsLocalHom (algebraMap A R)] [Module.Flat A R]

/-- **Flatness of a base-changed cokernel is exactness of the start on the special fibre.**
`F G ≡ 0` and `ker F ⊆ im G` modulo `I R` (`I ≤ 𝔪_A`); then `(A ⧸ I) ⊗_A coker F` is flat over
`A ⧸ I` iff `F v ∈ 𝔪_A R^a ⇒ v ∈ G R^c + 𝔪_A R^b`. -/
theorem flat_quotient_baseChange_coker_iff (I : Ideal A) (hI : I ≤ maximalIdeal A) {a b c : ℕ}
    (F : Matrix (Fin a) (Fin b) R) (G : Matrix (Fin b) (Fin c) R)
    (hcomp : ∀ i k, (F * G) i k ∈ I.map (algebraMap A R))
    (hexact : ∀ v : Fin b → R, (∀ i, (F *ᵥ v) i ∈ I.map (algebraMap A R)) →
      ∃ w : Fin c → R, ∀ j, (v - G *ᵥ w) j ∈ I.map (algebraMap A R)) :
    Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] ((Fin a → R) ⧸ LinearMap.range F.mulVecLin)) ↔
      ∀ v : Fin b → R, (∀ i, (F *ᵥ v) i ∈ (maximalIdeal A).map (algebraMap A R)) →
        ∃ w : Fin c → R, ∀ j, (v - G *ᵥ w) j ∈ (maximalIdeal A).map (algebraMap A R) := by
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hI
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  have : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hm : maximalIdeal (A ⧸ I) = (maximalIdeal A).map (Ideal.Quotient.mk I) :=
    (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  have hImR : I.map (algebraMap A R) ≤ (maximalIdeal A).map (algebraMap A R) := Ideal.map_mono hI
  have : Module.Flat A (Fin a → R) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype A (Fin a) fun _ => R).symm
  let FA : (Fin b → R) →ₗ[A] (Fin a → R) := F.mulVecLin.restrictScalars A
  let qA : (Fin a → R) →ₗ[A] ((Fin a → R) ⧸ LinearMap.range F.mulVecLin) :=
    (LinearMap.range F.mulVecLin).mkQ.restrictScalars A
  let FB := FA.baseChange (A ⧸ I)
  let qB := qA.baseChange (A ⧸ I)
  have hFB : ∀ v, FB (one_tmul I b v) = one_tmul I a (F *ᵥ v) := fun v => rfl
  have hexA : Exact FA qA := by
    intro y
    change Submodule.Quotient.mk y = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  have hqA : Surjective qA := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range F.mulVecLin) y
    exact ⟨x, rfl⟩
  have hexB : Exact FB qB := by
    have h := lTensor_exact (A ⧸ I) hexA hqA
    rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at h
  have hqB : Surjective qB := by
    have h := LinearMap.lTensor_surjective (A ⧸ I) hqA
    rwa [← LinearMap.baseChange_eq_ltensor] at h
  rw [flat_iff_smul_condition FB qB hexB hqB (flat_quotient_baseChange_of_lTensor_injective (R := R) I)]
  constructor
  · intro hQ v hv
    have hz : FB (one_tmul I b v) ∈ maximalIdeal (A ⧸ I) •
        (⊤ : Submodule (A ⧸ I) ((A ⧸ I) ⊗[A] (Fin a → R))) := by
      rw [hFB, hm, one_tmul_mem_smul_iff I hI]
      exact hv
    obtain ⟨q, hq, hqz⟩ := hQ _ hz
    obtain ⟨u, rfl⟩ := one_tmul_surjective I b q
    rw [hm, one_tmul_mem_smul_iff I hI] at hq
    have h0 : one_tmul I a (F *ᵥ (v - u)) = 0 := by
      rw [Matrix.mulVec_sub, map_sub, ← hFB, ← hFB]
      exact sub_eq_zero.2 hqz
    rw [one_tmul_eq_zero_iff] at h0
    obtain ⟨w, hw⟩ := hexact _ h0
    refine ⟨w, fun j => ?_⟩
    have h1 := Ideal.add_mem _ (hImR (hw j)) (hq j)
    convert h1 using 1
    simp only [Pi.sub_apply]
    ring
  · intro hslice p hp
    obtain ⟨v, rfl⟩ := one_tmul_surjective I b p
    rw [hFB, hm, one_tmul_mem_smul_iff I hI] at hp
    obtain ⟨w, hw⟩ := hslice v hp
    refine ⟨one_tmul I b (v - G *ᵥ w), ?_, ?_⟩
    · rw [hm, one_tmul_mem_smul_iff I hI]
      exact hw
    · rw [hFB, hFB, ← sub_eq_zero, ← map_sub, ← Matrix.mulVec_sub, sub_sub_cancel,
        one_tmul_eq_zero_iff, Matrix.mulVec_mulVec]
      intro i
      show ∑ k, (F * G) i k * w k ∈ _
      exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hcomp i k)

end Main

end Hironaka.Analytic.Unibranch.HironakaG10LfChartAlgebra
