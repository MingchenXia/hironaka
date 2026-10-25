import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Submodule

/-!
# Flatness of quotients, colon ideals, and Krull's intersection theorem with a saturation

Three elementary inputs of the descent of flatness along directed unions
(blueprint chapter `sm-flat-descent`, used for Temkin, *Stable modification of relative curves*,
§3.1, where EGA IV₃ 11.2.6 is quoted).

* `inf_le_mul_of_flat_quotient`, `flat_quotient_of_inf_le_mul`: for a ring map `R → P` and an
  ideal `K ⊆ P`, flatness of `P ⧸ K` over `R` gives `K ∩ 𝔟P ⊆ 𝔟K` for every ideal `𝔟 ⊆ R`, and
  conversely when `P` is flat over `R` (blueprint `lem:sm-fd-flat-quotient`).
* `mem_map_colon_of_mul_mem`: if `P` is flat over `R`, `t ∈ R` and `t y ∈ 𝔞P`, then
  `y ∈ (𝔞 : t)P` (blueprint `lem:sm-fd-colon`).
* `exists_sub_pow_mem_smul_eq_zero`: Krull's intersection theorem after inverting an element
  (blueprint `lem:sm-fd-krull`).
-/

open TensorProduct

namespace DeJongAlterations.StableModification.Limits.FlatDescent

section Quotient

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]

/-- The multiplication map `𝔟 ⊗ M → M` of an ideal `𝔟` of `R` and an `R`-module `M`. -/
noncomputable def mulMap (𝔟 : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    𝔟 ⊗[R] M →ₗ[R] M :=
  TensorProduct.lid R M ∘ₗ 𝔟.subtype.rTensor M

@[simp]
lemma mulMap_tmul (𝔟 : Ideal R) {M : Type*} [AddCommGroup M] [Module R M] (r : 𝔟) (m : M) :
    mulMap 𝔟 M (r ⊗ₜ m) = (r : R) • m := by
  simp [mulMap]

lemma mulMap_injective_of_flat (𝔟 : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Flat R M] : Function.Injective (mulMap 𝔟 M) :=
  (TensorProduct.lid R M).injective.comp (Module.Flat.iff_rTensor_injective'.mp inferInstance 𝔟)

lemma mulMap_comp_lTensor (𝔟 : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    mulMap 𝔟 N ∘ₗ f.lTensor 𝔟 = f ∘ₗ mulMap 𝔟 M := by
  ext r m
  simp

/-- Every element of `𝔟 • N` is the image of an element of `𝔟 ⊗ N`. -/
lemma exists_mulMap_eq_of_mem_smul (𝔟 : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) {x : M} (hx : x ∈ 𝔟 • N) :
    ∃ y : 𝔟 ⊗[R] N, N.subtype (mulMap 𝔟 N y) = x := by
  refine Submodule.smul_induction_on (p := fun x => ∃ y : 𝔟 ⊗[R] N, N.subtype (mulMap 𝔟 N y) = x)
    hx (fun r hr n hn => ⟨⟨r, hr⟩ ⊗ₜ ⟨n, hn⟩, by simp⟩) ?_
  rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
  exact ⟨a + b, by simp⟩

/-- The image of the multiplication map `𝔟 ⊗ M → M` lies in `𝔟 • ⊤`. -/
lemma mulMap_mem_smul_top (𝔟 : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    (y : 𝔟 ⊗[R] M) : mulMap 𝔟 M y ∈ 𝔟 • (⊤ : Submodule R M) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => simpa using Submodule.smul_mem_smul r.2 (Submodule.mem_top (x := m))
  | add a b ha hb => simpa using add_mem ha hb

/-- The image of `𝔟 ⊗ K → 𝔟 ⊗ P → P` lies in `𝔟 • K`. -/
lemma mulMap_lTensor_subtype_mem (𝔟 : Ideal R) (K : Ideal P) (z : 𝔟 ⊗[R] K.restrictScalars R) :
    mulMap 𝔟 P ((K.restrictScalars R).subtype.lTensor 𝔟 z) ∈
      𝔟.map (algebraMap R P) * K := by
  have h := mulMap_mem_smul_top 𝔟 (M := K.restrictScalars R) z
  rw [← LinearMap.comp_apply, mulMap_comp_lTensor, LinearMap.comp_apply]
  have hle : (𝔟 • ⊤ : Submodule R (K.restrictScalars R)).map (K.restrictScalars R).subtype ≤
      (𝔟.map (algebraMap R P) * K).restrictScalars R := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, ← Ideal.smul_eq_mul,
      Ideal.smul_restrictScalars]
  exact hle ⟨_, h, rfl⟩

/-- **Lemma `lem:sm-fd-flat-quotient` (1).** If `P ⧸ K` is flat over `R`, then
`K ∩ 𝔟P ⊆ 𝔟K` for every ideal `𝔟` of `R`. -/
theorem inf_le_mul_of_flat_quotient (K : Ideal P) [Module.Flat R (P ⧸ K)] (𝔟 : Ideal R) :
    K ⊓ 𝔟.map (algebraMap R P) ≤ 𝔟.map (algebraMap R P) * K := by
  intro x ⟨hxK, hx𝔟⟩
  have hx : x ∈ 𝔟 • (⊤ : Submodule R P) := by
    rw [Ideal.smul_top_eq_map]; exact hx𝔟
  obtain ⟨y, hy⟩ := exists_mulMap_eq_of_mem_smul 𝔟 ⊤ hx
  let q : P →ₗ[R] P ⧸ K := (Ideal.Quotient.mkₐ R K).toLinearMap
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R K
  -- the element `yt ∈ 𝔟 ⊗ P` with `μ yt = x`
  let yt : 𝔟 ⊗[R] P := (Submodule.subtype ⊤).lTensor 𝔟 y
  have hyt : mulMap 𝔟 P yt = x := by
    rw [← hy, ← LinearMap.comp_apply (mulMap 𝔟 P), mulMap_comp_lTensor]; rfl
  have h0 : q.lTensor 𝔟 yt = 0 := by
    apply mulMap_injective_of_flat 𝔟 (P ⧸ K)
    rw [← LinearMap.comp_apply (mulMap 𝔟 (P ⧸ K)), mulMap_comp_lTensor, LinearMap.comp_apply,
      hyt, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hxK
  have hexact : Function.Exact (K.restrictScalars R).subtype q := by
    intro p
    simp only [q, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Set.mem_range,
      Submodule.coe_subtype, Subtype.exists, exists_prop, exists_eq_right]
    exact Ideal.Quotient.eq_zero_iff_mem
  obtain ⟨z, hz⟩ := (lTensor_exact 𝔟 hexact hq yt).mp h0
  rw [← hyt, ← hz]
  exact mulMap_lTensor_subtype_mem 𝔟 K z

/-- **Lemma `lem:sm-fd-flat-quotient` (2).** If `P` is flat over `R` and `K ∩ 𝔟P ⊆ 𝔟K` for
every ideal `𝔟` of `R`, then `P ⧸ K` is flat over `R`. -/
theorem flat_quotient_of_inf_le_mul [Module.Flat R P] (K : Ideal P)
    (h : ∀ 𝔟 : Ideal R, K ⊓ 𝔟.map (algebraMap R P) ≤ 𝔟.map (algebraMap R P) * K) :
    Module.Flat R (P ⧸ K) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro 𝔟
  suffices hinj : Function.Injective (mulMap 𝔟 (P ⧸ K)) by
    intro a b hab
    apply hinj
    simp only [mulMap, LinearMap.comp_apply, hab]
  rw [injective_iff_map_eq_zero]
  intro y hy
  let q : P →ₗ[R] P ⧸ K := (Ideal.Quotient.mkₐ R K).toLinearMap
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R K
  obtain ⟨yt, rfl⟩ := LinearMap.lTensor_surjective 𝔟 hq y
  set x := mulMap 𝔟 P yt with hxdef
  have hxK : x ∈ K := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := congrArg (fun f => f yt) (mulMap_comp_lTensor 𝔟 q)
    simp only [LinearMap.comp_apply] at this
    rw [hy] at this
    exact this.symm
  have hx𝔟 : x ∈ 𝔟.map (algebraMap R P) := by
    have := mulMap_mem_smul_top 𝔟 yt
    rw [Ideal.smul_top_eq_map] at this
    exact this
  have hmem : x ∈ (𝔟 • K.restrictScalars R : Submodule R P) := by
    rw [← Ideal.smul_restrictScalars, Ideal.smul_eq_mul]
    exact h 𝔟 ⟨hxK, hx𝔟⟩
  obtain ⟨z, hz⟩ := exists_mulMap_eq_of_mem_smul 𝔟 (K.restrictScalars R) hmem
  have hzeq : (K.restrictScalars R).subtype.lTensor 𝔟 z = yt := by
    apply mulMap_injective_of_flat 𝔟 P
    rw [← LinearMap.comp_apply (mulMap 𝔟 P), mulMap_comp_lTensor, LinearMap.comp_apply, hz]
  rw [← hzeq, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  have : q ∘ₗ (K.restrictScalars R).subtype = 0 := by
    ext k
    simp [q, Ideal.Quotient.eq_zero_iff_mem.mpr k.2]
  rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]

end Quotient

section Colon

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]

/-- **Lemma `lem:sm-fd-colon`.** If `P` is a flat `R`-algebra and `t • y ∈ 𝔞P`, then
`y ∈ (𝔞 : t)P`. -/
theorem mem_map_colon_of_mul_mem [Module.Flat R P] (𝔞 : Ideal R) (t : R) {y : P}
    (hy : algebraMap R P t * y ∈ 𝔞.map (algebraMap R P)) :
    y ∈ (𝔞.colon {t}).map (algebraMap R P) := by
  -- the map `r ↦ t r mod 𝔞`, whose kernel is the colon ideal
  let f : R →ₗ[R] R ⧸ 𝔞 := (Submodule.mkQ 𝔞) ∘ₗ LinearMap.mulRight R t
  have hker : LinearMap.ker f = (𝔞.colon {t}).restrictScalars R := by
    ext r
    simp only [f, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulRight_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem,
      Submodule.mem_colon_singleton, smul_eq_mul]
  have hflat := Module.Flat.ker_lTensor_eq (R := R) R P f
  have h1 : (TensorProduct.AlgebraTensorModule.lTensor R P f) (y ⊗ₜ 1) = 0 := by
    simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, f, LinearMap.comp_apply,
      LinearMap.mulRight_apply, one_mul]
    have hy' : t • y ∈ 𝔞 • (⊤ : Submodule R P) := by
      rw [Ideal.smul_top_eq_map, Algebra.smul_def]; exact hy
    have key : ∀ u ∈ 𝔞 • (⊤ : Submodule R P), u ⊗ₜ[R] (Submodule.mkQ 𝔞 (1 : R)) = 0 := by
      intro u hu
      refine Submodule.smul_induction_on (p := fun u => u ⊗ₜ[R] (Submodule.mkQ 𝔞 (1 : R)) = 0)
        hu (fun r hr n _ => ?_) (fun a b ha hb => ?_)
      · rw [TensorProduct.smul_tmul, ← map_smul, smul_eq_mul, mul_one, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero 𝔞).mpr hr, TensorProduct.tmul_zero]
      · rw [TensorProduct.add_tmul, ha, hb, add_zero]
    have ht : (Submodule.mkQ 𝔞) t = t • (Submodule.mkQ 𝔞) (1 : R) := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [ht, ← TensorProduct.smul_tmul]
    exact key _ hy'
  have h2 : y ⊗ₜ[R] (1 : R) ∈ LinearMap.range
      (TensorProduct.AlgebraTensorModule.lTensor R P (LinearMap.ker f).subtype) := by
    rw [← hflat]; exact h1
  obtain ⟨w, hw⟩ := h2
  have hrid : TensorProduct.rid R P (y ⊗ₜ[R] (1 : R)) = y := by simp
  rw [← hrid, ← hw]
  -- the image of `P ⊗ ker f → P` lies in `(ker f) • ⊤`
  have : ∀ w : P ⊗[R] LinearMap.ker f,
      TensorProduct.rid R P ((TensorProduct.AlgebraTensorModule.lTensor R P
        (LinearMap.ker f).subtype) w) ∈ (𝔞.colon {t}).map (algebraMap R P) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul p c =>
      simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, Submodule.coe_subtype,
        TensorProduct.rid_tmul]
      have hc : (c : R) ∈ (𝔞.colon {t}).restrictScalars R := hker ▸ c.2
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc)
    | add a b ha hb => simpa using add_mem ha hb
  exact this w

end Colon

section Krull

variable {P L : Type*} [CommRing P] [AddCommGroup L] [Module P L]

/-- The image of `𝔞^n • ⊤` in a localization lies in `(𝔞 Pₛ)^n • ⊤`. -/
lemma mkLinearMap_mem_pow_smul_top (S : Submonoid P) (𝔞 : Ideal P) (n : ℕ) {y : L}
    (hy : y ∈ 𝔞 ^ n • (⊤ : Submodule P L)) :
    LocalizedModule.mkLinearMap S L y ∈
      (𝔞.map (algebraMap P (Localization S))) ^ n •
        (⊤ : Submodule (Localization S) (LocalizedModule S L)) := by
  refine Submodule.smul_induction_on (p := fun y => LocalizedModule.mkLinearMap S L y ∈
      (𝔞.map (algebraMap P (Localization S))) ^ n •
        (⊤ : Submodule (Localization S) (LocalizedModule S L))) hy (fun r hr m _ => ?_)
    (fun a b ha hb => ?_)
  · rw [map_smul, ← algebraMap_smul (Localization S) r]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hr
  · rw [map_add]; exact add_mem ha hb

/-- **Lemma `lem:sm-fd-krull`.** Krull's intersection theorem after inverting `α`: if for every
`n` some `α ^ k • x` lies in `𝔞 ^ n • L`, then some `s ≡ α ^ N (mod 𝔞)` kills `x`. -/
theorem exists_sub_pow_mem_smul_eq_zero [IsNoetherianRing P] [Module.Finite P L] (𝔞 : Ideal P)
    (α : P) (x : L) (hx : ∀ n : ℕ, ∃ k : ℕ, α ^ k • x ∈ 𝔞 ^ n • (⊤ : Submodule P L)) :
    ∃ (N : ℕ) (s : P), s - α ^ N ∈ 𝔞 ∧ s • x = 0 := by
  let S := Submonoid.powers α
  let Pα := Localization S
  let 𝔞' : Ideal Pα := 𝔞.map (algebraMap P Pα)
  let x' : LocalizedModule S L := LocalizedModule.mkLinearMap S L x
  have hmem : x' ∈ (⨅ i : ℕ, 𝔞' ^ i • ⊤ : Submodule Pα (LocalizedModule S L)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨k, hk⟩ := hx n
    have h1 := mkLinearMap_mem_pow_smul_top S 𝔞 n hk
    let sk : S := ⟨α ^ k, pow_mem (Submonoid.mem_powers α) k⟩
    have hxk : x' = (Localization.mk (1 : P) sk : Pα) •
        LocalizedModule.mkLinearMap S L (α ^ k • x) := by
      simp only [x', LocalizedModule.mkLinearMap_apply]
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one, LocalizedModule.mk_eq]
      exact ⟨1, by simp [sk, Submonoid.smul_def]⟩
    rw [hxk]
    exact Submodule.smul_mem _ _ h1
  obtain ⟨⟨r, hr⟩, hrx⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff 𝔞' x').mp hmem
  obtain ⟨⟨⟨c, hc⟩, ⟨s, hs⟩⟩, hrc⟩ := (IsLocalization.mem_map_algebraMap_iff S Pα).mp hr
  obtain ⟨M, rfl⟩ := hs
  simp only at hrc
  -- `(α ^ M - c) • x' = 0`
  have hzero : LocalizedModule.mkLinearMap S L ((α ^ M - c) • x) = 0 := by
    rw [map_smul, ← algebraMap_smul Pα, map_sub, sub_smul, ← hrc, mul_comm, mul_smul,
      hrx, sub_self]
  obtain ⟨⟨u, hu⟩, hM'⟩ := (IsLocalizedModule.eq_zero_iff S _).mp hzero
  obtain ⟨M', rfl⟩ := hu
  refine ⟨M' + M, α ^ M' * (α ^ M - c), ?_, ?_⟩
  · have : α ^ M' * (α ^ M - c) - α ^ (M' + M) = -(α ^ M' * c) := by ring
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ hc)
  · rw [mul_smul]
    simpa [Submonoid.smul_def] using hM'

end Krull

end DeJongAlterations.StableModification.Limits.FlatDescent
