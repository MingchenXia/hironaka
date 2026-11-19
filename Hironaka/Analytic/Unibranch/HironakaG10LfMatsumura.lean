import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The local flatness criterion without `Tor` (Matsumura, Th. 22.3, (3) ⇒ (1)) — lane G10LF, item 1a

Let `B → C` be a local homomorphism of Noetherian local rings and `M` a finite `C`-module. If
`𝔪_B ⊗_B M → M` is injective (i.e. `Tor₁^B(B/𝔪_B, M) = 0`), then `M` is flat over `B`
(**`flat_of_maximalIdeal_lTensor_injective`**, and the `rTensor` form
**`flat_of_maximalIdeal_rTensor_injective`**).

The proof avoids `Tor` (mathlib has no usable `Tor` API). `Acyc B M X` is the Tor-free statement
"`Tor₁^B(X, M) = 0`": for every short exact sequence `0 → A → E → X → 0`, the map `M ⊗ A → M ⊗ E` is
injective. Then:
* (1a.i) `Acyc` holds for `0`, is invariant under isomorphism, closed under extensions
  (`acyc_of_submodule`), and holds for the residue field (`acyc_of_cyclic`, a pushout diagram chase
  from the hypothesis). By Noetherian induction on ideals (socle elements), `Acyc B M (B ⧸ J)` for every
  `J ⊇ 𝔪ⁿ` (`acyc_quotient`).
* (1a.ii) For an ideal `I`, an element `x` of the kernel of `M ⊗ I → M` lies in the image of
  `M ⊗ (I ∩ 𝔪ⁿ)` for every `n` (`mem_range_of_lTensor_eq_zero`, via `B/𝔪ⁿ`), hence by Artin–Rees in
  `𝔪ᵏ (M ⊗ I)` for every `k`. `M ⊗_B I` is a finite `C`-module and `𝔪_B C ⊆ 𝔪_C`, so Krull's
  intersection theorem over `C` gives `x = 0`.
* (1a.iii) Flatness by ideals (`Module.Flat.iff_lTensor_injective'`).

Reference: Matsumura, *Commutative Ring Theory*, Th. 22.3. No named input.
BP: hironaka-g10lf-local-flatness.tex.
-/

set_option autoImplicit false

open Function TensorProduct IsLocalRing

namespace Hironaka.Analytic.Unibranch.HironakaG10LfMatsumura

universe uB uM

section Acyc

variable {B : Type uB} [CommRing B] (M : Type uM) [AddCommGroup M] [Module B M]

variable (B) in
/-- Tor-free form of `Tor₁^B(X, M) = 0`: for every short exact sequence `0 → A → E → X → 0` (with
`A`, `E` in the universe of `B`), `M ⊗ A → M ⊗ E` is injective. -/
def Acyc (X : Type*) [AddCommGroup X] [Module B X] : Prop :=
  ∀ ⦃A E : Type uB⦄ [AddCommGroup A] [Module B A] [AddCommGroup E] [Module B E]
    (f : A →ₗ[B] E) (g : E →ₗ[B] X), Injective f → Exact f g → Surjective g →
      Injective (f.lTensor M)

/-- `lTensor` of a bijective linear map is injective. -/
theorem lTensor_injective_of_bijective {N P : Type*} [AddCommGroup N] [Module B N] [AddCommGroup P]
    [Module B P] (f : N →ₗ[B] P) (hf : Bijective f) : Injective (f.lTensor M) := by
  have h2 : ((LinearEquiv.ofBijective f hf : N ≃ₗ[B] P) : N →ₗ[B] P) = f := LinearMap.ext fun _ => rfl
  have h3 : f.lTensor M = ((LinearEquiv.ofBijective f hf).lTensor M : M ⊗[B] N →ₗ[B] M ⊗[B] P) := by
    rw [LinearEquiv.coe_lTensor, h2]
  rw [h3]
  exact ((LinearEquiv.ofBijective f hf).lTensor M).injective

theorem acyc_of_subsingleton (X : Type*) [AddCommGroup X] [Module B X] [Subsingleton X] :
    Acyc B M X := by
  intro A E _ _ _ _ f g hf hfg _
  exact lTensor_injective_of_bijective M f ⟨hf, fun e => (hfg e).1 (Subsingleton.elim _ _)⟩

theorem Acyc.of_equiv {X X' : Type*} [AddCommGroup X] [Module B X] [AddCommGroup X'] [Module B X']
    {M} [AddCommGroup M] [Module B M] (h : Acyc B M X) (e : X ≃ₗ[B] X') : Acyc B M X' := by
  intro A E _ _ _ _ f g hf hfg hg
  refine h f (e.symm.toLinearMap.comp g) hf (fun y => ?_) (e.symm.surjective.comp hg)
  change e.symm (g y) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact hfg y

/-- **Extensions.** If `X₁ ≤ X` with `Acyc X₁` and `Acyc (X ⧸ X₁)`, then `Acyc X`. -/
theorem acyc_of_submodule {X : Type*} [AddCommGroup X] [Module B X] (X₁ : Submodule B X)
    (h₁ : Acyc B M X₁) (h₂ : Acyc B M (X ⧸ X₁)) : Acyc B M X := by
  intro A E _ _ _ _ f g hf hfg hg
  let E₁ : Submodule B E := X₁.comap g
  have hfE : ∀ a, f a ∈ E₁ := fun a => by
    change g (f a) ∈ X₁
    rw [hfg.apply_apply_eq_zero]
    exact X₁.zero_mem
  let f' : A →ₗ[B] E₁ := LinearMap.codRestrict E₁ f hfE
  let g' : E₁ →ₗ[B] X₁ := LinearMap.codRestrict X₁ (g.comp E₁.subtype) (fun e => e.2)
  have hf' : Injective f' := fun a a' h => hf (congrArg Subtype.val h)
  have hfg' : Exact f' g' := by
    intro e
    constructor
    · intro he
      obtain ⟨a, ha⟩ := (hfg e).1 (congrArg Subtype.val he)
      exact ⟨a, Subtype.ext ha⟩
    · rintro ⟨a, rfl⟩
      exact Subtype.ext (hfg.apply_apply_eq_zero a)
  have hg' : Surjective g' := by
    intro y
    obtain ⟨e, he⟩ := hg y
    refine ⟨⟨e, ?_⟩, Subtype.ext he⟩
    change g e ∈ X₁
    rw [he]
    exact y.2
  have i₁ := h₁ f' g' hf' hfg' hg'
  have hex₂ : Exact E₁.subtype (X₁.mkQ.comp g) := by
    intro e
    change Submodule.Quotient.mk (g e) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro he
      exact ⟨⟨e, he⟩, rfl⟩
    · rintro ⟨e', rfl⟩
      exact e'.2
  have i₂ := h₂ E₁.subtype (X₁.mkQ.comp g) E₁.injective_subtype hex₂
    ((Submodule.mkQ_surjective X₁).comp hg)
  have hcomp : f.lTensor M = (E₁.subtype.lTensor M).comp (f'.lTensor M) := by
    rw [← LinearMap.lTensor_comp, LinearMap.subtype_comp_codRestrict]
  rw [hcomp, LinearMap.coe_comp]
  exact i₂.comp i₁

variable [IsLocalRing B]

/-- **The residue field (and `0`).** A cyclic module killed by `𝔪` is `Acyc`, given
`𝔪 ⊗ M → M` injective. (Pushout diagram chase, no `Tor`.) -/
theorem acyc_of_cyclic (h : Injective ((maximalIdeal B).subtype.lTensor M))
    {X : Type*} [AddCommGroup X] [Module B X] (x : X) (hgen : ∀ y : X, ∃ b : B, b • x = y)
    (hm : ∀ b ∈ maximalIdeal B, b • x = 0) : Acyc B M X := by
  by_cases hx : x = 0
  · have : Subsingleton X := ⟨fun y y' => by
      obtain ⟨b, rfl⟩ := hgen y
      obtain ⟨b', rfl⟩ := hgen y'
      rw [hx, smul_zero, smul_zero]⟩
    exact acyc_of_subsingleton M X
  intro A E _ _ _ _ f g hf hfg hg
  obtain ⟨e, he⟩ := hg x
  have hann : ∀ b : B, b • x = 0 → b ∈ maximalIdeal B := by
    intro b hb
    by_contra hb'
    obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.1 hb'
    apply hx
    rw [← inv_smul_smul u x, Units.smul_def u x, hb, smul_zero]
  let v : (A × B) →ₗ[B] E := f.coprod (LinearMap.toSpanSingleton B E e)
  have hv_apply : ∀ p : A × B, v p = f p.1 + p.2 • e := fun p => rfl
  have hv : Surjective v := by
    intro y
    obtain ⟨b, hb⟩ := hgen (g y)
    have h0 : g (y - b • e) = 0 := by rw [map_sub, map_smul, he, hb, sub_self]
    obtain ⟨a, ha⟩ := (hfg _).1 h0
    refine ⟨(a, b), ?_⟩
    rw [hv_apply, ha, sub_add_cancel]
  let K := LinearMap.ker v
  have hK : ∀ p : K, f (p : A × B).1 + (p : A × B).2 • e = 0 := fun p => by
    rw [← hv_apply]
    exact p.2
  have hKm : ∀ p : K, (p : A × B).2 ∈ maximalIdeal B := by
    intro p
    apply hann
    have h1 := congrArg g (hK p)
    rwa [map_add, map_smul, hfg.apply_apply_eq_zero, he, zero_add, map_zero] at h1
  let σ : K →ₗ[B] maximalIdeal B :=
    LinearMap.codRestrict (maximalIdeal B) ((LinearMap.snd B A B).comp K.subtype) hKm
  have hσ : Bijective σ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro p hp
      have h2 : (p : A × B).2 = 0 := congrArg Subtype.val hp
      have hp' := hK p
      rw [h2, zero_smul, add_zero] at hp'
      have h1 : (p : A × B).1 = 0 := hf (by rw [hp', map_zero])
      exact Subtype.ext (Prod.ext h1 h2)
    · rintro ⟨b, hb⟩
      have h0 : g (b • e) = 0 := by rw [map_smul, he, hm b hb]
      obtain ⟨a, ha⟩ := (hfg _).1 h0
      have hmem : ((-a, b) : A × B) ∈ K := by
        change v (-a, b) = 0
        rw [hv_apply, map_neg, ha, neg_add_cancel]
      exact ⟨⟨(-a, b), hmem⟩, rfl⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hvz : v.lTensor M ((LinearMap.inl B A B).lTensor M z) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, LinearMap.coprod_inl]
    exact hz
  obtain ⟨w, hw⟩ := (lTensor_exact M (LinearMap.exact_subtype_ker_map v) hv _).1 hvz
  have hsnd : (maximalIdeal B).subtype.comp σ = (LinearMap.snd B A B).comp K.subtype :=
    LinearMap.subtype_comp_codRestrict _ _ _
  have hσw : σ.lTensor M w = 0 := by
    apply h
    rw [← LinearMap.lTensor_comp_apply, map_zero, hsnd,
      LinearMap.lTensor_comp_apply, hw, ← LinearMap.lTensor_comp_apply, LinearMap.snd_comp_inl,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  have hw0 : w = 0 := lTensor_injective_of_bijective M σ hσ (by rw [hσw, map_zero])
  have hz' : z = (LinearMap.fst B A B).lTensor M ((LinearMap.inl B A B).lTensor M z) := by
    rw [← LinearMap.lTensor_comp_apply, LinearMap.fst_comp_inl, LinearMap.lTensor_id,
      LinearMap.id_apply]
  rw [hz', ← hw, hw0, map_zero, map_zero]

/-- A socle element: if `J ≠ ⊤` contains a power of `𝔪`, some `x ∉ J` has `𝔪 x ⊆ J`. -/
theorem exists_socle {J : Ideal B} (hJ : J ≠ ⊤) {n : ℕ} (hn : maximalIdeal B ^ n ≤ J) :
    ∃ x : B, x ∉ J ∧ ∀ b ∈ maximalIdeal B, b * x ∈ J := by
  classical
  have hP : ∃ j, maximalIdeal B ^ j ≤ J := ⟨n, hn⟩
  have hj₀le : maximalIdeal B ^ Nat.find hP ≤ J := Nat.find_spec hP
  have hj₀ne : Nat.find hP ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at hj₀le
    exact hJ hj₀le
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hj₀ne
  have hnot : ¬ maximalIdeal B ^ j ≤ J := Nat.find_min hP (by omega)
  obtain ⟨x, hx, hxJ⟩ := SetLike.not_le_iff_exists.1 hnot
  refine ⟨x, hxJ, fun b hb => hj₀le ?_⟩
  rw [hj, pow_succ']
  exact Ideal.mul_mem_mul hb hx

variable [IsNoetherianRing B]

/-- **(1a.i) Finite length.** `Acyc B M (B ⧸ J)` for every ideal `J` containing a power of `𝔪`. -/
theorem acyc_quotient (h : Injective ((maximalIdeal B).subtype.lTensor M)) :
    ∀ J : Ideal B, (∃ n, maximalIdeal B ^ n ≤ J) → Acyc B M (B ⧸ J) := by
  intro J
  refine IsNoetherian.induction (P := fun J : Ideal B => (∃ n, maximalIdeal B ^ n ≤ J) →
    Acyc B M (B ⧸ J)) (fun J ih => ?_) J
  rintro ⟨n, hn⟩
  by_cases hJ : J = ⊤
  · have : Subsingleton (B ⧸ J) := Ideal.Quotient.subsingleton_iff.2 hJ
    exact acyc_of_subsingleton M _
  obtain ⟨x, hxJ, hxm⟩ := exists_socle hJ hn
  let J' : Ideal B := J ⊔ Submodule.span B {x}
  have hJJ' : J < J' := lt_of_le_of_ne le_sup_left fun heq => hxJ (by
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
  have h' : Acyc B M (B ⧸ J') := ih J' hJJ' ⟨n, hn.trans le_sup_left⟩
  let X₁ : Submodule B (B ⧸ J) := Submodule.span B {Submodule.mkQ J x}
  let x₁ : X₁ := ⟨Submodule.mkQ J x, Submodule.mem_span_singleton_self _⟩
  have h₁ : Acyc B M X₁ := by
    refine acyc_of_cyclic M h x₁ (fun y => ?_) (fun b hb => ?_)
    · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 y.2
      exact ⟨a, Subtype.ext ha⟩
    · apply Subtype.ext
      change b • Submodule.mkQ J x = 0
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact hxm b hb
  have hmap : Submodule.map J.mkQ J' = X₁ := by
    change (J ⊔ Submodule.span B {x}).map J.mkQ = _
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span,
      Set.image_singleton]
  have h₂ : Acyc B M ((B ⧸ J) ⧸ X₁) := by
    rw [← hmap]
    exact h'.of_equiv (Submodule.quotientQuotientEquivQuotient J J' le_sup_left).symm
  exact acyc_of_submodule M X₁ h₁ h₂

/-- **(1a.ii), finite level.** If `x ∈ M ⊗ I` maps to `0` in `M ⊗ B`, then for every `n` it comes from
`M ⊗ (I ∩ 𝔪ⁿ)`. -/
theorem mem_range_of_lTensor_eq_zero (h : Injective ((maximalIdeal B).subtype.lTensor M))
    (I : Ideal B) (n : ℕ) (x : M ⊗[B] I) (hx : I.subtype.lTensor M x = 0) :
    x ∈ LinearMap.range ((Submodule.comap I.subtype (maximalIdeal B ^ n)).subtype.lTensor M) := by
  set N : Ideal B := maximalIdeal B ^ n with hN
  set K : Submodule B I := Submodule.comap I.subtype N with hK
  let f : (I ⧸ K) →ₗ[B] (B ⧸ N) := K.mapQ N I.subtype le_rfl
  let g : (B ⧸ N) →ₗ[B] (B ⧸ (I ⊔ N)) := N.mapQ (I ⊔ N) LinearMap.id
    (fun y hy => Submodule.mem_sup_right hy)
  have hf : Injective f := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective K y
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hy
  have hg : Surjective g := by
    intro z
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (I ⊔ N) z
    exact ⟨Submodule.mkQ N b, rfl⟩
  have hfg : Exact f g := by
    intro e
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective N e
    change Submodule.Quotient.mk b = (0 : B ⧸ (I ⊔ N)) ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hb
      obtain ⟨i, hi, m, hm, rfl⟩ := Submodule.mem_sup.1 hb
      refine ⟨Submodule.mkQ K ⟨i, hi⟩, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      change i - (i + m) ∈ N
      rw [sub_add_cancel_left]
      exact N.neg_mem hm
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective K y
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        at hy
      have hb : b = (y : B) - ((y : B) - b) := by abel
      rw [hb]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left y.2) (Submodule.mem_sup_right hy)
  have hacyc : Acyc B M (B ⧸ (I ⊔ N)) := acyc_quotient M h (I ⊔ N) ⟨n, le_sup_right⟩
  have hinj := hacyc f g hf hfg hg
  have hcomm : f.comp K.mkQ = N.mkQ.comp I.subtype := Submodule.mapQ_mkQ _ _ _
  have hy : (K.mkQ.lTensor M) x = 0 := by
    apply hinj
    rw [← LinearMap.lTensor_comp_apply, hcomm, LinearMap.lTensor_comp_apply, hx, map_zero, map_zero]
  exact (lTensor_exact M (LinearMap.exact_subtype_mkQ K) (Submodule.mkQ_surjective K) x).1 hy

omit [IsLocalRing B] in
/-- **Artin–Rees**, in `I`: `I ∩ 𝔞^{k+c} ⊆ 𝔞ᵏ I`. -/
theorem exists_comap_pow_le (𝔞 I : Ideal B) :
    ∃ c, ∀ k, Submodule.comap I.subtype (𝔞 ^ (k + c)) ≤ 𝔞 ^ k • (⊤ : Submodule B I) := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔞 (M := B) I
  refine ⟨c, fun k y hy => ?_⟩
  have h0 : (y : B) ∈ 𝔞 ^ (k + c) • (⊤ : Submodule B B) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hy
  have h1 : (y : B) ∈ 𝔞 ^ (k + c) • (⊤ : Submodule B B) ⊓ I := ⟨h0, y.2⟩
  rw [hc (k + c) (by omega), Nat.add_sub_cancel] at h1
  have h2 : (y : B) ∈ 𝔞 ^ k • I := SetLike.le_def.1 (smul_mono_right _ inf_le_right) h1
  have h3 : 𝔞 ^ k • I = (𝔞 ^ k • (⊤ : Submodule B I)).map I.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [h3] at h2
  obtain ⟨y', hy', hyy'⟩ := h2
  rwa [← Subtype.ext hyy']

end Acyc

section Krull

variable {B : Type uB} [CommRing B] {C : Type*} [CommRing C] [Algebra B C]
  (M : Type uM) [AddCommGroup M] [Module B M] [Module C M] [IsScalarTower B C M]

/-- The image of `M ⊗ (𝔞ᵏ I)` in `M ⊗ I` lies in `(𝔞 C)ᵏ (M ⊗ I)`. -/
theorem mem_smul_top_of_mem_range (𝔞 I : Ideal B) (k : ℕ) (x : M ⊗[B] I)
    (hx : x ∈ LinearMap.range ((𝔞 ^ k • (⊤ : Submodule B I)).subtype.lTensor M)) :
    x ∈ (𝔞.map (algebraMap B C)) ^ k • (⊤ : Submodule C (M ⊗[B] I)) := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul m y =>
    obtain ⟨y, hy⟩ := y
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
    refine Submodule.smul_induction_on (p := fun y : I => m ⊗ₜ[B] y ∈
      (𝔞.map (algebraMap B C)) ^ k • (⊤ : Submodule C (M ⊗[B] I))) hy ?_ ?_
    · intro b hb y' _
      rw [TensorProduct.tmul_smul, ← algebraMap_smul C b (m ⊗ₜ[B] y')]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hb
    · intro y₁ y₂ h₁ h₂
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ h₁ h₂
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add]
    exact Submodule.add_mem _ h₁ h₂

/-- `M ⊗_B I` is a finite `C`-module. -/
theorem finite_tensor [IsNoetherianRing B] [Module.Finite C M] (I : Ideal B) :
    Module.Finite C (M ⊗[B] I) :=
  Module.Finite.equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange B C C M I)

variable [IsLocalRing B] [IsLocalRing C] [IsNoetherianRing B] [IsNoetherianRing C]
  [IsLocalHom (algebraMap B C)] [Module.Finite C M]

include C in
/-- **Local flatness criterion (Matsumura Th. 22.3), `lTensor` form.** -/
theorem flat_of_maximalIdeal_lTensor_injective
    (h : Injective ((maximalIdeal B).subtype.lTensor M)) : Module.Flat B M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, hc⟩ := exists_comap_pow_le (maximalIdeal B) I
  have hmem : ∀ k, x ∈ ((maximalIdeal B).map (algebraMap B C)) ^ k •
      (⊤ : Submodule C (M ⊗[B] I)) := by
    intro k
    apply mem_smul_top_of_mem_range M (maximalIdeal B) I k x
    obtain ⟨w, rfl⟩ := mem_range_of_lTensor_eq_zero M h I (k + c) x hx
    refine ⟨(Submodule.inclusion (hc k)).lTensor M w, ?_⟩
    rw [← LinearMap.lTensor_comp_apply, Submodule.subtype_comp_inclusion]
  have := finite_tensor (C := C) M I
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing ((maximalIdeal B).map (algebraMap B C))
    (M := M ⊗[B] I) (ne_top_of_lt (IsLocalRing.map_maximalIdeal_lt_top (algebraMap B C)))
  have hx' : x ∈ (⨅ i : ℕ, ((maximalIdeal B).map (algebraMap B C)) ^ i •
      ⊤ : Submodule C (M ⊗[B] I)) := Submodule.mem_iInf _ |>.2 hmem
  rw [hK] at hx'
  exact (Submodule.mem_bot C).1 hx'

include C in
/-- **Local flatness criterion (Matsumura Th. 22.3, (3) ⇒ (1)), Tor-free.** `B → C` local
homomorphism of Noetherian local rings, `M` a finite `C`-module: if `𝔪_B ⊗_B M → M` is injective,
then `M` is flat over `B`. -/
theorem flat_of_maximalIdeal_rTensor_injective
    (h : Injective ((maximalIdeal B).subtype.rTensor M)) : Module.Flat B M := by
  apply flat_of_maximalIdeal_lTensor_injective (C := C)
  rw [← LinearMap.comm_comp_rTensor_comp_comm_eq, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (TensorProduct.comm B B M).injective.comp (h.comp (TensorProduct.comm B M _).injective)

end Krull

end Hironaka.Analytic.Unibranch.HironakaG10LfMatsumura
