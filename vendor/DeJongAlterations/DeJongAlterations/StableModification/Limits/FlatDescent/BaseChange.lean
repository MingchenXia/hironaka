import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Base change of Tor over a generically flat stratum

Let `𝔭` be an ideal of a ring `R₀` and `a ∈ R₀`.

* `exists_pow_smul_eq_zero_of_lTensor_eq_zero`: if `0 → X → Y → Z → 0` is an exact sequence of
  `R₀ ⧸ 𝔭`-modules and `Z` becomes flat over `R₀ ⧸ 𝔭` after inverting `a`, then for every
  `R₀`-module `N` the kernel of `N ⊗ X → N ⊗ Y` is killed by powers of `a`
  (blueprint `lem:sm-fd-tor-torsion`).
* `exists_pow_smul_mem_of_mem_map`: for an `R₀`-algebra `P₀` and an ideal `J₀ ⊆ P₀` such that
  `(R₀/𝔭 ⊗ P₀) / J₀` becomes flat over `R₀/𝔭` after inverting `a`, every element of
  `J₀ (A ⊗ P₀) ∩ 𝔟 (A ⊗ P₀)` (for an `R₀`-algebra `A` and an ideal `𝔟 ⊇ 𝔭A`) is multiplied by a
  power of `a` into any ideal `𝔇` containing `𝔟 J₀(A ⊗ P₀)` and the elements `1 ⊗ e`,
  `e ∈ J₀ ∩ 𝔭P₀` (blueprint `lem:sm-fd-base-change`). This is the base change of Tor used in the
  local criterion of flatness (Stacks 00ML, proof of 00R6).

Blueprint chapter `sm-flat-descent.tex`.
-/

open TensorProduct

namespace DeJongAlterations.StableModification.Limits.FlatDescent

section Tor

variable {R : Type*} [CommRing R] (𝔭 : Ideal R) (a : R)

/-- **Lemma `lem:sm-fd-tor-torsion`.** Let `0 → X → Y → Z → 0` be exact over `R ⧸ 𝔭` with
`Z` flat over `R ⧸ 𝔭` after inverting `a`. Then every element of the kernel of
`N ⊗[R] X → N ⊗[R] Y` is killed by a power of `a`. -/
theorem exists_pow_smul_eq_zero_of_lTensor_eq_zero {X Y Z : Type*} [AddCommGroup X]
    [AddCommGroup Y] [AddCommGroup Z] [Module (R ⧸ 𝔭) X] [Module (R ⧸ 𝔭) Y] [Module (R ⧸ 𝔭) Z]
    [Module R X] [Module R Y] [IsScalarTower R (R ⧸ 𝔭) X] [IsScalarTower R (R ⧸ 𝔭) Y]
    (f : X →ₗ[R ⧸ 𝔭] Y) (g : Y →ₗ[R ⧸ 𝔭] Z) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.Flat (R ⧸ 𝔭) (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk 𝔭 a)) Z)]
    (N : Type*) [AddCommGroup N] [Module R N] (z : N ⊗[R] X)
    (hz : (f.restrictScalars R).lTensor N z = 0) : ∃ k : ℕ, a ^ k • z = 0 := by
  set Rb := R ⧸ 𝔭
  set S := Submonoid.powers (Ideal.Quotient.mk 𝔭 a)
  let Nb := Rb ⊗[R] N
  -- `N ⊗[R] W ≃ W ⊗[Rb] Nb` for the `Rb`-modules `W = X, Y`
  let EX : N ⊗[R] X ≃ₗ[R] X ⊗[Rb] Nb := (TensorProduct.comm R N X).trans
    ((AlgebraTensorModule.cancelBaseChange R Rb Rb X N).symm.restrictScalars R)
  let EY : N ⊗[R] Y ≃ₗ[R] Y ⊗[Rb] Nb := (TensorProduct.comm R N Y).trans
    ((AlgebraTensorModule.cancelBaseChange R Rb Rb Y N).symm.restrictScalars R)
  have hEX : ∀ (n : N) (w : X), EX (n ⊗ₜ w) = w ⊗ₜ ((1 : Rb) ⊗ₜ n) := by
    intro n w
    simp [EX, AlgebraTensorModule.cancelBaseChange_symm_tmul]
  have hEY : ∀ (n : N) (w : Y), EY (n ⊗ₜ w) = w ⊗ₜ ((1 : Rb) ⊗ₜ n) := by
    intro n w
    simp [EY, AlgebraTensorModule.cancelBaseChange_symm_tmul]
  have hnat : ∀ z : N ⊗[R] X, EY ((f.restrictScalars R).lTensor N z) = f.rTensor Nb (EX z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul n x => rw [LinearMap.lTensor_tmul, hEY, hEX, LinearMap.rTensor_tmul]; rfl
    | add u v hu hv => simp only [map_add, hu, hv]
  have hw : f.rTensor Nb (EX z) = 0 := by rw [← hnat, hz, map_zero]
  -- localize at the powers of `a`
  let fS : LocalizedModule S X →ₗ[Rb] LocalizedModule S Y :=
    (LocalizedModule.map S f).restrictScalars Rb
  let gS : LocalizedModule S Y →ₗ[Rb] LocalizedModule S Z :=
    (LocalizedModule.map S g).restrictScalars Rb
  have hfS : Function.Injective fS := LocalizedModule.map_injective S f hf
  have hgS : Function.Surjective gS := LocalizedModule.map_surjective S g hg
  have hfgS : Function.Exact fS gS := LocalizedModule.map_exact S f g hfg
  have hinj : Function.Injective (fS.rTensor Nb) :=
    (fS.lTensor_inj_iff_rTensor_inj Nb).mp
      (LinearMap.lTensor_injective_of_exact_of_flat gS hgS fS hfS hfgS Nb)
  let mX : X →ₗ[Rb] LocalizedModule S X := LocalizedModule.mkLinearMap S X
  let mY : Y →ₗ[Rb] LocalizedModule S Y := LocalizedModule.mkLinearMap S Y
  have hcomm : fS ∘ₗ mX = mY ∘ₗ f := by
    ext x
    simp [fS, mX, mY, LocalizedModule.map_mk]
  have h0 : mX.rTensor Nb (EX z) = 0 := by
    apply hinj
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hcomm, LinearMap.rTensor_comp,
      LinearMap.comp_apply, hw, map_zero, map_zero]
  have hloc : IsLocalizedModule S (AlgebraTensorModule.rTensor Rb Nb mX) :=
    IsLocalizedModule.rTensor Rb S mX
  obtain ⟨⟨s, hs⟩, hsz⟩ := (IsLocalizedModule.eq_zero_iff S
    (AlgebraTensorModule.rTensor Rb Nb mX)).mp h0
  obtain ⟨k, rfl⟩ := hs
  refine ⟨k, ?_⟩
  apply EX.injective
  rw [map_smul, map_zero, ← algebraMap_smul Rb (a ^ k), map_pow, Ideal.Quotient.algebraMap_eq]
  simpa [Submonoid.smul_def] using hsz

end Tor

section BaseChange

/-- `TensorProduct.map_ker` with the maps as explicit arguments. -/
lemma ker_map_eq_sup {R N P N' P' : Type*} [CommRing R] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup N'] [AddCommGroup P'] [Module R N] [Module R P] [Module R N'] [Module R P']
    (g : N →ₗ[R] P) (g' : N' →ₗ[R] P') (hg : Function.Surjective g)
    (hg' : Function.Surjective g') :
    LinearMap.ker (TensorProduct.map g g') =
      LinearMap.range ((LinearMap.ker g').subtype.lTensor N) ⊔
        LinearMap.range ((LinearMap.ker g).subtype.rTensor N') :=
  TensorProduct.map_ker (LinearMap.exact_subtype_ker_map g) hg
    (LinearMap.exact_subtype_ker_map g') hg'

variable {R₀ : Type*} [CommRing R₀] {P₀ : Type*} [CommRing P₀] [Algebra R₀ P₀]
  (J₀ : Ideal P₀) (𝔭 : Ideal R₀) (a : R₀)
  {B : Type*} [CommRing B] [Algebra R₀ B] (ι : P₀ →ₐ[R₀] B) (hι : Function.Surjective ι)
  (hιker : ∀ e : P₀, ι e = 0 → e ∈ 𝔭.map (algebraMap R₀ P₀))

/-- The surjection `J₀ → J₀ B`, `e ↦ ι e`. -/
noncomputable def toMapIdeal : J₀.restrictScalars R₀ →ₗ[R₀] J₀.map ι where
  toFun e := ⟨ι e, Ideal.mem_map_of_mem _ e.2⟩
  map_add' e e' := by ext; simp
  map_smul' r e := by ext; simp

include hι in
lemma toMapIdeal_surjective : Function.Surjective (toMapIdeal J₀ ι) := by
  rintro ⟨w, hw⟩
  obtain ⟨e, he, rfl⟩ := (Ideal.mem_map_iff_of_surjective ι hι).mp hw
  exact ⟨⟨e, he⟩, rfl⟩

variable (A : Type*) [CommRing A] [Algebra R₀ A]

/-- `a' ⊗ e = (a' ⊗ 1) (1 ⊗ e)`. -/
lemma tmul_eq_algebraMap_mul (a' : A) (e : P₀) :
    a' ⊗ₜ[R₀] e = algebraMap A (A ⊗[R₀] P₀) a' *
      (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀) e := by
  simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.algebraMap_apply]

/-- `(A → A ⧸ 𝔟) ⊗ ι` kills `𝔟 (A ⊗ P₀)`. -/
lemma map_eq_zero_of_mem_map (𝔟 : Ideal A) {w : A ⊗[R₀] P₀}
    (hw : w ∈ 𝔟.map (algebraMap A (A ⊗[R₀] P₀))) :
    TensorProduct.map (Ideal.Quotient.mkₐ R₀ 𝔟).toLinearMap ι.toLinearMap w = 0 := by
  have hw' : w ∈ (𝔟 • (⊤ : Submodule A (A ⊗[R₀] P₀))) := by
    rw [Ideal.smul_top_eq_map]; exact hw
  refine Submodule.smul_induction_on
    (p := fun w => TensorProduct.map (Ideal.Quotient.mkₐ R₀ 𝔟).toLinearMap ι.toLinearMap w = 0)
    hw' (fun b hb w hwt => ?_) (fun u v hu hv => by rw [map_add, hu, hv, add_zero])
  clear hwt
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a' p =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul]
    have : (Ideal.Quotient.mkₐ R₀ 𝔟).toLinearMap (b • a') = 0 := by
      simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, smul_eq_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ hb)
    rw [this, TensorProduct.zero_tmul]
  | add u v hu hv => rw [smul_add, map_add, hu, hv, add_zero]

include hι hιker in
/-- The kernel of `(A → A ⧸ 𝔟) ⊗ (J₀ → J₀ B)` maps into `𝔇` under `A ⊗ J₀ → A ⊗ P₀`. -/
lemma lTensor_mem_of_mem_ker (𝔟 : Ideal A) (𝔇 : Ideal (A ⊗[R₀] P₀))
    (hD : 𝔟.map (algebraMap A (A ⊗[R₀] P₀)) *
      J₀.map (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀) ≤ 𝔇)
    (hD' : ∀ e ∈ J₀, e ∈ 𝔭.map (algebraMap R₀ P₀) →
      (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀) e ∈ 𝔇)
    {w : A ⊗[R₀] J₀.restrictScalars R₀}
    (hw : w ∈ LinearMap.ker (TensorProduct.map (Ideal.Quotient.mkₐ R₀ 𝔟).toLinearMap
      (toMapIdeal J₀ ι))) :
    (J₀.restrictScalars R₀).subtype.lTensor A w ∈ 𝔇 := by
  have hw' := (ker_map_eq_sup (Ideal.Quotient.mkₐ R₀ 𝔟).toLinearMap (toMapIdeal J₀ ι)
    (Ideal.Quotient.mkₐ_surjective R₀ 𝔟) (toMapIdeal_surjective J₀ ι hι)).le hw
  have h1 : ∀ w : A ⊗[R₀] LinearMap.ker (toMapIdeal J₀ ι),
      (J₀.restrictScalars R₀).subtype.lTensor A
        ((LinearMap.ker (toMapIdeal J₀ ι)).subtype.lTensor A w) ∈ 𝔇 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a' e =>
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, Submodule.coe_subtype,
        tmul_eq_algebraMap_mul]
      refine Ideal.mul_mem_left _ _ (hD' _ e.1.2 (hιker _ ?_))
      exact congrArg Subtype.val (LinearMap.mem_ker.mp e.2)
    | add u v hu hv => rw [map_add, map_add]; exact add_mem hu hv
  have h2 : ∀ w : LinearMap.ker (Ideal.Quotient.mkₐ R₀ 𝔟).toLinearMap ⊗[R₀] J₀.restrictScalars R₀,
      (J₀.restrictScalars R₀).subtype.lTensor A
        ((LinearMap.ker (Ideal.Quotient.mkₐ R₀ 𝔟).toLinearMap).subtype.rTensor _ w) ∈ 𝔇 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a' e =>
      rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, Submodule.coe_subtype,
        tmul_eq_algebraMap_mul]
      have ha' : (a' : A) ∈ 𝔟 := by
        have := LinearMap.mem_ker.mp a'.2
        rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem] at this
        exact this
      exact hD (Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ ha') (Ideal.mem_map_of_mem _ e.2))
    | add u v hu hv => rw [map_add, map_add]; exact add_mem hu hv
  obtain ⟨u, ⟨w₁, rfl⟩, v, ⟨w₂, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hw'
  rw [map_add]
  exact add_mem (h1 w₁) (h2 w₂)

include hι hιker in
/-- **Lemma `lem:sm-fd-base-change`.** Base change of Tor over a generically flat stratum: here
`B = P₀ ⧸ 𝔭 P₀` is presented by the surjection `ι : P₀ → B` with kernel inside `𝔭 P₀`. -/
theorem exists_pow_smul_mem_of_mem_map [Algebra (R₀ ⧸ 𝔭) B] [IsScalarTower R₀ (R₀ ⧸ 𝔭) B]
    [Module.Flat (R₀ ⧸ 𝔭) (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk 𝔭 a))
      (B ⧸ J₀.map ι))]
    (𝔟 : Ideal A) (𝔇 : Ideal (A ⊗[R₀] P₀))
    (hD : 𝔟.map (algebraMap A (A ⊗[R₀] P₀)) *
      J₀.map (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀) ≤ 𝔇)
    (hD' : ∀ e ∈ J₀, e ∈ 𝔭.map (algebraMap R₀ P₀) →
      (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀) e ∈ 𝔇)
    {x : A ⊗[R₀] P₀}
    (hxJ : x ∈ J₀.map (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀))
    (hx𝔟 : x ∈ 𝔟.map (algebraMap A (A ⊗[R₀] P₀))) :
    ∃ k : ℕ, a ^ k • x ∈ 𝔇 := by
  -- `x = Θ y` with `y ∈ A ⊗ J₀`
  have hxΘ : x ∈ LinearMap.range ((J₀.restrictScalars R₀).subtype.lTensor A) := by
    rw [← Ideal.map_includeRight_eq]
    exact hxJ
  obtain ⟨y, rfl⟩ := hxΘ
  set Jb := J₀.map ι
  -- the exact sequence `0 → J₀ B → B → B / J₀ B → 0` over `R₀ ⧸ 𝔭`
  let fX : Jb →ₗ[R₀ ⧸ 𝔭] B := Jb.subtype.restrictScalars (R₀ ⧸ 𝔭)
  let gX : B →ₗ[R₀ ⧸ 𝔭] B ⧸ Jb := (Ideal.Quotient.mkₐ (R₀ ⧸ 𝔭) Jb).toLinearMap
  have hfgX : Function.Exact fX gX := by
    intro z
    simp only [gX, fX, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Set.mem_range,
      LinearMap.coe_restrictScalars, Submodule.coe_subtype, Subtype.exists, exists_prop,
      exists_eq_right]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hζ' : ∀ y : A ⊗[R₀] J₀.restrictScalars R₀, (fX.restrictScalars R₀).lTensor (A ⧸ 𝔟)
      (TensorProduct.map (Ideal.Quotient.mkₐ R₀ 𝔟).toLinearMap (toMapIdeal J₀ ι) y) =
      TensorProduct.map (Ideal.Quotient.mkₐ R₀ 𝔟).toLinearMap ι.toLinearMap
        ((J₀.restrictScalars R₀).subtype.lTensor A y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' e => rfl
    | add u v hu hv => simp only [map_add, hu, hv]
  have hζ : (fX.restrictScalars R₀).lTensor (A ⧸ 𝔟)
      (TensorProduct.map (Ideal.Quotient.mkₐ R₀ 𝔟).toLinearMap (toMapIdeal J₀ ι) y) = 0 := by
    rw [hζ']
    exact map_eq_zero_of_mem_map ι A 𝔟 hx𝔟
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_lTensor_eq_zero 𝔭 a fX gX Subtype.val_injective
    (Ideal.Quotient.mkₐ_surjective (R₀ ⧸ 𝔭) Jb) hfgX (A ⧸ 𝔟) _ hζ
  refine ⟨k, ?_⟩
  have hker : a ^ k • y ∈ LinearMap.ker
      (TensorProduct.map (Ideal.Quotient.mkₐ R₀ 𝔟).toLinearMap (toMapIdeal J₀ ι)) := by
    rw [LinearMap.mem_ker, map_smul]
    exact hk
  rw [← map_smul]
  exact lTensor_mem_of_mem_ker J₀ 𝔭 ι hι hιker A 𝔟 𝔇 hD hD' hker

end BaseChange

end DeJongAlterations.StableModification.Limits.FlatDescent
