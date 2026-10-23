import DeJongAlterations.StableModification.Limits.FlatDescent.Criteria
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Generic flatness

Let `D` be a noetherian domain, `B` a `D`-algebra of finite type and `M` a finitely generated
`B`-module. Then `M_b` is flat over `D` for some nonzero `b ∈ D`
(`exists_flat_localizedModule`; EGA IV₂ 6.9.1, Stacks 051R). The proof is by induction on the
number of generators of `B`: writing `B = B'[x]`, the module `M` is filtered by the
`B'`-submodules `G_d = Σ_{j<d} x^j N` with `N` the `B'`-span of generators of `M`, whose
successive quotients `N / K_d` take only finitely many values by noetherianity.

We also record that flatness is stable under extensions (`flat_of_exact`) and directed unions of
submodules (`flat_of_iSup_eq_top`).

Blueprint: `lem:sm-fd-flat-extension`, `thm:sm-fd-generic-flatness` in `sm-flat-descent.tex`.
-/

open TensorProduct

namespace DeJongAlterations.StableModification.Limits.FlatDescent

section Extension

variable {D : Type*} [CommRing D]

lemma flat_of_mulMap_injective {M : Type*} [AddCommGroup M] [Module D M]
    (h : ∀ 𝔟 : Ideal D, Function.Injective (mulMap 𝔟 M)) : Module.Flat D M := by
  rw [Module.Flat.iff_rTensor_injective']
  intro 𝔟 a b hab
  apply h 𝔟
  simp only [mulMap, LinearMap.comp_apply, hab]

/-- **Lemma `lem:sm-fd-flat-extension` (1).** An extension of flat modules is flat. -/
theorem flat_of_exact {M' M M'' : Type*} [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module D M'] [Module D M] [Module D M''] [Module.Flat D M'] [Module.Flat D M'']
    (f : M' →ₗ[D] M) (g : M →ₗ[D] M'') (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) : Module.Flat D M := by
  refine flat_of_mulMap_injective fun 𝔟 => ?_
  rw [injective_iff_map_eq_zero]
  intro y hy
  have h1 : g.lTensor 𝔟 y = 0 := by
    apply mulMap_injective_of_flat 𝔟 M''
    rw [← LinearMap.comp_apply (mulMap 𝔟 M''), mulMap_comp_lTensor, LinearMap.comp_apply, hy,
      map_zero, map_zero]
  obtain ⟨y', rfl⟩ := (lTensor_exact 𝔟 hfg hg y).mp h1
  have h2 : mulMap 𝔟 M' y' = 0 := by
    apply hf
    rw [← LinearMap.comp_apply f, ← mulMap_comp_lTensor, LinearMap.comp_apply, hy, map_zero]
  rw [mulMap_injective_of_flat 𝔟 M' (h2.trans (map_zero _).symm), map_zero]

/-- **Lemma `lem:sm-fd-flat-extension` (2).** A directed union of flat submodules is flat. -/
theorem flat_of_iSup_eq_top {M : Type*} [AddCommGroup M] [Module D M] {ι : Type*} [Nonempty ι]
    (N : ι → Submodule D M) (hdir : Directed (· ≤ ·) N) (htop : ⨆ i, N i = ⊤)
    (hflat : ∀ i, Module.Flat D (N i)) : Module.Flat D M := by
  refine flat_of_mulMap_injective fun 𝔟 => ?_
  rw [injective_iff_map_eq_zero]
  intro y hy
  -- `y` comes from some `𝔟 ⊗ N i`
  have hrange : ∀ y : 𝔟 ⊗[D] M, ∃ i, y ∈ LinearMap.range ((N i).subtype.lTensor 𝔟) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨Classical.arbitrary ι, zero_mem _⟩
    | tmul r m =>
      have hm : m ∈ ⨆ i, N i := by rw [htop]; exact Submodule.mem_top
      obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed N hdir).mp hm
      exact ⟨i, r ⊗ₜ ⟨m, hi⟩, rfl⟩
    | add a b ha hb =>
      obtain ⟨i, a', rfl⟩ := ha
      obtain ⟨j, b', rfl⟩ := hb
      obtain ⟨k, hik, hjk⟩ := hdir i j
      refine ⟨k, (Submodule.inclusion hik).lTensor 𝔟 a' + (Submodule.inclusion hjk).lTensor 𝔟 b',
        ?_⟩
      rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
        ← LinearMap.lTensor_comp]
      rfl
  obtain ⟨i, y', rfl⟩ := hrange y
  have h2 : mulMap 𝔟 (N i) y' = 0 := by
    apply Subtype.val_injective
    rw [← Submodule.coe_subtype, ← LinearMap.comp_apply (N i).subtype, ← mulMap_comp_lTensor,
      LinearMap.comp_apply, hy]
    rfl
  rw [mulMap_injective_of_flat 𝔟 (N i) (h2.trans (map_zero _).symm), map_zero]

end Extension

section Localization

variable {D : Type*} [CommRing D] (S : Submonoid D)

/-- A retract of a module with flat localization has flat localization. -/
lemma flat_localizedModule_of_retract {M N : Type*} [AddCommGroup M] [Module D M] [AddCommGroup N]
    [Module D N] [Module.Flat D (LocalizedModule S M)] (i : N →ₗ[D] M) (r : M →ₗ[D] N)
    (h : r ∘ₗ i = LinearMap.id) : Module.Flat D (LocalizedModule S N) := by
  let F : LocalizedModule S N →ₗ[D] LocalizedModule S M :=
    (LocalizedModule.map S i).restrictScalars D
  let G : LocalizedModule S M →ₗ[D] LocalizedModule S N :=
    (LocalizedModule.map S r).restrictScalars D
  refine Module.Flat.of_retract F G ?_
  ext x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    have := congrArg (fun f => f m) h
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [F, G, LocalizedModule.map_mk, this]

/-- Flatness of localizations is invariant under linear equivalences. -/
lemma flat_localizedModule_of_equiv {M N : Type*} [AddCommGroup M] [Module D M] [AddCommGroup N]
    [Module D N] (e : M ≃ₗ[D] N) [Module.Flat D (LocalizedModule S M)] :
    Module.Flat D (LocalizedModule S N) :=
  flat_localizedModule_of_retract S e.symm.toLinearMap e.toLinearMap (by ext; simp)

/-- Localization preserves short exact sequences, so an extension of modules with flat
localizations has flat localization. -/
lemma flat_localizedModule_of_exact {M' M M'' : Type*} [AddCommGroup M'] [AddCommGroup M]
    [AddCommGroup M''] [Module D M'] [Module D M] [Module D M'']
    [Module.Flat D (LocalizedModule S M')] [Module.Flat D (LocalizedModule S M'')]
    (f : M' →ₗ[D] M) (g : M →ₗ[D] M'') (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) : Module.Flat D (LocalizedModule S M) :=
  flat_of_exact ((LocalizedModule.map S f).restrictScalars D)
    ((LocalizedModule.map S g).restrictScalars D) (LocalizedModule.map_injective S f hf)
    (LocalizedModule.map_surjective S g hg) (LocalizedModule.map_exact S f g hfg)

/-- `flat_localizedModule_of_exact` for linear maps over a `D`-algebra `B'`. -/
lemma flat_localizedModule_of_exact' {B' : Type*} [CommRing B'] [Algebra D B']
    {M' M M'' : Type*} [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M''] [Module B' M']
    [Module B' M] [Module B' M''] [Module D M'] [Module D M] [Module D M'']
    [IsScalarTower D B' M'] [IsScalarTower D B' M] [IsScalarTower D B' M'']
    [Module.Flat D (LocalizedModule S M')] [Module.Flat D (LocalizedModule S M'')]
    (f : M' →ₗ[B'] M) (g : M →ₗ[B'] M'') (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Module.Flat D (LocalizedModule S M) :=
  flat_localizedModule_of_exact S (f.restrictScalars D) (g.restrictScalars D) hf hg hfg

end Localization

section Filtration

variable {D : Type*} [CommRing D] (S : Submonoid D)
variable {B' M : Type*} [CommRing B'] [Algebra D B'] [AddCommGroup M] [Module B' M] [Module D M]
  [IsScalarTower D B' M]

/-- One step of the filtration: if `G₁ = G₀ + φ N` and `K = {y ∈ N | φ y ∈ G₀}`, then
`G₁ / G₀ ≅ N / K`. -/
noncomputable def quotientEquivOfSucc (N : Submodule B' M) (φ : M →ₗ[B'] M)
    (G₀ G₁ : Submodule B' M) (hle : G₀ ≤ G₁) (hG : G₁ = G₀ ⊔ N.map φ) (K : Submodule B' N)
    (hK : ∀ y : N, y ∈ K ↔ φ y ∈ G₀) :
    (N ⧸ K) ≃ₗ[B'] (G₁ ⧸ LinearMap.range (Submodule.inclusion hle)) := by
  let ψ₀ : N →ₗ[B'] G₁ := (φ ∘ₗ N.subtype).codRestrict G₁ (fun y => by
    rw [hG]
    exact Submodule.mem_sup_right ⟨y, y.2, by rw [LinearMap.comp_apply]; rfl⟩)
  have hψ₀ : ∀ y : N, (ψ₀ y : M) = φ y := fun y => rfl
  clear_value ψ₀
  let ψ : N →ₗ[B'] G₁ ⧸ LinearMap.range (Submodule.inclusion hle) :=
    (LinearMap.range (Submodule.inclusion hle)).mkQ ∘ₗ ψ₀
  have hψapp : ∀ y, ψ y = Submodule.Quotient.mk (ψ₀ y) := fun y => rfl
  clear_value ψ
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨m, hm⟩, rfl⟩ := Submodule.mkQ_surjective _ z
    have hm' := hm
    rw [hG] at hm'
    obtain ⟨u, hu, v, ⟨y, hy, rfl⟩, huv⟩ := Submodule.mem_sup.mp hm'
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [hψapp, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨⟨-u, G₀.neg_mem hu⟩, ?_⟩
    apply Subtype.ext
    rw [Submodule.coe_inclusion, Submodule.coe_sub, hψ₀]
    subst huv
    simp
  have hkerψ : LinearMap.ker ψ = K := by
    ext y
    rw [hK, LinearMap.mem_ker, hψapp, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨u, hu⟩
      have := congrArg Subtype.val hu
      rw [Submodule.coe_inclusion, hψ₀] at this
      rw [← this]
      exact u.2
    · intro h
      refine ⟨⟨_, h⟩, ?_⟩
      apply Subtype.ext
      rw [Submodule.coe_inclusion, hψ₀]
  exact (Submodule.quotEquivOfEq _ _ hkerψ.symm).trans (LinearMap.quotKerEquivOfSurjective ψ hψ)

/-- One step of the filtration: flatness of the localizations of `G₀` and `N / K` gives
flatness of the localization of `G₁ = G₀ + φ N`. -/
lemma flat_localizedModule_succ (N : Submodule B' M) (φ : M →ₗ[B'] M) (G₀ G₁ : Submodule B' M)
    (hG : G₁ = G₀ ⊔ N.map φ) (K : Submodule B' N) (hK : ∀ y : N, y ∈ K ↔ φ y ∈ G₀)
    [Module.Flat D (LocalizedModule S G₀)] [Module.Flat D (LocalizedModule S (N ⧸ K))] :
    Module.Flat D (LocalizedModule S G₁) := by
  have hle : G₀ ≤ G₁ := by rw [hG]; exact le_sup_left
  have : Module.Flat D
      (LocalizedModule S (G₁ ⧸ LinearMap.range (Submodule.inclusion hle))) :=
    flat_localizedModule_of_equiv S
      ((quotientEquivOfSucc N φ G₀ G₁ hle hG K hK).restrictScalars D)
  exact flat_localizedModule_of_exact' S (Submodule.inclusion hle)
    (LinearMap.range (Submodule.inclusion hle)).mkQ
    (Submodule.inclusion_injective hle) (Submodule.mkQ_surjective _)
    (LinearMap.exact_map_mkQ_range (Submodule.inclusion hle))

/-- The localization of `M` is flat if `M` is the union of an increasing sequence of submodules
with flat localizations. -/
lemma flat_localizedModule_of_union (G : ℕ → Submodule B' M) (hGmono : Monotone G)
    (hGtop : ∀ m : M, ∃ d, m ∈ G d) (hflat : ∀ d, Module.Flat D (LocalizedModule S (G d))) :
    Module.Flat D (LocalizedModule S M) := by
  let L : ℕ → Submodule D (LocalizedModule S M) := fun k =>
    LinearMap.range ((LocalizedModule.map S ((G k).subtype.restrictScalars D)).restrictScalars D)
  have hLinj : ∀ k, Function.Injective
      ((LocalizedModule.map S ((G k).subtype.restrictScalars D)).restrictScalars D) := fun k =>
    LocalizedModule.map_injective _ _ Subtype.val_injective
  have hLdir : Directed (· ≤ ·) L := by
    refine Monotone.directed_le fun k k' hkk' => ?_
    rintro _ ⟨z, rfl⟩
    refine ⟨(LocalizedModule.map S ((Submodule.inclusion (hGmono hkk')).restrictScalars D)) z, ?_⟩
    induction z using LocalizedModule.induction_on with
    | h m s => simp [LocalizedModule.map_mk]
  refine flat_of_iSup_eq_top L hLdir ?_ ?_
  · rw [eq_top_iff]
    rintro z -
    induction z using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨d, hd⟩ := hGtop m
      refine (Submodule.mem_iSup_of_directed L hLdir).mpr ⟨d, ⟨LocalizedModule.mk ⟨m, hd⟩ s, ?_⟩⟩
      simp [LocalizedModule.map_mk]
  · intro k
    have := hflat k
    exact Module.Flat.of_linearEquiv (LinearEquiv.ofInjective _ (hLinj k)).symm

/-- The filtration argument of generic flatness: let `M` be the union of the submodules
`G d` with `G 0 = 0` and `G (d + 1) = G d + φ^d N`, and `K d = {y ∈ N | φ^d y ∈ G d}`, constant
for `d ≥ d₀`. If `G d₀` and `N / K d₀` have flat localizations, so has `M`. -/
lemma flat_localizedModule_of_filtration (N : Submodule B' M) (φ : M →ₗ[B'] M)
    (G : ℕ → Submodule B' M) (hGsucc : ∀ d, G (d + 1) = G d ⊔ N.map (φ ^ d))
    (hGtop : ∀ m : M, ∃ d, m ∈ G d) (K : ℕ → Submodule B' N)
    (hKmem : ∀ d (y : N), y ∈ K d ↔ (φ ^ d) y ∈ G d) (d₀ : ℕ) (hd₀ : ∀ d, d₀ ≤ d → K d = K d₀)
    (h0 : Module.Flat D (LocalizedModule S (G d₀)))
    (hK : Module.Flat D (LocalizedModule S (N ⧸ K d₀))) :
    Module.Flat D (LocalizedModule S M) := by
  have hGmono : Monotone G := monotone_nat_of_le_succ fun d => by
    rw [hGsucc]; exact le_sup_left
  have hflatG : ∀ k, Module.Flat D (LocalizedModule S (G (d₀ + k))) := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ihk =>
      have hKd := hd₀ (d₀ + k) (by omega)
      have : Module.Flat D (LocalizedModule S (N ⧸ K (d₀ + k))) := by rw [hKd]; exact hK
      exact flat_localizedModule_succ S N (φ ^ (d₀ + k)) (G (d₀ + k)) (G (d₀ + k + 1))
        (hGsucc _) (K (d₀ + k)) (hKmem _)
  refine flat_localizedModule_of_union S (fun k => G (d₀ + k)) (fun k k' h => hGmono (by omega))
    (fun m => ?_) hflatG
  obtain ⟨d, hd⟩ := hGtop m
  exact ⟨d, hGmono (by omega) hd⟩

end Filtration

section GenericFlatness

universe u v w

variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D]

/-- The base case of generic flatness: a finitely generated `D`-module. -/
lemma exists_flat_localizedModule_of_finite (M : Type w) [AddCommGroup M] [Module D M]
    [Module.Finite D M] :
    ∃ b : D, b ≠ 0 ∧ Module.Flat D (LocalizedModule (Submonoid.powers b) M) := by
  have : Module.FinitePresentation D M := Module.finitePresentation_of_finite D M
  let : Field (FractionRing D) := FractionRing.field D
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors D) (LocalizedModule.mkLinearMap (nonZeroDivisors D) M) (FractionRing D)
  refine ⟨r, nonZeroDivisors.ne_zero hr, ?_⟩
  have : Module.Flat (Localization (Submonoid.powers r))
      (LocalizedModule (Submonoid.powers r) M) := Module.Flat.of_free
  have : Module.Flat D (Localization (Submonoid.powers r)) :=
    IsLocalization.flat _ (Submonoid.powers r)
  exact Module.Flat.trans D (Localization (Submonoid.powers r)) _

omit [IsDomain D] [IsNoetherianRing D] in
/-- The filtration of a finitely generated `B'[x]`-module by `B'`-submodules. -/
lemma exists_filtration {B : Type v} [CommRing B] [Algebra D B] (B' : Subalgebra D B) (x : B)
    (hB : Algebra.adjoin B' ({x} : Set B) = ⊤) (M : Type w) [AddCommGroup M] [Module B M]
    [Module D M] [IsScalarTower D B M] [Module.Finite B M] :
    ∃ (N : Submodule B' M) (G : ℕ → Submodule B' M), N.FG ∧
      (∀ d, G (d + 1) = G d ⊔ N.map (((LinearMap.lsmul B M x).restrictScalars B') ^ d)) ∧
      (∀ d, ∀ y ∈ G d, x • y ∈ G (d + 1)) ∧ (∀ m : M, ∃ d, m ∈ G d) ∧ ∀ d, (G d).FG := by
  classical
  obtain ⟨g, hg⟩ := (Module.Finite.fg_top : (⊤ : Submodule B M).FG)
  let N : Submodule B' M := Submodule.span B' (g : Set M)
  let φ : M →ₗ[B'] M := (LinearMap.lsmul B M x).restrictScalars B'
  have hφ : ∀ m, φ m = x • m := fun m => rfl
  let G : ℕ → Submodule B' M := fun d => (Finset.range d).sup fun j => N.map (φ ^ j)
  have hGsucc : ∀ d, G (d + 1) = G d ⊔ N.map (φ ^ d) := by
    intro d
    simp only [G, Finset.range_add_one, Finset.sup_insert, sup_comm]
  have hGmono : Monotone G := monotone_nat_of_le_succ fun d => by
    rw [hGsucc]; exact le_sup_left
  have hφG : ∀ d, ∀ y ∈ G d, φ y ∈ G (d + 1) := by
    intro d
    have : G d ≤ (G (d + 1)).comap φ := by
      apply Finset.sup_le
      intro j hj
      rw [← Submodule.map_le_iff_le_comap, ← Submodule.map_comp]
      have : φ ∘ₗ φ ^ j = φ ^ (j + 1) := by rw [pow_succ']; rfl
      rw [this]
      exact Finset.le_sup (f := fun j => N.map (φ ^ j))
        (Finset.mem_range.mpr (Nat.succ_lt_succ (Finset.mem_range.mp hj)))
    exact fun y hy => this hy
  have hGfg : ∀ d, (G d).FG := by
    intro d
    simp only [G]
    exact Submodule.fg_finset_sup _ _ fun j _ => (Submodule.fg_span g.finite_toSet).map _
  refine ⟨N, G, Submodule.fg_span g.finite_toSet, hGsucc, fun d y hy => hφ y ▸ hφG d y hy, ?_,
    hGfg⟩
  have hdirG : Directed (· ≤ ·) G := hGmono.directed_le
  let Ginf : Submodule B' M := ⨆ d, G d
  have hmemInf : ∀ m, m ∈ Ginf ↔ ∃ d, m ∈ G d := fun m =>
    Submodule.mem_iSup_of_directed G hdirG
  have hxG : ∀ m ∈ Ginf, x • m ∈ Ginf := by
    intro m hm
    obtain ⟨d, hd⟩ := (hmemInf m).mp hm
    exact (hmemInf _).mpr ⟨d + 1, hφ m ▸ hφG d m hd⟩
  have hpolyG : ∀ q : Polynomial B', ∀ m ∈ Ginf, Polynomial.aeval x q • m ∈ Ginf := by
    intro q
    induction q using Polynomial.induction_on with
    | C c =>
      intro m hm
      rw [Polynomial.aeval_C, algebraMap_smul]
      exact Ginf.smul_mem c hm
    | add p q hp hq =>
      intro m hm
      rw [map_add, add_smul]
      exact add_mem (hp m hm) (hq m hm)
    | monomial k c hk =>
      intro m hm
      have : Polynomial.aeval x (Polynomial.C c * Polynomial.X ^ (k + 1)) • m =
          Polynomial.aeval x (Polynomial.C c * Polynomial.X ^ k) • (x • m) := by
        rw [← mul_smul]
        congr 1
        simp [pow_succ, mul_assoc]
      rw [this]
      exact hk _ (hxG m hm)
  have hBG : ∀ β : B, ∀ m ∈ Ginf, β • m ∈ Ginf := by
    intro β m hm
    have hβ : β ∈ Algebra.adjoin B' ({x} : Set B) := by rw [hB]; exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hβ
    obtain ⟨q, rfl⟩ := hβ
    exact hpolyG q m hm
  intro m
  have hm : m ∈ Submodule.span B (g : Set M) := by rw [hg]; exact Submodule.mem_top
  refine (hmemInf m).mp ?_
  induction hm using Submodule.span_induction with
  | mem y hy =>
    refine (hmemInf y).mpr ⟨1, ?_⟩
    rw [hGsucc]
    apply Submodule.mem_sup_right
    exact ⟨y, Submodule.subset_span hy, by simp⟩
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul β y _ hy => exact hBG β y hy

omit [IsDomain D] [IsNoetherianRing D] in
/-- Removing one generator: `B = B'[x]` with `B'` generated by the remaining ones. -/
lemma exists_adjoin_erase {B : Type v} [CommRing B] [Algebra D B] (s : Finset B)
    (hadj : Algebra.adjoin D (s : Set B) = ⊤) {x : B} (hx : x ∈ s) :
    ∃ (B' : Subalgebra D B) (t : Finset B'), t.card + 1 = s.card ∧
      Algebra.adjoin D (t : Set B') = ⊤ ∧ Algebra.adjoin B' ({x} : Set B) = ⊤ := by
  classical
  set s' := s.erase x with hs'
  let B' : Subalgebra D B := Algebra.adjoin D (s' : Set B)
  let f : s' ↪ B' := ⟨fun y => ⟨y.1, Algebra.subset_adjoin y.2⟩, fun y z h => by
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa using this⟩
  refine ⟨B', s'.attach.map f, ?_, ?_, ?_⟩
  · simp only [Finset.card_map, Finset.card_attach, hs', Finset.card_erase_of_mem hx]
    have := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  · apply Subalgebra.map_injective (f := B'.val) Subtype.val_injective
    rw [← Algebra.adjoin_image, Algebra.map_top, Subalgebra.range_val]
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Finset.mem_coe, Finset.mem_map] at hz
      obtain ⟨w, -, rfl⟩ := hz
      exact w.2
    · intro hy
      refine ⟨⟨y, Algebra.subset_adjoin hy⟩, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_map]
      exact ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩
  · apply Subalgebra.restrictScalars_injective D
    rw [Subalgebra.restrictScalars_top, ← Algebra.adjoin_union_eq_adjoin_adjoin, ← hadj]
    congr 1
    ext y
    simp only [hs', Finset.coe_erase, Set.mem_union, Set.mem_sdiff, Finset.mem_coe,
      Set.mem_singleton_iff]
    constructor
    · rintro (⟨h, -⟩ | rfl) <;> assumption
    · intro h
      by_cases hyx : y = x
      · exact Or.inr hyx
      · exact Or.inl ⟨h, hyx⟩

/-- Generic flatness, by induction on the number of algebra generators. -/
lemma exists_flat_localizedModule_aux (n : ℕ) :
    ∀ (B : Type v) [CommRing B] [Algebra D B] (s : Finset B), s.card ≤ n →
      Algebra.adjoin D (s : Set B) = ⊤ →
      ∀ (M : Type w) [AddCommGroup M] [Module B M] [Module D M] [IsScalarTower D B M]
        [Module.Finite B M],
        ∃ b : D, b ≠ 0 ∧ Module.Flat D (LocalizedModule (Submonoid.powers b) M) := by
  classical
  induction n with
  | zero =>
    intro B _ _ s hs hadj M _ _ _ _ _
    have hs0 : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
    subst hs0
    have hsurj : Function.Surjective (Algebra.linearMap D B) := by
      intro b
      have hb : b ∈ (⊥ : Subalgebra D B) := by
        rw [← Algebra.adjoin_empty D B, ← Finset.coe_empty, hadj]; exact Algebra.mem_top
      obtain ⟨d, rfl⟩ := Algebra.mem_bot.mp hb
      exact ⟨d, rfl⟩
    have : Module.Finite D B := Module.Finite.of_surjective _ hsurj
    have : Module.Finite D M := Module.Finite.trans B M
    exact exists_flat_localizedModule_of_finite M
  | succ n ih =>
    intro B _ _ s hs hadj M _ _ _ _ _
    rcases s.eq_empty_or_nonempty with hs0 | ⟨x, hx⟩
    · subst hs0
      exact ih B ∅ (by simp) hadj M
    obtain ⟨B', t, ht, htadj, hB⟩ := exists_adjoin_erase s hadj hx
    have : Algebra.FiniteType D B' := ⟨⟨t, htadj⟩⟩
    have : IsNoetherianRing B' := Algebra.FiniteType.isNoetherianRing D B'
    obtain ⟨N, G, hNfg, hGsucc, hxG, hGtop, hGfg⟩ := exists_filtration B' x hB M
    have : Module.Finite B' N := Module.Finite.iff_fg.mpr hNfg
    set φ : M →ₗ[B'] M := (LinearMap.lsmul B M x).restrictScalars B' with hφ
    have hφapp : ∀ m, φ m = x • m := fun m => rfl
    clear_value φ
    let K : ℕ → Submodule B' N := fun d => (G d).comap ((φ ^ d) ∘ₗ N.subtype)
    have hKmem : ∀ d (y : N), y ∈ K d ↔ (φ ^ d) y ∈ G d := fun d y => Iff.rfl
    clear_value K
    have hKmono : Monotone K := monotone_nat_of_le_succ fun d y hy => by
      rw [hKmem] at hy ⊢
      rw [pow_succ', Module.End.mul_apply, hφapp]
      exact hxG d _ hy
    obtain ⟨d₀, hd₀⟩ := monotone_stabilizes_iff_noetherian.mpr
      (inferInstance : IsNoetherian B' N) ⟨K, hKmono⟩
    have hd₀' : ∀ d, d₀ ≤ d → K d = K d₀ := fun d hd => (hd₀ d hd).symm
    have : Module.Finite B' (G d₀) := Module.Finite.iff_fg.mpr (hGfg d₀)
    obtain ⟨b, hb, hflatQ⟩ := ih B' t (by omega) htadj (G d₀ × (N ⧸ K d₀))
    have hflat0 : Module.Flat D (LocalizedModule (Submonoid.powers b) (G d₀)) :=
      flat_localizedModule_of_retract (M := G d₀ × (N ⧸ K d₀)) (Submonoid.powers b)
        (LinearMap.inl D _ _) (LinearMap.fst D _ _) (LinearMap.fst_comp_inl D _ _)
    have hflatK : Module.Flat D (LocalizedModule (Submonoid.powers b) (N ⧸ K d₀)) :=
      flat_localizedModule_of_retract (M := G d₀ × (N ⧸ K d₀)) (Submonoid.powers b)
        (LinearMap.inr D _ _) (LinearMap.snd D _ _) (LinearMap.snd_comp_inr D _ _)
    exact ⟨b, hb, flat_localizedModule_of_filtration _ N φ G hGsucc hGtop K hKmem d₀ hd₀'
      hflat0 hflatK⟩

/-- **Theorem `thm:sm-fd-generic-flatness` (generic flatness).** Let `D` be a noetherian domain,
`B` a `D`-algebra of finite type and `M` a finitely generated `B`-module. Then `M_b` is a flat
`D`-module for some nonzero `b ∈ D`. -/
theorem exists_flat_localizedModule {B : Type v} [CommRing B] [Algebra D B]
    [Algebra.FiniteType D B] (M : Type w) [AddCommGroup M] [Module B M] [Module D M]
    [IsScalarTower D B M] [Module.Finite B M] :
    ∃ b : D, b ≠ 0 ∧ Module.Flat D (LocalizedModule (Submonoid.powers b) M) := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra D B).FG)
  exact exists_flat_localizedModule_aux s.card B s le_rfl hs M

end GenericFlatness

end DeJongAlterations.StableModification.Limits.FlatDescent
