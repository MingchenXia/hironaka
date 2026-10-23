import DeJongAlterations.StableModification.Limits.FlatDescent.LocalCriterion
import DeJongAlterations.StableModification.Limits.FlatDescent.GenericFlatness
import DeJongAlterations.StableModification.Limits.FlatDescent.BaseChange
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.TotallySplit

/-!
# Descent of flatness along directed unions of noetherian rings

Let `R₀` be a noetherian ring, `L` an `R₀`-algebra, `F i` (`i ∈ ι`) a directed family of
noetherian `R₀`-subalgebras of `L`, and `R ⊆ L` an `R₀`-subalgebra which is their union. If
`B₀` is an `R₀`-algebra of finite type such that `R ⊗[R₀] B₀` is flat over `R`, then
`F j ⊗[R₀] B₀` is flat over `F j` for all large `j` (`flat_tensor_of_flat_tensor_union`).

This is the case of EGA IV₃ 11.2.6 used by Temkin, *Stable modification of relative curves*,
§3.1 (`approxsec`): "a finitely presented `f` is flat if and only if each `f_i`, `i ≥ i₀`, is
flat", for the approximation of a valuation ring of `K^s` by the local rings (or affine
neighbourhoods) of its centres on the quasi-alterations of a base of finite type over a field.

The proof (blueprint chapter `sm-flat-descent`, `thm:sm-flatness-descent`) is a noetherian
induction on `Spec R₀`: over the closed subset `V(𝔭)` of a prime `𝔭` generic flatness
(`exists_flat_localizedModule`) gives `a ∉ 𝔭` with `(B₀ ⧸ 𝔭)_a` flat over `R₀ ⧸ 𝔭`; the base
change of Tor (`exists_pow_smul_mem_of_mem_map`) and the colimit give, at a finite stage, the
hypotheses of the local criterion of flatness with explicit multipliers
(`exists_mul_mem_of_localCriterion`), hence flatness at the maximal ideals over `V(𝔭) ∩ D(a)`;
`V(𝔭 + (a))` is handled by induction.

## Main results

* `exists_sub_pow_mul_mem`: the local criterion at one stage (blueprint `lem:sm-fd-step`).
* `exists_mem_map_of_mem_map`: ideal membership descends along the directed union
  (blueprint `lem:sm-fd-colimit-ideal`).
* `flat_quotient_of_flat_quotient_union`: the theorem for `P₀ ⧸ J₀` with `P₀` a flat
  `R₀`-algebra of finite type.
* `flat_tensor_of_flat_tensor_union`: the theorem for an `R₀`-algebra `B₀` of finite type
  (blueprint `thm:sm-flatness-descent`).
-/

open TensorProduct

universe u v w

namespace DeJongAlterations.StableModification.Limits.FlatDescent

section Stage

variable {R₀ : Type*} [CommRing R₀] {P₀ : Type*} [CommRing P₀] [Algebra R₀ P₀]
  (J₀ : Ideal P₀) (𝔭 : Ideal R₀) (a : R₀)

variable (R₀) in
/-- The ideal `J₀ (A ⊗ P₀)` of `A ⊗[R₀] P₀`. -/
abbrev extIdeal (A : Type*) [CommRing A] [Algebra R₀ A] : Ideal (A ⊗[R₀] P₀) :=
  J₀.map (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀)

lemma map_algebraMap_eq (A : Type*) [CommRing A] [Algebra R₀ A] (I : Ideal R₀) :
    (I.map (algebraMap R₀ A)).map (algebraMap A (A ⊗[R₀] P₀)) =
      I.map (algebraMap R₀ (A ⊗[R₀] P₀)) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

lemma map_includeRight_algebraMap_eq (A : Type*) [CommRing A] [Algebra R₀ A] (I : Ideal R₀) :
    (I.map (algebraMap R₀ P₀)).map
        (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀) =
      I.map (algebraMap R₀ (A ⊗[R₀] P₀)) := by
  change Ideal.map (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀).toRingHom
    (I.map (algebraMap R₀ P₀)) = _
  rw [Ideal.map_map]
  congr 1
  exact (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀).comp_algebraMap

lemma smul_eq_algebraMap_pow_mul {A : Type*} [CommRing A] [Algebra R₀ A] (k : ℕ)
    (x : A ⊗[R₀] P₀) :
    a ^ k • x = algebraMap A (A ⊗[R₀] P₀) (algebraMap R₀ A a) ^ k * x := by
  rw [Algebra.smul_def, ← map_pow, ← map_pow, ← IsScalarTower.algebraMap_apply]

/-- **Lemma `lem:sm-fd-step`, at one stage.** Let `A` be a noetherian `R₀`-algebra, and assume
that `(P₀ ⧸ 𝔭P₀) ⧸ J₀` becomes flat over `R₀ ⧸ 𝔭` after inverting `a`, and that the generators
of `J₀ ∩ 𝔭P₀` lie in `𝔭 J₀ (A ⊗ P₀)`. Then every `x ∈ J₀(A ⊗ P₀) ∩ 𝔟(A ⊗ P₀)` is multiplied into
`𝔟 J₀(A ⊗ P₀)` by some `s ≡ a ^ N (mod 𝔭)`. -/
theorem exists_sub_pow_mul_mem [IsNoetherianRing P₀]
    [Module.Flat (R₀ ⧸ 𝔭) (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk 𝔭 a))
      ((P₀ ⧸ 𝔭.map (algebraMap R₀ P₀)) ⧸
        J₀.map (Ideal.Quotient.mkₐ R₀ (𝔭.map (algebraMap R₀ P₀)))))]
    [Module.Flat R₀ P₀]
    (A : Type*) [CommRing A] [Algebra R₀ A] [IsNoetherianRing A]
    [IsNoetherianRing (A ⊗[R₀] P₀)]
    (hT : ∀ e ∈ J₀ ⊓ 𝔭.map (algebraMap R₀ P₀),
      (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀) e ∈
        𝔭.map (algebraMap R₀ (A ⊗[R₀] P₀)) * extIdeal R₀ J₀ A)
    (𝔟 : Ideal A) {x : A ⊗[R₀] P₀}
    (hx : x ∈ extIdeal R₀ J₀ A ⊓ 𝔟.map (algebraMap A (A ⊗[R₀] P₀))) :
    ∃ (N : ℕ) (s : A ⊗[R₀] P₀), s - algebraMap R₀ (A ⊗[R₀] P₀) a ^ N ∈
        𝔭.map (algebraMap R₀ (A ⊗[R₀] P₀)) ∧
      s * x ∈ 𝔟.map (algebraMap A (A ⊗[R₀] P₀)) * extIdeal R₀ J₀ A := by
  set 𝔭P := 𝔭.map (algebraMap R₀ P₀)
  let ιb : P₀ →ₐ[R₀] P₀ ⧸ 𝔭P := Ideal.Quotient.mkₐ R₀ 𝔭P
  have hιb : Function.Surjective ιb := Ideal.Quotient.mkₐ_surjective R₀ 𝔭P
  have hιbker : ∀ e : P₀, ιb e = 0 → e ∈ 𝔭P := fun e he =>
    Ideal.Quotient.eq_zero_iff_mem.mp he
  set I : Ideal A := 𝔭.map (algebraMap R₀ A)
  have hI : I.map (algebraMap A (A ⊗[R₀] P₀)) = 𝔭.map (algebraMap R₀ (A ⊗[R₀] P₀)) :=
    map_algebraMap_eq A 𝔭
  have hincl : ∀ e ∈ 𝔭P, (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀) e ∈
      𝔭.map (algebraMap R₀ (A ⊗[R₀] P₀)) := by
    intro e he
    rw [← map_includeRight_algebraMap_eq A 𝔭]
    exact Ideal.mem_map_of_mem _ he
  -- hypothesis (i) of the local criterion
  have h1 : IsGood (extIdeal R₀ J₀ A) (algebraMap R₀ A a) I := by
    intro x hx
    obtain ⟨hxJ, hxI⟩ := Submodule.mem_inf.mp hx
    let 𝔇 : Ideal (A ⊗[R₀] P₀) := I.map (algebraMap A (A ⊗[R₀] P₀)) * extIdeal R₀ J₀ A
    have hD' : ∀ e ∈ J₀, e ∈ 𝔭P →
        (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀) e ∈ 𝔇 := by
      intro e he he'
      show _ ∈ I.map (algebraMap A (A ⊗[R₀] P₀)) * extIdeal R₀ J₀ A
      rw [hI]
      exact hT e (Submodule.mem_inf.mpr ⟨he, he'⟩)
    obtain ⟨k, hk⟩ := exists_pow_smul_mem_of_mem_map J₀ 𝔭 a ιb hιb hιbker (A := A) (𝔟 := I)
      (𝔇 := 𝔇) le_rfl hD' hxJ hxI
    exact ⟨k, by rw [← smul_eq_algebraMap_pow_mul]; exact hk⟩
  -- hypothesis (ii) of the local criterion
  have h2 : ∀ 𝔟 : Ideal A, I ≤ 𝔟 →
      ∀ x ∈ (extIdeal R₀ J₀ A ⊔ I.map (algebraMap A (A ⊗[R₀] P₀))) ⊓
        𝔟.map (algebraMap A (A ⊗[R₀] P₀)),
      ∃ k : ℕ, algebraMap A (A ⊗[R₀] P₀) (algebraMap R₀ A a) ^ k * x ∈
        𝔟.map (algebraMap A (A ⊗[R₀] P₀)) * extIdeal R₀ J₀ A ⊔ I.map (algebraMap A (A ⊗[R₀] P₀)) := by
    intro 𝔟 h𝔟 x hx
    obtain ⟨hxJI, hx𝔟⟩ := Submodule.mem_inf.mp hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hxJI
    have hx₂𝔟 : x₂ ∈ 𝔟.map (algebraMap A (A ⊗[R₀] P₀)) := Ideal.map_mono h𝔟 hx₂
    have hx₁𝔟 : x₁ ∈ 𝔟.map (algebraMap A (A ⊗[R₀] P₀)) := by
      have := Ideal.sub_mem _ hx𝔟 hx₂𝔟
      rwa [add_sub_cancel_right] at this
    let 𝔇 : Ideal (A ⊗[R₀] P₀) :=
      𝔟.map (algebraMap A (A ⊗[R₀] P₀)) * extIdeal R₀ J₀ A ⊔ I.map (algebraMap A (A ⊗[R₀] P₀))
    have hD' : ∀ e ∈ J₀, e ∈ 𝔭P →
        (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀) e ∈ 𝔇 := by
      intro e _ he'
      apply Ideal.mem_sup_right
      rw [hI]
      exact hincl e he'
    obtain ⟨k, hk⟩ := exists_pow_smul_mem_of_mem_map J₀ 𝔭 a ιb hιb hιbker (A := A) (𝔟 := 𝔟)
      (𝔇 := 𝔇) le_sup_left hD' hx₁ hx₁𝔟
    refine ⟨k, ?_⟩
    rw [mul_add]
    refine add_mem ?_ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hx₂))
    rw [← smul_eq_algebraMap_pow_mul]
    exact hk
  obtain ⟨N, s, hs, hsx⟩ := exists_mul_mem_of_localCriterion h1 h2 𝔟 hx
  refine ⟨N, s, ?_, hsx⟩
  rw [← hI, IsScalarTower.algebraMap_apply R₀ A (A ⊗[R₀] P₀)]
  exact hs

end Stage

section Union

variable {R₀ : Type u} [CommRing R₀] {L : Type v} [CommRing L] [Algebra R₀ L]
  {P₀ : Type*} [CommRing P₀] [Algebra R₀ P₀]

/-- The map `A ⊗ P₀ → A' ⊗ P₀` induced by an inclusion of subalgebras `A ≤ A'`. -/
noncomputable abbrev tmap {A A' : Subalgebra R₀ L} (h : A ≤ A') :
    A ⊗[R₀] P₀ →ₐ[R₀] A' ⊗[R₀] P₀ :=
  Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id R₀ P₀)

lemma tmap_tmap {A A' A'' : Subalgebra R₀ L} (h₁ : A ≤ A') (h₂ : A' ≤ A'')
    (z : A ⊗[R₀] P₀) : tmap (P₀ := P₀) h₂ (tmap h₁ z) = tmap (h₁.trans h₂) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x p => rfl
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]

lemma tmap_includeRight {A A' : Subalgebra R₀ L} (h : A ≤ A') (p : P₀) :
    tmap h (Algebra.TensorProduct.includeRight p : A ⊗[R₀] P₀) =
      Algebra.TensorProduct.includeRight p := by
  simp [tmap]

lemma tmap_injective [Module.Flat R₀ P₀] {A A' : Subalgebra R₀ L} (h : A ≤ A') :
    Function.Injective (tmap (P₀ := P₀) h) := by
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := P₀)
    (Subalgebra.inclusion h).toLinearMap (Subalgebra.inclusion_injective h)
  convert hinj using 1
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x p => rfl
  | add u v hu hv => simp only [map_add, hu, hv]

variable {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  (F : ι →o Subalgebra R₀ L) (R : Subalgebra R₀ L) (hF : ∀ i, F i ≤ R)
  (hR : ∀ x ∈ R, ∃ i, x ∈ F i)

include hR in
/-- Every element of `R ⊗ P₀` comes from some `F i ⊗ P₀`. -/
lemma exists_tmap_eq (z : R ⊗[R₀] P₀) : ∃ i, ∃ y : F i ⊗[R₀] P₀, tmap (hF i) y = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨Classical.arbitrary ι, 0, map_zero _⟩
  | tmul x p =>
    obtain ⟨i, hi⟩ := hR x.1 x.2
    exact ⟨i, ⟨x.1, hi⟩ ⊗ₜ p, rfl⟩
  | add u v hu hv =>
    obtain ⟨i, y, rfl⟩ := hu
    obtain ⟨i', y', rfl⟩ := hv
    obtain ⟨k, hik, hi'k⟩ := directed_of (· ≤ ·) i i'
    refine ⟨k, tmap (F.monotone hik) y + tmap (F.monotone hi'k) y', ?_⟩
    rw [map_add, tmap_tmap, tmap_tmap]

include hF hR in
/-- **Lemma `lem:sm-fd-colimit-ideal`.** If `1 ⊗ g ∈ 𝔠 (R ⊗ P₀)`, then `1 ⊗ g ∈ 𝔠 (F j ⊗ P₀)`
for all large `j`. -/
theorem exists_mem_map_of_mem_map [Module.Flat R₀ P₀] (𝔠 : Ideal P₀) {g : P₀}
    (hg : (Algebra.TensorProduct.includeRight g : R ⊗[R₀] P₀) ∈
      𝔠.map (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] R ⊗[R₀] P₀)) :
    ∃ i, ∀ j, F i ≤ F j → (Algebra.TensorProduct.includeRight g : F j ⊗[R₀] P₀) ∈
      𝔠.map (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] F j ⊗[R₀] P₀) := by
  -- every element of `𝔠 (R ⊗ P₀)` lifts to `𝔠 (F j ⊗ P₀)` for all large `j`
  have key : ∀ z ∈ 𝔠.map (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] R ⊗[R₀] P₀),
      ∃ i, ∀ j, F i ≤ F j → ∃ y ∈ 𝔠.map (Algebra.TensorProduct.includeRight :
        P₀ →ₐ[R₀] F j ⊗[R₀] P₀), tmap (hF j) y = z := by
    intro z hz
    refine Submodule.span_induction (p := fun z _ => ∃ i, ∀ j, F i ≤ F j → ∃ y ∈ 𝔠.map
        (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] F j ⊗[R₀] P₀), tmap (hF j) y = z)
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨e, he, rfl⟩
      exact ⟨Classical.arbitrary ι, fun j _ => ⟨_, Ideal.mem_map_of_mem _ he,
        tmap_includeRight _ e⟩⟩
    · exact ⟨Classical.arbitrary ι, fun j _ => ⟨0, zero_mem _, map_zero _⟩⟩
    · rintro x x' - - ⟨i, hi⟩ ⟨i', hi'⟩
      obtain ⟨k, hik, hi'k⟩ := directed_of (· ≤ ·) i i'
      refine ⟨k, fun j hj => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hi j ((F.monotone hik).trans hj)
      obtain ⟨y', hy', rfl⟩ := hi' j ((F.monotone hi'k).trans hj)
      exact ⟨y + y', add_mem hy hy', map_add _ _ _⟩
    · rintro c x - ⟨i, hi⟩
      obtain ⟨ic, yc, rfl⟩ := exists_tmap_eq F R hF hR c
      obtain ⟨k, hik, hick⟩ := directed_of (· ≤ ·) i ic
      refine ⟨k, fun j hj => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hi j ((F.monotone hik).trans hj)
      refine ⟨tmap ((F.monotone hick).trans hj) yc * y, Ideal.mul_mem_left _ _ hy, ?_⟩
      rw [map_mul, tmap_tmap, smul_eq_mul]
  obtain ⟨i, hi⟩ := key _ hg
  refine ⟨i, fun j hj => ?_⟩
  obtain ⟨y, hy, hyeq⟩ := hi j hj
  rw [← tmap_includeRight (hF j) g] at hyeq
  rw [← tmap_injective (hF j) hyeq]
  exact hy

include hF hR in
/-- The generators of `J₀ ∩ 𝔭P₀` lie in `𝔭 J₀ (F j ⊗ P₀)` for all large `j`, when
`(R ⊗ P₀) / J₀` is flat over `R`. -/
lemma exists_index_mem_mul [IsNoetherianRing P₀] [Module.Flat R₀ P₀] (J₀ : Ideal P₀)
    (𝔭 : Ideal R₀) [Module.Flat R ((R ⊗[R₀] P₀) ⧸ extIdeal R₀ J₀ R)] :
    ∃ i, ∀ j, F i ≤ F j → ∀ e ∈ J₀ ⊓ 𝔭.map (algebraMap R₀ P₀),
      (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] F j ⊗[R₀] P₀) e ∈
        𝔭.map (algebraMap R₀ (F j ⊗[R₀] P₀)) * extIdeal R₀ J₀ (F j) := by
  classical
  let 𝔠 : Ideal P₀ := 𝔭.map (algebraMap R₀ P₀) * J₀
  have hc : ∀ (A : Type _) [CommRing A] [Algebra R₀ A],
      𝔠.map (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] A ⊗[R₀] P₀) =
        𝔭.map (algebraMap R₀ (A ⊗[R₀] P₀)) * extIdeal R₀ J₀ A := by
    intro A _ _
    rw [Ideal.map_mul, map_includeRight_algebraMap_eq]
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (J₀ ⊓ 𝔭.map (algebraMap R₀ P₀)) :
    (J₀ ⊓ 𝔭.map (algebraMap R₀ P₀)).FG)
  -- each generator descends to some stage
  have hgen : ∀ g ∈ s, ∃ i, ∀ j, F i ≤ F j →
      (Algebra.TensorProduct.includeRight g : F j ⊗[R₀] P₀) ∈
        𝔠.map (Algebra.TensorProduct.includeRight : P₀ →ₐ[R₀] F j ⊗[R₀] P₀) := by
    intro g hg
    have hgT : g ∈ J₀ ⊓ 𝔭.map (algebraMap R₀ P₀) := hs ▸ Submodule.subset_span hg
    obtain ⟨hgJ, hg𝔭⟩ := Submodule.mem_inf.mp hgT
    apply exists_mem_map_of_mem_map F R hF hR 𝔠
    rw [hc, ← map_algebraMap_eq R 𝔭]
    apply inf_le_mul_of_flat_quotient
    refine Submodule.mem_inf.mpr ⟨Ideal.mem_map_of_mem _ hgJ, ?_⟩
    rw [map_algebraMap_eq, ← map_includeRight_algebraMap_eq]
    exact Ideal.mem_map_of_mem _ hg𝔭
  choose! idx hidx using hgen
  obtain ⟨M, hM⟩ := Finset.exists_le (s.image idx)
  refine ⟨M, fun j hj e he => ?_⟩
  rw [← hc]
  have hle : J₀ ⊓ 𝔭.map (algebraMap R₀ P₀) ≤ (𝔠.map (Algebra.TensorProduct.includeRight :
      P₀ →ₐ[R₀] F j ⊗[R₀] P₀)).comap (Algebra.TensorProduct.includeRight :
        P₀ →ₐ[R₀] F j ⊗[R₀] P₀) := by
    rw [← hs, Submodule.span_le]
    intro g hg
    exact hidx g hg j ((F.monotone (hM _ (Finset.mem_image_of_mem idx hg))).trans hj)
  exact hle he

/-- The multiplier condition at a maximal ideal `𝔪` of `A ⊗ P₀`. -/
def Good (A : Type*) [CommRing A] [Algebra R₀ A] (J₀ : Ideal P₀)
    (𝔪 : Ideal (A ⊗[R₀] P₀)) : Prop :=
  ∀ (𝔟 : Ideal A) (x : A ⊗[R₀] P₀), x ∈ extIdeal R₀ J₀ A ⊓ 𝔟.map (algebraMap A (A ⊗[R₀] P₀)) →
    ∃ s ∉ 𝔪, s * x ∈ 𝔟.map (algebraMap A (A ⊗[R₀] P₀)) * extIdeal R₀ J₀ A

/-- If the multiplier condition holds at every maximal ideal, `(A ⊗ P₀) / J₀` is flat over `A`
(Lemma `lem:sm-fd-flat-quotient` (2)). -/
lemma flat_of_good [Module.Flat R₀ P₀] (A : Type*) [CommRing A] [Algebra R₀ A] (J₀ : Ideal P₀)
    (h : ∀ 𝔪 : Ideal (A ⊗[R₀] P₀), 𝔪.IsMaximal → Good A J₀ 𝔪) :
    Module.Flat A ((A ⊗[R₀] P₀) ⧸ extIdeal R₀ J₀ A) := by
  apply flat_quotient_of_inf_le_mul
  intro 𝔟 x hx
  let Q : Ideal (A ⊗[R₀] P₀) :=
    (𝔟.map (algebraMap A (A ⊗[R₀] P₀)) * extIdeal R₀ J₀ A).colon {x}
  have hQ : Q = ⊤ := by
    by_contra hQ
    obtain ⟨𝔪, h𝔪, hQ𝔪⟩ := Ideal.exists_le_maximal Q hQ
    obtain ⟨s, hs, hsx⟩ := h 𝔪 h𝔪 𝔟 x hx
    exact hs (hQ𝔪 (Submodule.mem_colon_singleton.mpr hsx))
  have h1 : (1 : A ⊗[R₀] P₀) ∈ Q := by rw [hQ]; exact Submodule.mem_top
  simpa using Submodule.mem_colon_singleton.mp h1

/-- An ideal `𝔠` of `R₀` is *settled* if the multiplier condition holds at all large stages at
the maximal ideals lying over `V(𝔠)`. -/
def Settled (J₀ : Ideal P₀) (𝔠 : Ideal R₀) : Prop :=
  ∃ i, ∀ j, F i ≤ F j → ∀ 𝔪 : Ideal (F j ⊗[R₀] P₀), 𝔪.IsMaximal →
    𝔠 ≤ 𝔪.comap (algebraMap R₀ (F j ⊗[R₀] P₀)) → Good (F j) J₀ 𝔪

end Union

section Main

variable {R₀ : Type u} [CommRing R₀] {L : Type v} [CommRing L] [Algebra R₀ L]
  {P₀ : Type*} [CommRing P₀] [Algebra R₀ P₀]
  {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  (F : ι →o Subalgebra R₀ L) (R : Subalgebra R₀ L) (hF : ∀ i, F i ≤ R)
  (hR : ∀ x ∈ R, ∃ i, x ∈ F i)

omit [IsDirected ι (· ≤ ·)] in
lemma settled_top (J₀ : Ideal P₀) : Settled F J₀ ⊤ := by
  refine ⟨Classical.arbitrary ι, fun j _ 𝔪 h𝔪 htop => ?_⟩
  exfalso
  have : (1 : R₀) ∈ 𝔪.comap (algebraMap R₀ (F j ⊗[R₀] P₀)) := htop Submodule.mem_top
  rw [Ideal.mem_comap, map_one] at this
  exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr this)

omit [Nonempty ι] in
lemma settled_of_mul_mem (J₀ : Ideal P₀) {𝔠 : Ideal R₀} {u v : R₀} (huv : u * v ∈ 𝔠)
    (hu : Settled F J₀ (𝔠 ⊔ Ideal.span {u})) (hv : Settled F J₀ (𝔠 ⊔ Ideal.span {v})) :
    Settled F J₀ 𝔠 := by
  obtain ⟨i₁, h₁⟩ := hu
  obtain ⟨i₂, h₂⟩ := hv
  obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) i₁ i₂
  refine ⟨k, fun j hj 𝔪 h𝔪 h𝔠 => ?_⟩
  have hprime := (h𝔪.isPrime).comap (algebraMap R₀ (F j ⊗[R₀] P₀))
  rcases hprime.mem_or_mem (h𝔠 huv) with hu' | hv'
  · exact h₁ j ((F.monotone hk₁).trans hj) 𝔪 h𝔪
      (sup_le h𝔠 ((Ideal.span_singleton_le_iff_mem _).mpr hu'))
  · exact h₂ j ((F.monotone hk₂).trans hj) 𝔪 h𝔪
      (sup_le h𝔠 ((Ideal.span_singleton_le_iff_mem _).mpr hv'))

include hF hR in
/-- The induction step at a prime ideal `𝔭`: generic flatness over `R₀ ⧸ 𝔭` and the local
criterion over `V(𝔭) ∩ D(a)`. -/
lemma settled_of_isPrime [IsNoetherianRing R₀] [Algebra.FiniteType R₀ P₀] [Module.Flat R₀ P₀]
    (hnoeth : ∀ i, IsNoetherianRing (F i)) (J₀ : Ideal P₀)
    [Module.Flat R ((R ⊗[R₀] P₀) ⧸ extIdeal R₀ J₀ R)] (𝔭 : Ideal R₀) [𝔭.IsPrime]
    (ih : ∀ 𝔠 : Ideal R₀, 𝔭 < 𝔠 → Settled F J₀ 𝔠) : Settled F J₀ 𝔭 := by
  have : IsNoetherianRing P₀ := Algebra.FiniteType.isNoetherianRing R₀ P₀
  -- generic flatness over `R₀ ⧸ 𝔭`
  set 𝔭P := 𝔭.map (algebraMap R₀ P₀)
  have : Algebra.FiniteType R₀ (P₀ ⧸ 𝔭P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R₀ 𝔭P) (Ideal.Quotient.mkₐ_surjective _ _)
  have : Algebra.FiniteType (R₀ ⧸ 𝔭) (P₀ ⧸ 𝔭P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R₀ (R₀ ⧸ 𝔭) (P₀ ⧸ 𝔭P)
  obtain ⟨b, hb, hflat⟩ := exists_flat_localizedModule (D := R₀ ⧸ 𝔭) (B := P₀ ⧸ 𝔭P)
    ((P₀ ⧸ 𝔭P) ⧸ J₀.map (Ideal.Quotient.mkₐ R₀ 𝔭P))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ha : a ∉ 𝔭 := fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  -- `V(𝔭 + (a))` by induction, `V(𝔭) ∩ D(a)` by the local criterion
  obtain ⟨i₁, h₁⟩ := ih (𝔭 ⊔ Ideal.span {a}) (lt_of_le_of_ne le_sup_left fun h =>
    ha (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))
  obtain ⟨i₂, h₂⟩ := exists_index_mem_mul F R hF hR J₀ 𝔭
  obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) i₁ i₂
  refine ⟨k, fun j hj 𝔪 h𝔪 h𝔭 => ?_⟩
  by_cases haj : a ∈ 𝔪.comap (algebraMap R₀ (F j ⊗[R₀] P₀))
  · exact h₁ j ((F.monotone hk₁).trans hj) 𝔪 h𝔪
      (sup_le h𝔭 ((Ideal.span_singleton_le_iff_mem _).mpr haj))
  · have := hnoeth j
    have : IsNoetherianRing (F j ⊗[R₀] P₀) :=
      Algebra.FiniteType.isNoetherianRing (F j) (F j ⊗[R₀] P₀)
    intro 𝔟 x hx
    obtain ⟨N, s, hs, hsx⟩ := exists_sub_pow_mul_mem J₀ 𝔭 a (F j)
      (h₂ j ((F.monotone hk₂).trans hj)) 𝔟 hx
    refine ⟨s, fun hs𝔪 => haj ?_, hsx⟩
    have h𝔭𝔪 : 𝔭.map (algebraMap R₀ (F j ⊗[R₀] P₀)) ≤ 𝔪 := Ideal.map_le_iff_le_comap.mpr h𝔭
    have hpow : algebraMap R₀ (F j ⊗[R₀] P₀) a ^ N ∈ 𝔪 := by
      have := Ideal.sub_mem _ hs𝔪 (h𝔭𝔪 hs)
      rwa [sub_sub_cancel] at this
    exact Ideal.mem_comap.mpr ((h𝔪.isPrime).mem_of_pow_mem N hpow)

set_option synthInstance.maxHeartbeats 200000 in
include hF hR in
/-- **Theorem `thm:sm-flatness-descent`, presentation form.** Let `R₀` be noetherian, `P₀` a flat
`R₀`-algebra of finite type, `J₀ ⊆ P₀` an ideal, and `R ⊆ L` the union of a directed family of
noetherian `R₀`-subalgebras `F i`. If `(R ⊗ P₀) / J₀` is flat over `R`, then
`(F j ⊗ P₀) / J₀` is flat over `F j` for all `j` with `F i ≤ F j`, for some `i`. -/
theorem flat_quotient_of_flat_quotient_union [IsNoetherianRing R₀] [Algebra.FiniteType R₀ P₀]
    [Module.Flat R₀ P₀] (hnoeth : ∀ i, IsNoetherianRing (F i)) (J₀ : Ideal P₀)
    [Module.Flat R ((R ⊗[R₀] P₀) ⧸ extIdeal R₀ J₀ R)] :
    ∃ i, ∀ j, F i ≤ F j → Module.Flat (F j) ((F j ⊗[R₀] P₀) ⧸ extIdeal R₀ J₀ (F j)) := by
  have hall : ∀ 𝔠 : Ideal R₀, Settled F J₀ 𝔠 := by
    intro 𝔠
    induction 𝔠 using WellFoundedGT.induction with
    | _ 𝔠 ih =>
      by_cases htop : 𝔠 = ⊤
      · rw [htop]; exact settled_top F J₀
      by_cases hprime : 𝔠.IsPrime
      · exact settled_of_isPrime F R hF hR hnoeth J₀ 𝔠 ih
      · have : ∃ u v, u * v ∈ 𝔠 ∧ u ∉ 𝔠 ∧ v ∉ 𝔠 := by
          by_contra hcon
          push Not at hcon
          exact hprime ⟨htop, fun {u v} huv => by
            by_contra h
            push Not at h
            exact h.2 (hcon u v huv h.1)⟩
        obtain ⟨u, v, huv, hu, hv⟩ := this
        refine settled_of_mul_mem F J₀ huv (ih _ ?_) (ih _ ?_)
        · exact lt_of_le_of_ne le_sup_left fun h =>
            hu (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self u))
        · exact lt_of_le_of_ne le_sup_left fun h =>
            hv (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self v))
  obtain ⟨i, hi⟩ := hall ⊥
  exact ⟨i, fun j hj => flat_of_good (F j) J₀ fun 𝔪 h𝔪 => hi j hj 𝔪 h𝔪 bot_le⟩

set_option synthInstance.maxHeartbeats 200000 in
include hF hR in
/-- **Theorem `thm:sm-flatness-descent` (descent of flatness along directed unions).** Let `R₀`
be a noetherian ring, `L` an `R₀`-algebra, `F i` a directed family of noetherian
`R₀`-subalgebras of `L` with union `R`, and `B₀` an `R₀`-algebra of finite type. If
`R ⊗[R₀] B₀` is flat over `R`, then `F j ⊗[R₀] B₀` is flat over `F j` for all `j` with
`F i ≤ F j`, for some `i`. -/
theorem flat_tensor_of_flat_tensor_union [IsNoetherianRing R₀] (hnoeth : ∀ i, IsNoetherianRing (F i))
    (B₀ : Type*) [CommRing B₀] [Algebra R₀ B₀] [Algebra.FiniteType R₀ B₀]
    [Module.Flat R (R ⊗[R₀] B₀)] :
    ∃ i, ∀ j, F i ≤ F j → Module.Flat (F j) (F j ⊗[R₀] B₀) := by
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R₀) (S := B₀)).mp
    inferInstance
  let J₀ := RingHom.ker f
  -- `A ⊗ B₀ ≅ (A ⊗ P₀) / J₀` for every `R₀`-algebra `A`
  let e : ∀ (A : Type _) [CommRing A] [Algebra R₀ A],
      (A ⊗[R₀] B₀) ≃ₐ[A] (A ⊗[R₀] MvPolynomial (Fin n) R₀) ⧸ extIdeal R₀ J₀ A :=
    fun A _ _ => (Algebra.TensorProduct.congr AlgEquiv.refl
      (Ideal.quotientKerAlgEquivOfSurjective hf).symm).trans
        (Algebra.TensorProduct.tensorQuotientEquiv A (MvPolynomial (Fin n) R₀) A J₀)
  have : Module.Flat R ((R ⊗[R₀] MvPolynomial (Fin n) R₀) ⧸ extIdeal R₀ J₀ R) :=
    Module.Flat.of_linearEquiv (e R).symm.toLinearEquiv
  obtain ⟨i, hi⟩ := flat_quotient_of_flat_quotient_union F R hF hR hnoeth J₀
  refine ⟨i, fun j hj => ?_⟩
  have := hi j hj
  exact Module.Flat.of_linearEquiv (e (F j)).toLinearEquiv

include hF hR in
/-- `flat_tensor_of_flat_tensor_union` in the form "for all `j ≥ i`". -/
theorem exists_forall_ge_flat_tensor [IsNoetherianRing R₀] (hnoeth : ∀ i, IsNoetherianRing (F i))
    (B₀ : Type*) [CommRing B₀] [Algebra R₀ B₀] [Algebra.FiniteType R₀ B₀]
    [Module.Flat R (R ⊗[R₀] B₀)] :
    ∃ i, ∀ j, i ≤ j → Module.Flat (F j) (F j ⊗[R₀] B₀) := by
  obtain ⟨i, hi⟩ := flat_tensor_of_flat_tensor_union F R hF hR hnoeth B₀
  exact ⟨i, fun j hj => hi j (F.monotone hj)⟩

end Main

end DeJongAlterations.StableModification.Limits.FlatDescent
