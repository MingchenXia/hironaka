import Hironaka.Analytic.Unibranch.HironakaG10GfModStart
import Hironaka.Resolution.HironakaRelativeNormalCoefficientPolynomialBaseChange
import Hironaka.Resolution.HironakaRelativeNormalCoefficientFunctionAlgebra

/-!
# Generic freeness over an irreducible analytic base, uniformly for all nearby points (route N, item N2)

Lane G10GN, run 0081 (`work/hironaka-run0081-20261117/G10GN/hGF-route.md`, item G10GN-N2). Let `B ∋ 0` be open in
`ℂᵈ`, `C0` a finite-type ℂ-algebra of functions holomorphic near every point of `B`, and `Q` a family of
polynomials over `C0`. Let `P ⊆ ℂᵈ` be a set whose germ at `0` is irreducible (its vanishing ideal `I_P(0)` is
prime). **`exists_uniform_free_over_base`**: there are a function `g`, holomorphic on `B`, NOT vanishing
identically on `P` near `0`, and an open `V ∋ 0` such that for every `a ∈ V` with `g a ≠ 0` the polynomial quotient
`(𝒪_a ⧸ I_P(a))[x] ⧸ (Q at a)` is FREE over `𝒪_a ⧸ I_P(a)`.

Proof (Frisch (II,1)(i) / EGA IV 6.9.2 for polynomial quotients, with ONE denominator for all nearby points): the
coefficient domain `D := C0 ⧸ ker(C0 → 𝒪_0 ⧸ I_P(0))` (a domain: `I_P(0)` is prime); the library's uniform leading
denominator `b ∈ D` (standard monomials w.r.t. `degLex`, `uniformLeadingDenominator`) makes the quotient free after
any base change sending `b` to a unit (`moduleFree_coefficient_image_at_uniform_denominator`). The kernel is
finitely generated (`C0` is noetherian), so its generators vanish on `P` near `0`, and for `a` near `0` the germ map
at `a` factors through `D`; `g` represents a lift of `b`.

BP: hironaka-g10gn-base-free.tex.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GnBaseFree

noncomputable section

open Hironaka Hironaka
open HolGerm OkaRelationSheaf AnalyticGermDecomposition HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalNearbyPolynomialCoefficientGerms
  HironakaRelativeNormalCoefficientFunctionAlgebra HironakaRelativeNormalUniformLocalization
  HironakaRelativeNormalCoefficientPolynomialBaseChange Hironaka.Analytic.Unibranch.HironakaG10GfModStart

attribute [local instance] coefficientSubalgebraRing

variable {d t : ℕ}

/-- The germ map at `a` of the coefficient algebra, followed by the quotient by `I_P(a)`. -/
abbrev baseGermHom {B : Set (ComplexModel d)} (C0 : Subalgebra ℂ (coefficientFunctionAlgebra d B))
    (P : Set (ComplexModel d)) (a : ComplexModel d) (ha : a ∈ B) :
    C0 →+* HolGerm (ComplexModel d) ⧸ baseIdeal P a :=
  (Ideal.Quotient.mk (baseIdeal P a)).comp ((coefficientGermHom d B a ha).comp C0.val).toRingHom

theorem coefficientGermHom_apply {B : Set (ComplexModel d)} (a : ComplexModel d) (ha : a ∈ B)
    (f : coefficientFunctionAlgebra d B) :
    coefficientGermHom d B a ha f = HolGerm.mk (f.val ∘ actualAffineTranslation d a)
      (actualCoefficientFunctionTranslation_holomorphic d a f.val (f.property a ha)) := rfl

/-- A coefficient function lies in the kernel at `a` iff it vanishes on `P` near `a`. -/
theorem baseGermHom_eq_zero_iff {B : Set (ComplexModel d)}
    (C0 : Subalgebra ℂ (coefficientFunctionAlgebra d B)) (P : Set (ComplexModel d)) (a : ComplexModel d)
    (ha : a ∈ B) (f : C0) :
    baseGermHom C0 P a ha f = 0 ↔ ∀ᶠ w in 𝓝 (0 : ComplexModel d), a + w ∈ P → (C0.val f).val (a + w) = 0 := by
  change Ideal.Quotient.mk (baseIdeal P a) (coefficientGermHom d B a ha (C0.val f)) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, coefficientGermHom_apply, baseIdeal, mem_vanishingIdeal_mk]
  rfl

/-- **Generic freeness over an irreducible base, one denominator for all nearby points.** -/
theorem exists_uniform_free_over_base {B : Set (ComplexModel d)} (hB : IsOpen B)
    (h0 : (0 : ComplexModel d) ∈ B) (C0 : Subalgebra ℂ (coefficientFunctionAlgebra d B))
    (hC0 : Algebra.FiniteType ℂ C0) {ι : Type*} (Q : ι → MvPolynomial (Fin t) C0)
    (P : Set (ComplexModel d)) (hP : (baseIdeal P 0).IsPrime) :
    ∃ g : ComplexModel d → ℂ, (∀ a ∈ B, HolAt g a) ∧
      (¬ ∀ᶠ w in 𝓝 (0 : ComplexModel d), w ∈ P → g w = 0) ∧
      ∃ V : Set (ComplexModel d), IsOpen V ∧ (0 : ComplexModel d) ∈ V ∧ ∃ hVB : V ⊆ B,
        ∀ a (ha : a ∈ V), g a ≠ 0 →
          Module.Free (HolGerm (ComplexModel d) ⧸ baseIdeal P a)
            (MvPolynomial (Fin t) (HolGerm (ComplexModel d) ⧸ baseIdeal P a) ⧸
              (Ideal.span (range Q)).map (MvPolynomial.map (baseGermHom C0 P a (hVB ha)))) := by
  classical
  have hnoeth : IsNoetherianRing C0 := Algebra.FiniteType.isNoetherianRing ℂ C0
  let φ₀ := baseGermHom C0 P 0 h0
  let 𝔨 : Ideal C0 := RingHom.ker φ₀
  have : (𝔨).IsPrime := RingHom.ker_isPrime φ₀
  let D := C0 ⧸ 𝔨
  let : Field (FractionRing D) := FractionRing.field D
  -- the kernel is finitely generated; its generators vanish on `P` near `0`
  obtain ⟨S, hS⟩ : 𝔨.FG := IsNoetherian.noetherian 𝔨
  have hvan : ∀ f ∈ S, ∀ᶠ w in 𝓝 (0 : ComplexModel d), w ∈ P → (C0.val f).val w = 0 := by
    intro f hf
    have hk : f ∈ 𝔨 := hS ▸ Ideal.subset_span hf
    have h := (baseGermHom_eq_zero_iff C0 P 0 h0 f).mp hk
    simpa only [zero_add] using h
  have hall : ∀ᶠ w in 𝓝 (0 : ComplexModel d), ∀ f ∈ S, w ∈ P → (C0.val f).val w = 0 :=
    (eventually_all_finset S).mpr hvan
  obtain ⟨U, hUsub, hU, h0U⟩ := mem_nhds_iff.mp hall
  let V := U ∩ B
  have hV : IsOpen V := hU.inter hB
  have hVB : V ⊆ B := fun _ hx => hx.2
  -- the kernel at `0` is contained in the kernel at every `a ∈ V`
  have hker : ∀ a (ha : a ∈ V), 𝔨 ≤ RingHom.ker (baseGermHom C0 P a (hVB ha)) := by
    intro a ha
    rw [← hS]
    apply Ideal.span_le.mpr
    intro f hf
    change baseGermHom C0 P a (hVB ha) f = 0
    rw [baseGermHom_eq_zero_iff]
    have ht : Tendsto (fun w : ComplexModel d => a + w) (𝓝 0) (𝓝 a) :=
      (continuous_const.add continuous_id).tendsto' 0 a (by simp)
    exact (ht.eventually (hU.mem_nhds ha.1)).mono fun w hw hwP => hUsub hw f hf hwP
  let ρ : ∀ a, a ∈ V → D →+* HolGerm (ComplexModel d) ⧸ baseIdeal P a := fun a ha =>
    Ideal.Quotient.lift 𝔨 (baseGermHom C0 P a (hVB ha)) (fun f hf => hker a ha hf)
  have hρ : ∀ a (ha : a ∈ V), (ρ a ha).comp (Ideal.Quotient.mk 𝔨) = baseGermHom C0 P a (hVB ha) :=
    fun a ha => Ideal.Quotient.lift_comp_mk _ _ _
  -- the uniform denominator
  let H : Ideal (MvPolynomial (Fin t) D) :=
    Ideal.span (range fun i => MvPolynomial.map (Ideal.Quotient.mk 𝔨) (Q i))
  let b := uniformLeadingDenominator (K := FractionRing D) t (MonomialOrder.degLex (σ := Fin t)) H
  have hb : b ≠ 0 := uniformLeadingDenominator_ne_zero _ _ _
  obtain ⟨c, hcb⟩ := Ideal.Quotient.mk_surjective b
  let g : ComplexModel d → ℂ := (C0.val c).val
  have hcnot : c ∉ 𝔨 := by
    intro hc
    apply hb
    rw [← hcb]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hc
  refine ⟨g, fun a ha => (C0.val c).property a ha, ?_, V, hV, ⟨h0U, h0⟩, hVB, ?_⟩
  · intro hz
    apply hcnot
    change baseGermHom C0 P 0 h0 c = 0
    rw [baseGermHom_eq_zero_iff]
    simpa only [zero_add] using hz
  · intro a ha hga
    have hunit : IsUnit (ρ a ha b) := by
      rw [← hcb]
      change IsUnit (((ρ a ha).comp (Ideal.Quotient.mk 𝔨)) c)
      rw [hρ a ha]
      have hg : IsUnit (coefficientGermHom d B a (hVB ha) (C0.val c)) := by
        rw [coefficientGermHom_apply, HolGerm.isUnit_iff_eval_ne_zero, HolGerm.eval_mk]
        simpa only [Function.comp_apply, actualAffineTranslation_zero] using hga
      exact hg.map (Ideal.Quotient.mk (baseIdeal P a))
    have hfree := moduleFree_coefficient_image_at_uniform_denominator (K := FractionRing D)
      t (MonomialOrder.degLex (σ := Fin t)) H (ρ a ha) hunit
    have hmap : H.map (MvPolynomial.map (ρ a ha)) =
        (Ideal.span (range Q)).map (MvPolynomial.map (baseGermHom C0 P a (hVB ha))) := by
      rw [Ideal.map_span, Ideal.map_span]
      congr 1
      ext p
      simp only [mem_image, mem_range, exists_exists_eq_and]
      constructor
      · rintro ⟨i, rfl⟩
        refine ⟨i, ?_⟩
        rw [MvPolynomial.map_map, hρ a ha]
      · rintro ⟨i, rfl⟩
        refine ⟨i, ?_⟩
        rw [MvPolynomial.map_map, hρ a ha]
    rw [hmap] at hfree
    exact hfree

end

end Hironaka.Analytic.Unibranch.HironakaG10GnBaseFree
