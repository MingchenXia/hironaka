import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Descent of a standard étale algebra to a subring

Let `O` be a standard étale algebra over a ring `Ō` (`Algebra.IsStandardEtale Ō O`), and
`A ⊆ O` a finite set. This file shows (`exists_finset_standardEtale_descent`) that there is a
finite set `G ⊆ Ō` such that for every injective ring map `ι : B̄ → Ō` whose image contains `G`,
the standard étale presentation of `O` descends to a standard étale `B̄`-algebra `E` with an
injective map `E → O` over `ι` whose image contains `A`.

This replaces, in our proof of M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), Proposition 4.3.3 (`locunifprop`, `semi-stable.tex`
lines 3076–3079: "By [EGA IV₄, 17.7.8], `A ⊗_Ā 𝒪_{C̄ᵢ,x̄ᵢ}` is étale over `𝒪_{C̄ᵢ,x̄ᵢ}` for some
`i`"), the flattening theorem of line 3065 together with EGA IV 17.7.8 (plan `PLAN-SM-GEOM.md`,
S7). The descended algebra is `E = B̄[X]_{g'}/(f')` for lifts `f', g'` of the presentation
`O ≅ Ō[X]_g/(f)`; injectivity of `E → O` comes from `O ≅ Ō ⊗_{B̄} E` and the flatness of `E`
over `B̄`. Blueprint `lem:sm-lu-curve-etale-descent` (`sm-local-uniformization-curve.tex`).
-/

noncomputable section

open Polynomial TensorProduct

universe u

namespace DeJongAlterations.StableModification.LocalUniformization.Curve

/-- A polynomial whose coefficients lie in the image of `ι` lifts along `ι`. -/
theorem mem_lifts_of_coeffs_subset {Bb Ob : Type*} [CommRing Bb] [CommRing Ob] (ι : Bb →+* Ob)
    (q : Ob[X]) (h : ∀ c ∈ q.coeffs, c ∈ ι.range) : q ∈ lifts ι := by
  refine (lifts_iff_coeff_lifts q).mpr fun n ↦ ?_
  by_cases hn : q.coeff n = 0
  · exact ⟨0, by rw [hn, map_zero]⟩
  · obtain ⟨b, hb⟩ := h _ (coeff_mem_coeffs hn)
    exact ⟨b, hb⟩

/-- **Descent of a standard étale algebra** (blueprint `lem:sm-lu-curve-etale-descent`). -/
theorem exists_finset_standardEtale_descent {Ob O : Type u} [CommRing Ob] [CommRing O]
    [Algebra Ob O] [Algebra.IsStandardEtale Ob O] (A : Finset O) :
    ∃ G : Finset Ob, ∀ (Bb : Type u) [CommRing Bb] (ι : Bb →+* Ob), Function.Injective ι →
      (∀ c ∈ G, c ∈ ι.range) →
      ∃ (E : Type u) (_ : CommRing E) (_ : Algebra Bb E) (φ : E →+* O),
        Algebra.IsStandardEtale Bb E ∧ Function.Injective φ ∧
        φ.comp (algebraMap Bb E) = (algebraMap Ob O).comp ι ∧ ∀ a ∈ A, a ∈ φ.range := by
  classical
  obtain ⟨⟨⟨f, hf, g, hcond⟩, x, hx, hbij⟩⟩ :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := Ob) (S := O)
  obtain ⟨p₁, p₂, n, hpn⟩ := hcond
  have hpa : ∀ a : O, ∃ p : Ob[X], ∃ m : ℕ, a * aeval x g ^ m = aeval x p := fun a ↦
    (StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x
      ⟨⟨f, hf, g, ⟨p₁, p₂, n, hpn⟩⟩, x, hx, hbij⟩ a)
  choose pa ma hpa using hpa
  refine ⟨f.coeffs ∪ g.coeffs ∪ p₁.coeffs ∪ p₂.coeffs ∪ A.biUnion fun a ↦ (pa a).coeffs,
    fun Bb _ ι hι hG ↦ ?_⟩
  have hl : ∀ q : Ob[X], (∀ c ∈ q.coeffs, c ∈ ι.range) → q ∈ lifts ι :=
    mem_lifts_of_coeffs_subset ι
  obtain ⟨f', hf', -, hf'm⟩ := lifts_and_natDegree_eq_and_monic
    (hl f fun c hc ↦ hG c (by simp [hc])) hf
  obtain ⟨g', hg'⟩ := hl g fun c hc ↦ hG c (by simp [hc])
  obtain ⟨q₁, hq₁⟩ := hl p₁ fun c hc ↦ hG c (by simp [hc])
  obtain ⟨q₂, hq₂⟩ := hl p₂ fun c hc ↦ hG c (by simp [hc])
  have hqa : ∀ a ∈ A, ∃ q : Bb[X], q.map ι = pa a := fun a ha ↦
    hl (pa a) fun c hc ↦ hG c (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, ha, hc⟩))
  simp only [Polynomial.coe_mapRingHom] at hg' hq₁ hq₂
  subst hf' hg'
  have hcond' : derivative f' * q₁ + f' * q₂ = g' ^ n := by
    apply Polynomial.map_injective ι hι
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      hq₁, hq₂, Polynomial.map_pow, hpn]
  let P' : StandardEtalePair Bb := ⟨f', hf'm, g', ⟨q₁, q₂, n, hcond'⟩⟩
  let := ι.toAlgebra
  let : Algebra Bb O := ((algebraMap Ob O).comp ι).toAlgebra
  have : IsScalarTower Bb Ob O := IsScalarTower.of_algebraMap_eq' rfl
  have haeval : ∀ q : Bb[X], aeval x q = aeval x (q.map ι) := fun q ↦ by
    rw [← aeval_map_algebraMap Ob]
    rfl
  have hmap : P'.HasMap x := ⟨by
    change aeval x f' = 0
    rw [haeval]
    exact hx.1, by
    change IsUnit (aeval x g')
    rw [haeval]
    exact hx.2⟩
  let φ := P'.lift x hmap
  refine ⟨P'.Ring, inferInstance, inferInstance, φ.toRingHom, inferInstance, ?_, ?_, ?_⟩
  · -- injectivity through `Ob ⊗_{Bb} E ≅ O`
    let PE : StandardEtalePresentation Bb P'.Ring :=
      ⟨P', P'.X, P'.hasMap_X, by simpa using Function.bijective_id⟩
    let BC := PE.baseChange (T := Ob)
    let θ : Ob ⊗[Bb] P'.Ring →ₐ[Ob] O :=
      Algebra.TensorProduct.lift (Algebra.ofId Ob O) φ fun _ _ ↦ Commute.all _ _
    let Pmap : StandardEtalePair Ob := ⟨f'.map ι, hf, g'.map ι, ⟨p₁, p₂, n, hpn⟩⟩
    have hθ : θ = (Pmap.lift x hx).comp BC.equivRing.toAlgHom := by
      apply BC.hom_ext
      change θ (1 ⊗ₜ P'.X) = Pmap.lift x hx (BC.equivRing BC.x)
      rw [BC.equivRing_x]
      have key : (Pmap.lift x hx) Pmap.X = x := StandardEtalePair.lift_X _ _ _
      change θ (1 ⊗ₜ P'.X) = Pmap.lift x hx Pmap.X
      rw [key, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact P'.lift_X x hmap
    have hθinj : Function.Injective θ := by
      rw [hθ]
      exact hbij.1.comp BC.equivRing.injective
    have hincl : Function.Injective (Algebra.TensorProduct.includeRight :
        P'.Ring →ₐ[Bb] Ob ⊗[Bb] P'.Ring) := by
      have h1 : Function.Injective ((Algebra.linearMap Bb Ob).rTensor P'.Ring) :=
        Module.Flat.rTensor_preserves_injective_linearMap _ hι
      have h2 : ∀ e : P'.Ring, (Algebra.TensorProduct.includeRight : P'.Ring →ₐ[Bb] _) e =
          (Algebra.linearMap Bb Ob).rTensor P'.Ring ((TensorProduct.lid Bb P'.Ring).symm e) := by
        intro e
        simp [Algebra.TensorProduct.includeRight_apply]
      intro e₁ e₂ he
      rw [h2, h2] at he
      exact (TensorProduct.lid Bb P'.Ring).symm.injective (h1 he)
    intro e₁ e₂ he
    apply hincl
    apply hθinj
    change θ (1 ⊗ₜ e₁) = θ (1 ⊗ₜ e₂)
    rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
      one_mul]
    exact he
  · ext b
    exact φ.commutes b
  · intro a ha
    obtain ⟨q, hq⟩ := hqa a ha
    have hu := P'.hasMap_X.2
    refine ⟨aeval P'.X q * ((hu.unit⁻¹ : (P'.Ring)ˣ) : P'.Ring) ^ ma a, ?_⟩
    have hφX : φ P'.X = x := P'.lift_X x hmap
    have hφq : φ (aeval P'.X q) = aeval x (pa a) := by
      rw [← aeval_algHom_apply, hφX, haeval, hq]
    have hφg : φ (aeval P'.X g') = aeval x (g'.map ι) := by
      rw [← aeval_algHom_apply, hφX, haeval]
    have hux : IsUnit (aeval x (g'.map ι)) := hx.2
    change φ (aeval P'.X q * ((hu.unit⁻¹ : (P'.Ring)ˣ) : P'.Ring) ^ ma a) = a
    rw [map_mul, map_pow, hφq, ← hpa a]
    have hinv : φ ((hu.unit⁻¹ : (P'.Ring)ˣ) : P'.Ring) * aeval x (g'.map ι) = 1 := by
      rw [← hφg, ← map_mul, IsUnit.val_inv_mul, map_one]
    calc a * aeval x (g'.map ι) ^ ma a * φ ((hu.unit⁻¹ : (P'.Ring)ˣ) : P'.Ring) ^ ma a
        = a * (φ ((hu.unit⁻¹ : (P'.Ring)ˣ) : P'.Ring) * aeval x (g'.map ι)) ^ ma a := by ring
      _ = a := by rw [hinv, one_pow, mul_one]

end DeJongAlterations.StableModification.LocalUniformization.Curve
