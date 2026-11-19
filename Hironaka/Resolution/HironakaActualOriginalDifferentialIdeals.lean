/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOriginalTaylorDerivatives

/-! Entire original differential-generated ideals and every finite closure commute with genuine Taylor extension. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualOriginalDifferentialIdeals
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalTaylorCoefficients
  HironakaActualOriginalFormalTaylor HironakaActualOriginalTaylorDerivatives

/-- The whole original analytic ideal together with actual derivatives of ALL its members. -/
def originalDifferentialIdeal (n : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) :
    Ideal (HolGerm (ComplexModel (0+n))) :=
  I ⊔ Ideal.span {H | ∃ (i : Fin n) (g : HolGerm (ComplexModel (0+n))),
    g ∈ I ∧ H=iteratedDerivativeGerm [normalVector 0 n i] g}

/-- The whole formal ideal together with actual formal derivatives of ALL its members. -/
def formalDifferentialIdeal (n : ℕ) (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Ideal (MvPowerSeries (Fin n) ℂ) :=
  K ⊔ Ideal.span {H | ∃ (i : Fin n) (F : MvPowerSeries (Fin n) ℂ),
    F ∈ K ∧ H=MvPowerSeries.pderiv ℂ i F}

/-- Whole differential-generated ideals commute with genuine original Taylor extension. -/
theorem map_originalDifferentialIdeal (n : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) :
    (originalDifferentialIdeal n I).map (originalTaylorAlgHom n).toRingHom =
      formalDifferentialIdeal n (I.map (originalTaylorAlgHom n).toRingHom) := by
  let T := (originalTaylorAlgHom n).toRingHom
  let K := I.map T
  let J := (originalDifferentialIdeal n I).map T
  have hK : K ≤ J := Ideal.map_mono (show I ≤ originalDifferentialIdeal n I from le_sup_left)
  have hgen (i : Fin n) (g : HolGerm (ComplexModel (0+n))) (hg : g ∈ I) :
      MvPowerSeries.pderiv ℂ i (T g) ∈ J := by
    change MvPowerSeries.pderiv ℂ i (originalTaylorAlgHom n g) ∈ J
    rw [← originalTaylorAlgHom_coordinate_derivative]
    apply Ideal.mem_map_of_mem T
    apply (show Ideal.span _ ≤ originalDifferentialIdeal n I from le_sup_right)
    exact Ideal.subset_span ⟨i,g,hg,rfl⟩
  have hder (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ K) :
      ∀ i : Fin n, MvPowerSeries.pderiv ℂ i F ∈ J := by
    change F ∈ Ideal.map T I at hF
    rw [Ideal.map] at hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
        obtain ⟨g,hg,rfl⟩ := hF
        exact fun i => hgen i g hg
    | zero => intro i; simp
    | add F G _ _ hF hG =>
        intro i
        simpa only [map_add] using J.add_mem (hF i) (hG i)
    | smul a F hF ih =>
        intro i
        change MvPowerSeries.pderiv ℂ i (a*F) ∈ J
        rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul]
        exact J.add_mem (J.mul_mem_left a (ih i)) (J.mul_mem_right _ (hK hF))
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    change I ⊔ Ideal.span _ ≤ Ideal.comap T (formalDifferentialIdeal n K)
    refine sup_le ?_ (Ideal.span_le.mpr ?_)
    · intro g hg
      change T g ∈ formalDifferentialIdeal n K
      exact (show K ≤ formalDifferentialIdeal n K from le_sup_left) (Ideal.mem_map_of_mem T hg)
    · rintro H ⟨i,g,hg,rfl⟩
      change originalTaylorAlgHom n (iteratedDerivativeGerm [normalVector 0 n i] g) ∈ formalDifferentialIdeal n K
      rw [originalTaylorAlgHom_coordinate_derivative]
      apply (show Ideal.span _ ≤ formalDifferentialIdeal n K from le_sup_right)
      exact Ideal.subset_span ⟨i,T g,Ideal.mem_map_of_mem T hg,rfl⟩
  · change K ⊔ Ideal.span _ ≤ J
    refine sup_le hK (Ideal.span_le.mpr ?_)
    rintro H ⟨i,F,hF,rfl⟩
    exact hder F hF i

/-- Actual natural-number iteration of the entire original differential-generated ideal. -/
def originalDifferentialClosure (n : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) :
    ℕ → Ideal (HolGerm (ComplexModel (0+n)))
  | 0 => I
  | q+1 => originalDifferentialIdeal n (originalDifferentialClosure n I q)

/-- Actual natural-number iteration of the entire formal differential-generated ideal. -/
def formalDifferentialClosure (n : ℕ) (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    ℕ → Ideal (MvPowerSeries (Fin n) ℂ)
  | 0 => K
  | q+1 => formalDifferentialIdeal n (formalDifferentialClosure n K q)

/-- Every finite whole differential closure commutes with the same genuine original Taylor map. -/
theorem map_originalDifferentialClosure (n : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n))))
    (q : ℕ) :
    (originalDifferentialClosure n I q).map (originalTaylorAlgHom n).toRingHom =
      formalDifferentialClosure n (I.map (originalTaylorAlgHom n).toRingHom) q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      change (originalDifferentialIdeal n (originalDifferentialClosure n I q)).map _ =
        formalDifferentialIdeal n (formalDifferentialClosure n (I.map _) q)
      rw [map_originalDifferentialIdeal,ih]

end
end Hironaka.HironakaActualOriginalDifferentialIdeals
