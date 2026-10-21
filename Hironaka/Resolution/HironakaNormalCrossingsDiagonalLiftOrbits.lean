/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsFirstStepChartHistory

/-! # Actual diagonal lifts and exceptional direction point identities

Actual universal-property uniqueness proves the lifted monomial-chart point
identity. No fixed whole canonical value image or later canonical driver is
asserted. Blueprint: `hironaka-normal-crossings-diagonal-lift-orbits-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsDiagonalLiftOrbits

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerIsomorphism BlowupFlatCoordinates BlowupMonomialCharts
  BlowupLocalSurjectivity MarkedIdealBiholomorphism
  HironakaNormalCrossingsInitialFullMaximum HironakaNormalCrossingsFirstStepChartHistory

noncomputable section
variable {n : ℕ}

/-- Coordinatewise actual linear scaling. -/
def diagonal (a : Fin n → ℂ) (w : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 fun i => a i * w i

@[simp] theorem diagonal_apply (a : Fin n → ℂ) (w : ComplexModel n) (i : Fin n) :
    diagonal a w i = a i * w i := rfl

theorem contDiff_diagonal (a : Fin n → ℂ) : ContDiff ℂ ∞ (diagonal a) := by
  exact (contDiff_piLp 2).mpr fun i =>
    contDiff_const.mul (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).contDiff

private theorem contMDiff_down :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun p : LiftedModel.{u} n => p.down) := by
  intro p
  change ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
    (extChartAt 𝓘(ℂ, ComplexModel n) p) p
  exact contMDiffAt_extChartAt

private def modelUp (p : ComplexModel n) : LiftedModel.{u} n := ULift.up p

private theorem contMDiff_up :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (modelUp.{u} : ComplexModel n → LiftedModel.{u} n) := by
  intro p
  rw [contMDiffAt_iff_target]
  refine ⟨continuous_uliftUp.continuousAt,?_⟩
  change ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
    (id : ComplexModel n → ComplexModel n) p
  exact contMDiffAt_id

/-- A genuine entire biholomorphism with the actual reciprocal inverse. -/
def diagonalEquiv (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0) :
    LiftedModel.{u} n ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ LiftedModel.{u} n where
  toFun w := ULift.up (diagonal a w.down)
  invFun w := ULift.up (diagonal (fun i => (a i)⁻¹) w.down)
  left_inv w := by
    apply ULift.ext
    ext i
    simp [diagonal,ha i]
  right_inv w := by
    apply ULift.ext
    ext i
    simp [diagonal,ha i]
  contMDiff_toFun := contMDiff_up.comp ((contDiff_diagonal a).contMDiff.comp contMDiff_down)
  contMDiff_invFun := contMDiff_up.comp
    ((contDiff_diagonal (fun i => (a i)⁻¹)).contMDiff.comp contMDiff_down)

/-- Whole coordinate centre with free coordinates below k. -/
def entireCentre (k : ℕ) : Set (LiftedModel.{u} n) :=
  {w | w.down ∈ complexCoordinatePlane n k}

theorem diagonal_preimage_centre (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0) (k : ℕ) :
    (diagonalEquiv.{u} a ha) ⁻¹' entireCentre k = entireCentre k := by
  ext w
  change (∀ i : Fin n, k ≤ i.val → a i * w.down i = 0) ↔
    (∀ i : Fin n, k ≤ i.val → w.down i = 0)
  simp only [mul_eq_zero,ha,false_or]

theorem diagonal_preimage_carrier (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0)
    (S : Finset (Fin n)) :
    (diagonalEquiv.{u} a ha) ⁻¹' coordinateCarrier S = coordinateCarrier S := by
  ext w
  change (∃ i ∈ S, a i * w.down i = 0) ↔ ∃ i ∈ S, w.down i = 0
  simp only [mul_eq_zero,ha,false_or]

/-- Actual affine-chart scaling, with pivot ratios on nonpivot normal coordinates. -/
def chartScale (a : Fin n → ℂ) (k : ℕ) (j : Fin n) : ComplexModel n → ComplexModel n :=
  diagonal (fun i => if k ≤ i.val ∧ i ≠ j then a i / a j else a i)

/-- Whole polynomial map equality, valid at every actual chart point. -/
theorem monomial_chartScale (a : Fin n → ℂ) {k : ℕ} {j : Fin n}
    (haj : a j ≠ 0) (w : ComplexModel n) :
    monomial k j (chartScale a k j w) = diagonal a (monomial k j w) := by
  ext i
  simp only [monomial_apply,chartScale,diagonal_apply]
  by_cases hi : k ≤ i.val ∧ i ≠ j
  · simp only [if_pos hi,if_neg (show ¬ (k ≤ j.val ∧ j ≠ j) by simp)]
    field_simp
  · simp only [if_neg hi]

private def modelZero : LiftedModel.{u} n := ULift.up (0 : ComplexModel n)

private def entireChart : LocalHolomorphicEquivAt (n := n)
    (chartAt (ComplexModel n) (modelZero : LiftedModel.{u} n) modelZero) where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := id
  invFun := id
  toFun_holomorphic := differentiable_id.differentiableOn
  invFun_holomorphic := differentiable_id.differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

private theorem entireChart_source :
    (entireChart.{u} (n := n)).source ⊆
      (chartAt (ComplexModel n) (modelZero : LiftedModel.{u} n)).target :=
  fun _ _ => mem_univ _

private theorem entireChart_flat (k : ℕ) {y : LiftedModel.{u} n}
    (_hy : y ∈ (chartAt (ComplexModel n) (modelZero : LiftedModel.{u} n)).source)
    (_hyΦ : chartAt (ComplexModel n) (modelZero : LiftedModel.{u} n) y ∈
      (entireChart.{u} (n := n)).source) :
    y ∈ entireCentre k ↔
      (entireChart.{u} (n := n)).toFun
        (chartAt (ComplexModel n) (modelZero : LiftedModel.{u} n) y) ∈
          complexCoordinatePlane n k := Iff.rfl

private abbrev entireDomain (k : ℕ) (j : Fin n) :=
  monomialDomain (M := LiftedModel.{u} n) (y₀ := modelZero) (entireChart.{u} (n := n)) k j

abbrev EntireTest (k : ℕ) (j : Fin n) := LiftedOpen.{u} (entireDomain.{u} k j)

def scaledTest (a : Fin n → ℂ) (k : ℕ) (j : Fin n) (w : EntireTest.{u} k j) :
    EntireTest.{u} k j :=
  LiftedOpen.mk _ (chartScale a k j (LiftedOpen.toModel _ w)) (mem_univ _)

private theorem contMDiff_scaledTest (a : Fin n → ℂ) (k : ℕ) (j : Fin n) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (scaledTest.{u} a k j) := by
  intro w
  apply LiftedOpen.contMDiffAt_of_toModel
  exact ((contDiff_diagonal _).contMDiff.comp (LiftedOpen.contMDiff_toModel _)) w

variable {D : CMfd.{u} n} {k : ℕ} {σ : D → LiftedModel.{u} n}

/-- The actual entire monomial lift chosen from the genuine unique lift theorem. -/
def entireLift (hσ : IsBlowupAlong n (entireCentre k) σ) (j : Fin n) (hj : k ≤ j.val) :
    EntireTest.{u} k j → D :=
  Classical.choose (existsUnique_monomialLift hσ entireChart_source.{u} (entireChart_flat.{u} k) hj)

theorem entireLift_spec (hσ : IsBlowupAlong n (entireCentre k) σ)
    (j : Fin n) (hj : k ≤ j.val) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (entireLift hσ j hj) ∧
      σ ∘ entireLift hσ j hj = monomialChart (M := LiftedModel.{u} n) (y₀ := modelZero) (entireChart.{u} (n := n)) k j :=
  (Classical.choose_spec (existsUnique_monomialLift hσ entireChart_source.{u} (entireChart_flat.{u} k) hj)).1

def entireTower (hσ : IsBlowupAlong n (entireCentre k) σ) :
    BlowupTower (CMfd.of (n := n) (LiftedModel.{u} n)) D := .step .refl _ σ hσ

/-- The ACTUAL diagonal history lift satisfies the ACTUAL entire chart point law. -/
theorem exists_diagonal_history_lift_chart (hσ : IsBlowupAlong n (entireCentre k) σ)
    (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0) :
    ∃ E : D ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ D,
      IsTowerIso (diagonalEquiv a ha) (entireTower hσ) (entireTower hσ) E ∧
      ∀ (j : Fin n) (hj : k ≤ j.val) (w : EntireTest.{u} k j),
        E (entireLift hσ j hj w) = entireLift hσ j hj (scaledTest a k j w) := by
  obtain ⟨E,hE⟩ := exists_oneStep_isTowerIso
    (A := CMfd.of (n := n) (LiftedModel.{u} n))
    (B := CMfd.of (n := n) (LiftedModel.{u} n))
    (diagonalEquiv a ha) hσ hσ (diagonal_preimage_centre a ha k)
  refine ⟨E,hE,?_⟩
  intro j hj w
  have hproj (z : D) : σ (E z) = diagonalEquiv a ha (σ z) :=
    (hE.proj_comm z).symm
  let γ := monomialChart (M := LiftedModel.{u} n) (y₀ := modelZero) (entireChart.{u} (n := n)) k j
  have hγ := contMDiff_monomialChart (M := LiftedModel.{u} n) (y₀ := modelZero)
    (Φ := entireChart.{u}) (k := k) (j := j) entireChart_source.{u}
  have hγinv := isInvertible_pullback_monomialChart entireChart_source.{u} (entireChart_flat.{u} k) hj
  have hpull := pullback_vanishingIdeal_preimage (diagonalEquiv a ha).contMDiff
    (diagonalEquiv a ha).symm.contMDiff (diagonalEquiv a ha).apply_symm_apply
    (diagonalEquiv a ha).symm_apply_apply hγ (entireCentre k)
  rw [diagonal_preimage_centre] at hpull
  have hginv : (GermIdeal.pullback (m := n) ((diagonalEquiv a ha) ∘ γ)
      (vanishingIdeal (n := n) (entireCentre k))).IsInvertible := by
    rw [← hpull]
    exact hγinv
  obtain ⟨_,_,huniq⟩ := hσ.2.2.2.2 n (EntireTest.{u} k j) ((diagonalEquiv a ha) ∘ γ)
    ((diagonalEquiv a ha).contMDiff.comp hγ) hginv
  have hfirst : σ ∘ (E ∘ entireLift hσ j hj) = (diagonalEquiv a ha) ∘ γ := by
    funext v
    change σ (E (entireLift hσ j hj v)) = diagonalEquiv a ha (γ v)
    rw [hproj]
    exact congrArg (diagonalEquiv a ha) (congrFun (entireLift_spec hσ j hj).2 v)
  have hsecond : σ ∘ (entireLift hσ j hj ∘ scaledTest a k j) = (diagonalEquiv a ha) ∘ γ := by
    funext v
    change (σ ∘ entireLift hσ j hj) (scaledTest a k j v) = _
    rw [(entireLift_spec hσ j hj).2]
    apply ULift.ext
    exact monomial_chartScale a (ha j) (LiftedOpen.toModel _ v)
  have heq := (huniq (E ∘ entireLift hσ j hj)
    ⟨E.contMDiff.comp (entireLift_spec hσ j hj).1,hfirst⟩).trans
      (huniq (entireLift hσ j hj ∘ scaledTest a k j)
        ⟨(entireLift_spec hσ j hj).1.comp (contMDiff_scaledTest a k j),hsecond⟩).symm
  exact congrFun heq w

/-- An actual entire monomial chart point with literal binary support. -/
def binaryPoint (k : ℕ) (j : Fin n) (S : Finset (Fin n)) : EntireTest.{u} k j :=
  LiftedOpen.mk _ (WithLp.toLp 2 fun i => if i ∈ S then (1 : ℂ) else 0) (mem_univ _)

/-- Actual diagonal histories normalize actual exceptional fibre points to
finite pivot/support data, using the whole lifted chart point identity. -/
theorem exists_binary_direction_history_lift (hσ : IsBlowupAlong n (entireCentre k) σ)
    (z : D) (hz : σ z = (ULift.up (0 : ComplexModel n) : LiftedModel.{u} n)) :
    ∃ (j : Fin n) (hj : k ≤ j.val) (S : Finset (Fin n)),
      (∀ i ∈ S, k ≤ i.val ∧ i ≠ j) ∧
      ∃ (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0),
        ∃ E : D ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ D,
          IsTowerIso (diagonalEquiv a ha) (entireTower hσ) (entireTower hσ) E ∧
          E z = entireLift hσ j hj (binaryPoint k j S) := by
  classical
  have hzflat : σ z ∈ flatDomain (entireChart.{u} (n := n)) := ⟨mem_univ _,mem_univ _⟩
  obtain ⟨j,hj,w,hw,_⟩ := exists_monomialLift_eq hσ
    entireChart_source.{u} (entireChart_flat.{u} k) hzflat
  have hwz := hw (entireLift hσ j hj) (entireLift_spec hσ j hj).1 (entireLift_spec hσ j hj).2
  let v := LiftedOpen.toModel _ w
  have hm0 : monomial k j v = 0 := by
    have hh := congrFun (entireLift_spec hσ j hj).2 w
    change σ (entireLift hσ j hj w) = _ at hh
    rw [hwz,hz] at hh
    have hh' := congrArg (fun p : LiftedModel.{u} n => p.down) hh
    change (0 : ComplexModel n) = monomial k j v at hh'
    exact hh'.symm
  have hzero (i : Fin n) (hi : ¬ (k ≤ i.val ∧ i ≠ j)) : v i = 0 := by
    have hh := congrArg (fun p : ComplexModel n => p i) hm0
    simpa [monomial_apply,hi] using hh
  let S := Finset.univ.filter (fun i : Fin n => k ≤ i.val ∧ i ≠ j ∧ v i ≠ 0)
  let a : Fin n → ℂ := fun i => if k ≤ i.val ∧ i ≠ j ∧ v i ≠ 0 then (v i)⁻¹ else 1
  have ha (i : Fin n) : a i ≠ 0 := by
    dsimp [a]
    split_ifs with hi
    · exact inv_ne_zero hi.2.2
    · exact one_ne_zero
  have hvector : chartScale a k j v =
      WithLp.toLp 2 (fun i => if i ∈ S then (1 : ℂ) else 0) := by
    ext i
    by_cases hi : k ≤ i.val ∧ i ≠ j
    · by_cases hv : v i = 0
      · simp [chartScale,diagonal,a,S,hi.1,hi.2,hv]
      · simp [chartScale,diagonal,a,S,hi.1,hi.2,hv]
    · have hv := hzero i hi
      simp [chartScale,diagonal,a,S,hv]
  have hscaled : scaledTest a k j w = binaryPoint k j S := by
    apply Subtype.ext
    apply ULift.ext
    exact hvector
  obtain ⟨E,hE,hpoint⟩ := exists_diagonal_history_lift_chart hσ a ha
  refine ⟨j,hj,S,?_,a,ha,E,hE,?_⟩
  · intro i hi
    have ht := (Finset.mem_filter.mp hi).2
    exact ⟨ht.1,ht.2.1⟩
  · rw [← hwz]
    exact (hpoint j hj w).trans (congrArg (entireLift hσ j hj) hscaled)

/-- Actual finite geometric orbit representatives, with genuine whole history
lifts. This makes no assertion about a finite WHOLE invariant value image. -/
theorem exists_finite_geometric_orbit_representatives
    (hσ : IsBlowupAlong n (entireCentre k) σ) :
    ∃ Q : Set D, Q.Finite ∧
      ∀ z : D, σ z = (ULift.up (0 : ComplexModel n) : LiftedModel.{u} n) →
        ∃ (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0),
          ∃ E : D ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ D,
            IsTowerIso (diagonalEquiv a ha) (entireTower hσ) (entireTower hσ) E ∧ E z ∈ Q := by
  classical
  let idx := {j : Fin n // k ≤ j.val} × Finset (Fin n)
  let point : idx → D := fun i => entireLift hσ i.1.val i.1.property (binaryPoint k i.1.val i.2)
  refine ⟨range point,Set.finite_range point,?_⟩
  intro z hz
  obtain ⟨j,hj,S,_,a,ha,E,hE,hpoint⟩ := exists_binary_direction_history_lift hσ z hz
  exact ⟨a,ha,E,hE,⟨(⟨j,hj⟩,S),hpoint.symm⟩⟩

end
end Hironaka.HironakaNormalCrossingsDiagonalLiftOrbits
