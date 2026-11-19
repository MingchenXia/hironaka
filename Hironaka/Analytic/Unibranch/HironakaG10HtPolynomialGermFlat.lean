import Hironaka.Resolution.HironakaActualTaylorCoordinateNaturality
import Hironaka.Resolution.HironakaActualPolynomialAnalyticFlatness
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.RingHom.Flat

/-!
# N5.c1 — convergent germs are flat over polynomials with convergent coefficients

Lane G10HT, run 0081, sub-item N5.c1 of `G10HT/hT-route-decision.md` (towards Hironaka 1975, p. 532: the analytic
stalk of a blowup chart is flat over the algebraic Rees chart).  For `H_d = HolGerm (ComplexModel d)`:

* `evPoly d r b : H_d[X_0, …, X_{r-1}] → H_{d+r}`, `C a ↦ a` (tangential pull-back), `X_i ↦ b_i + z_{d+i}`;
* **`evPoly_flat`** — `evPoly d r b` is flat, for every `d`, `r`, `b`.

Proof: one variable at a time (`evOne_flat`): `H_n[X] → H_{n+1} → ℂ⟦z_0,…,z_n⟧` (faithfully flat Taylor map,
`HironakaActualTaylorFaithfullyFlat`) equals `H_n[X] → ℂ⟦z⟧[X] → ℂ⟦z⟧⟦X⟧ ≅ ℂ⟦z_0,…,z_n⟧` (flat base change of the
flat Taylor map; flatness of the `X`-adic completion of a Noetherian ring, mathlib `AdicCompletion.flat_of_isNoetherian`
and `MvPowerSeries.toAdicCompletionAlgEquiv`), so `H_n[X] → H_{n+1}` is flat by faithfully flat descent
(`HironakaActualPolynomialAnalyticFlatness.flat_of_faithfully_flat_target`); then induction on `r`.  This generalizes
the library's `originalPolynomialEval_flat` (`d = 0`).

No named input.
-/

set_option autoImplicit false

universe u

namespace Hironaka.Analytic.Unibranch.HironakaG10HtPolynomialGermFlat

open Hironaka Hironaka
  HironakaActualTaylorCoordinateNaturality HironakaRelativeNormalIdeal
  HironakaActualCoefficientPresentationCentrePower HironakaActualTaylorFaithfullyFlat
  HironakaActualPolynomialAnalyticFlatness HironakaHolomorphicJetMonomialSpan
  HironakaActualOriginalFormalTaylor HironakaActualFormalCoordinatePowerDivision

noncomputable section

/-! ### The Taylor map -/

/-- The unshifted Taylor map is faithfully flat. -/
theorem unshiftedTaylor_faithfullyFlat (n : ℕ) :
    (actualUnshiftedTaylorAlgHom n).toRingHom.FaithfullyFlat := by
  have hc : ∀ {m : ℕ} (hm : m = n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ),
      f.toRingHom.FaithfullyFlat →
      (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm)
        f).toRingHom.FaithfullyFlat := by
    intro m hm f hf
    subst hm
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) (originalTaylorAlgHom_faithfullyFlat n)

theorem unshiftedTaylor_flat (n : ℕ) : (actualUnshiftedTaylorAlgHom n).toRingHom.Flat :=
  (unshiftedTaylor_faithfullyFlat n).flat

theorem unshiftedTaylor_const (n : ℕ) (c : ℂ) :
    actualUnshiftedTaylorAlgHom n (HolGerm.constHom c) = MvPowerSeries.C c :=
  (actualUnshiftedTaylorAlgHom n).commutes c

/-! ### Algebraic flatness lemmas -/

/-- Flat base change to polynomial rings. -/
theorem mvPolynomial_map_flat {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Flat)
    (σ : Type u) : (MvPolynomial.map f : MvPolynomial σ A →+* MvPolynomial σ B).Flat := by
  let := f.toAlgebra
  let : Algebra (MvPolynomial σ A) (MvPolynomial σ B) := MvPolynomial.algebraMvPolynomial
  exact RingHom.Flat.isStableUnderBaseChange A B (MvPolynomial σ A) (MvPolynomial σ B) hf

/-- Power series are flat over polynomials (Noetherian coefficients, finitely many variables). -/
theorem coe_mvPowerSeries_flat (σ Q : Type*) [Finite σ] [CommRing Q] [IsNoetherianRing Q] :
    (algebraMap (MvPolynomial σ Q) (MvPowerSeries σ Q)).Flat := by
  rw [RingHom.flat_algebraMap_iff]
  have : Module.Flat (MvPolynomial σ Q)
      (AdicCompletion (MvPolynomial.idealOfVars σ Q) (MvPolynomial σ Q)) := inferInstance
  exact Module.Flat.of_linearEquiv (MvPowerSeries.toAdicCompletionAlgEquiv σ Q).toLinearEquiv

/-- The translation `X ↦ X + C a` of a one-variable polynomial ring. -/
def shiftHom (Q : Type*) [CommRing Q] (a : Q) : MvPolynomial Unit Q →+* MvPolynomial Unit Q :=
  (MvPolynomial.aeval fun _ : Unit => MvPolynomial.X () + MvPolynomial.C a).toRingHom

theorem shiftHom_C (Q : Type*) [CommRing Q] (a q : Q) :
    shiftHom Q a (MvPolynomial.C q) = MvPolynomial.C q := by
  simp [shiftHom]

theorem shiftHom_X (Q : Type*) [CommRing Q] (a : Q) (u : Unit) :
    shiftHom Q a (MvPolynomial.X u) = MvPolynomial.X () + MvPolynomial.C a := by
  simp [shiftHom]

theorem shiftHom_comp_neg (Q : Type*) [CommRing Q] (a : Q) :
    (shiftHom Q (-a)).comp (shiftHom Q a) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro q
    simp [shiftHom_C]
  · intro u
    simp [shiftHom_X, shiftHom_C]

theorem shiftHom_bijective (Q : Type*) [CommRing Q] (a : Q) : Function.Bijective (shiftHom Q a) := by
  have h1 := shiftHom_comp_neg Q a
  have h2 := shiftHom_comp_neg Q (-a)
  rw [neg_neg] at h2
  refine ⟨fun x y hxy => ?_, fun y => ⟨shiftHom Q (-a) y, ?_⟩⟩
  · have := congrArg (shiftHom Q (-a)) hxy
    simpa only [← RingHom.comp_apply, h1, RingHom.id_apply] using this
  · simp only [← RingHom.comp_apply, h2, RingHom.id_apply]

/-! ### One new variable -/

/-- `H_n[X] → H_{n+1}`: coefficients are pulled back tangentially, `X ↦ c + z_n` (the last coordinate). -/
def evOne (n : ℕ) (c : ℂ) :
    MvPolynomial Unit (HolGerm (ComplexModel n)) →+* HolGerm (ComplexModel (n + 1)) :=
  MvPolynomial.eval₂Hom (tangentPullback n 1).toRingHom
    fun _ => HolGerm.constHom c + coordinateGerm (Fin.last n)

/-- The formal model of `evOne`. -/
def formalOne (n : ℕ) (c : ℂ) :
    MvPolynomial Unit (HolGerm (ComplexModel n)) →+* MvPowerSeries (Fin (n + 1)) ℂ :=
  (MvPowerSeries.renameEquiv ℂ (finRotate (n + 1)).symm).toRingHom.comp
    ((MvPowerSeries.finSuccEquiv ℂ n).symm.toRingHom.comp
      ((algebraMap (MvPolynomial Unit (MvPowerSeries (Fin n) ℂ))
          (MvPowerSeries Unit (MvPowerSeries (Fin n) ℂ))).comp
        ((shiftHom (MvPowerSeries (Fin n) ℂ) (MvPowerSeries.C c)).comp
          (MvPolynomial.map (actualUnshiftedTaylorAlgHom n).toRingHom))))

theorem formalOne_flat (n : ℕ) (c : ℂ) : (formalOne n c).Flat := by
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (AlgEquiv.bijective _))
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (AlgEquiv.bijective _))
  refine RingHom.Flat.comp ?_ (coe_mvPowerSeries_flat Unit (MvPowerSeries (Fin n) ℂ))
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (shiftHom_bijective _ _))
  exact mvPolynomial_map_flat _ (unshiftedTaylor_flat n) Unit

theorem finRotate_symm_zero (n : ℕ) : (finRotate (n + 1)).symm 0 = Fin.last n := by
  rw [Equiv.symm_apply_eq, finRotate_last]

theorem finRotate_symm_succ (n : ℕ) (i : Fin n) : (finRotate (n + 1)).symm i.succ = i.castSucc := by
  rw [Equiv.symm_apply_eq]
  ext
  rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]
  simp

theorem algebraMap_C {Q : Type*} [CommRing Q] (q : Q) :
    algebraMap (MvPolynomial Unit Q) (MvPowerSeries Unit Q) (MvPolynomial.C q) = PowerSeries.C q := by
  rw [MvPowerSeries.algebraMap_apply', Algebra.algebraMap_self, MvPowerSeries.map_id, RingHom.id_apply,
    MvPolynomial.coe_C]
  rfl

theorem algebraMap_X {Q : Type*} [CommRing Q] (u : Unit) :
    algebraMap (MvPolynomial Unit Q) (MvPowerSeries Unit Q) (MvPolynomial.X u) = PowerSeries.X := by
  rw [MvPowerSeries.algebraMap_apply', Algebra.algebraMap_self, MvPowerSeries.map_id, RingHom.id_apply,
    MvPolynomial.coe_X]
  rfl

theorem finSucc_symm_C_C (n : ℕ) (z : ℂ) :
    (MvPowerSeries.finSuccEquiv ℂ n).symm (PowerSeries.C (MvPowerSeries.C z)) = MvPowerSeries.C z := by
  rw [AlgEquiv.symm_apply_eq, MvPowerSeries.finSuccEquiv_C]

theorem finSucc_symm_C_X (n : ℕ) (i : Fin n) :
    (MvPowerSeries.finSuccEquiv ℂ n).symm (PowerSeries.C (MvPowerSeries.X i)) = MvPowerSeries.X i.succ := by
  rw [AlgEquiv.symm_apply_eq, MvPowerSeries.finSuccEquiv_X_succ]

theorem finSucc_symm_X (n : ℕ) :
    (MvPowerSeries.finSuccEquiv ℂ n).symm PowerSeries.X = MvPowerSeries.X 0 := by
  rw [AlgEquiv.symm_apply_eq, MvPowerSeries.finSuccEquiv_X_zero]

theorem formalOne_apply (n : ℕ) (c : ℂ) (p : MvPolynomial Unit (HolGerm (ComplexModel n))) :
    formalOne n c p = MvPowerSeries.rename (finRotate (n + 1)).symm
      ((MvPowerSeries.finSuccEquiv ℂ n).symm
        (algebraMap (MvPolynomial Unit (MvPowerSeries (Fin n) ℂ)) (MvPowerSeries Unit (MvPowerSeries (Fin n) ℂ))
          (shiftHom (MvPowerSeries (Fin n) ℂ) (MvPowerSeries.C c)
            (MvPolynomial.map (actualUnshiftedTaylorAlgHom n).toRingHom p)))) :=
  rfl

theorem formalOne_C_const (n : ℕ) (c z : ℂ) :
    formalOne n c (MvPolynomial.C (HolGerm.constHom z)) = MvPowerSeries.C z := by
  rw [formalOne_apply, MvPolynomial.map_C, shiftHom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    unshiftedTaylor_const, algebraMap_C, finSucc_symm_C_C, MvPowerSeries.rename_C]

theorem formalOne_C_coordinateGerm (n : ℕ) (c : ℂ) (i : Fin n) :
    formalOne n c (MvPolynomial.C (coordinateGerm i)) = MvPowerSeries.X i.castSucc := by
  rw [formalOne_apply, MvPolynomial.map_C, shiftHom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    actualUnshiftedTaylor_coordinate, algebraMap_C, finSucc_symm_C_X, MvPowerSeries.rename_X,
    finRotate_symm_succ]

theorem formalOne_X (n : ℕ) (c : ℂ) (u : Unit) :
    formalOne n c (MvPolynomial.X u) = MvPowerSeries.X (Fin.last n) + MvPowerSeries.C c := by
  rw [formalOne_apply, MvPolynomial.map_X, shiftHom_X, map_add, algebraMap_X, algebraMap_C, map_add,
    finSucc_symm_X, finSucc_symm_C_C, map_add, MvPowerSeries.rename_X, MvPowerSeries.rename_C,
    finRotate_symm_zero]

theorem formalOne_C (n : ℕ) (c : ℂ) (a : HolGerm (ComplexModel n)) :
    formalOne n c (MvPolynomial.C a) =
      actualUnshiftedTaylorAlgHom (n + 1) (tangentPullback n 1 a) := by
  -- both sides are `ℂ`-algebra maps of `a`, determined on coordinates
  let F : HolGerm (ComplexModel n) →ₐ[ℂ] MvPowerSeries (Fin (n + 1)) ℂ :=
    { toRingHom := (formalOne n c).comp MvPolynomial.C
      commutes' := fun z => formalOne_C_const n c z }
  have hF : F = (actualUnshiftedTaylorAlgHom (n + 1)).comp (tangentPullback n 1) := by
    apply actualGermAlgHom_eq_of_coordinate_images
    · intro i
      change formalOne n c (MvPolynomial.C (coordinateGerm i)) =
        actualUnshiftedTaylorAlgHom (n + 1) (tangentPullback n 1 (coordinateGerm i))
      rw [tangentPullback_coordinateGerm, actualUnshiftedTaylor_coordinate, formalOne_C_coordinateGerm]
      rfl
    · intro i
      change formalOne n c (MvPolynomial.C (coordinateGerm i)) ∈ _
      rw [formalOne_C_coordinateGerm]
      exact Ideal.subset_span ⟨i.castSucc, Set.mem_univ _, rfl⟩
  exact congrArg (fun φ : HolGerm (ComplexModel n) →ₐ[ℂ] MvPowerSeries (Fin (n + 1)) ℂ => φ a) hF

theorem formalOne_eq (n : ℕ) (c : ℂ) :
    formalOne n c = (actualUnshiftedTaylorAlgHom (n + 1)).toRingHom.comp (evOne n c) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [formalOne_C]
    simp [evOne]
  · intro u
    rw [formalOne_X, RingHom.comp_apply, evOne, MvPolynomial.eval₂Hom_X', AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, map_add, unshiftedTaylor_const, actualUnshiftedTaylor_coordinate]
    exact add_comm _ _

/-- **One new variable**: `H_n[X] → H_{n+1}`, `X ↦ c + z_n`, is flat. -/
theorem evOne_flat (n : ℕ) (c : ℂ) : (evOne n c).Flat := by
  let P := MvPolynomial Unit (HolGerm (ComplexModel n))
  let R := HolGerm (ComplexModel (n + 1))
  let S := MvPowerSeries (Fin (n + 1)) ℂ
  let : Algebra P R := (evOne n c).toAlgebra
  let : Algebra R S := (actualUnshiftedTaylorAlgHom (n + 1)).toRingHom.toAlgebra
  let : Algebra P S := (formalOne n c).toAlgebra
  have : IsScalarTower P R S := IsScalarTower.of_algebraMap_eq fun p => by
    change formalOne n c p = actualUnshiftedTaylorAlgHom (n + 1) (evOne n c p)
    rw [formalOne_eq]
    rfl
  have : Module.Flat P S := formalOne_flat n c
  have : Module.FaithfullyFlat R S := unshiftedTaylor_faithfullyFlat (n + 1)
  change Module.Flat P R
  exact flat_of_faithfully_flat_target P R S

/-! ### Several new variables -/

/-- `H_d[X_0, …, X_{r-1}] → H_{d+r}`: coefficients are pulled back tangentially, `X_i ↦ b_i + z_{d+i}`. -/
def evPoly (d r : ℕ) (b : Fin r → ℂ) :
    MvPolynomial (Fin r) (HolGerm (ComplexModel d)) →+* HolGerm (ComplexModel (d + r)) :=
  MvPolynomial.eval₂Hom (tangentPullback d r).toRingHom
    fun i => HolGerm.constHom (b i) + coordinateGerm (Fin.natAdd d i)

theorem evPoly_C (d r : ℕ) (b : Fin r → ℂ) (a : HolGerm (ComplexModel d)) :
    evPoly d r b (MvPolynomial.C a) = tangentPullback d r a :=
  MvPolynomial.eval₂Hom_C _ _ _

theorem evPoly_X (d r : ℕ) (b : Fin r → ℂ) (i : Fin r) :
    evPoly d r b (MvPolynomial.X i) = HolGerm.constHom (b i) + coordinateGerm (Fin.natAdd d i) :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- Tangential pull-backs compose. -/
theorem tangentPullback_tangentPullback (d r : ℕ) (a : HolGerm (ComplexModel d)) :
    tangentPullback (d + r) 1 (tangentPullback d r a) = tangentPullback d (r + 1) a := by
  induction a using HolGerm.induction_on with
  | h F hF => rfl

/-- Splitting off the last variable: `A[X_0, …, X_{r+1}] ≅ (A[X_0, …, X_r])[X]`. -/
def splitLast (A : Type) [CommRing A] (r : ℕ) :
    MvPolynomial (Fin (r + 1 + 1)) A →+* MvPolynomial Unit (MvPolynomial (Fin (r + 1)) A) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (Fin.lastCases (MvPolynomial.X ()) fun i => MvPolynomial.C (MvPolynomial.X i))

/-- Its inverse. -/
def joinLast (A : Type) [CommRing A] (r : ℕ) :
    MvPolynomial Unit (MvPolynomial (Fin (r + 1)) A) →+* MvPolynomial (Fin (r + 1 + 1)) A :=
  MvPolynomial.eval₂Hom (MvPolynomial.rename Fin.castSucc).toRingHom
    fun _ => MvPolynomial.X (Fin.last (r + 1))

theorem joinLast_comp_splitLast (A : Type) [CommRing A] (r : ℕ) :
    (joinLast A r).comp (splitLast A r) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [joinLast, splitLast]
  · intro i
    induction i using Fin.lastCases with
    | last => simp [joinLast, splitLast]
    | cast j => simp [joinLast, splitLast]

theorem splitLast_comp_rename (A : Type) [CommRing A] (r : ℕ) :
    (splitLast A r).comp (MvPolynomial.rename Fin.castSucc).toRingHom = MvPolynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [splitLast]
  · intro i
    simp [splitLast]

theorem splitLast_comp_joinLast (A : Type) [CommRing A] (r : ℕ) :
    (splitLast A r).comp (joinLast A r) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro p
    have := RingHom.congr_fun (splitLast_comp_rename A r) p
    simpa [joinLast] using this
  · intro u
    simp [joinLast, splitLast]

theorem splitLast_bijective (A : Type) [CommRing A] (r : ℕ) : Function.Bijective (splitLast A r) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨joinLast A r y, ?_⟩⟩
  · have := congrArg (joinLast A r) hxy
    simpa only [← RingHom.comp_apply, joinLast_comp_splitLast, RingHom.id_apply] using this
  · simp only [← RingHom.comp_apply, splitLast_comp_joinLast, RingHom.id_apply]

theorem evPoly_one (d : ℕ) (b : Fin 1 → ℂ) :
    evPoly d 1 b = (evOne d (b 0)).comp
      (MvPolynomial.renameEquiv (HolGerm (ComplexModel d)) (Equiv.equivPUnit (Fin 1))).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [evPoly_C, evOne]
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [evPoly_X, RingHom.comp_apply]
    change _ = evOne d (b 0) (MvPolynomial.rename (Equiv.equivPUnit (Fin 1)) (MvPolynomial.X 0))
    rw [MvPolynomial.rename_X, evOne, MvPolynomial.eval₂Hom_X']
    congr 2

theorem evPoly_succ (d r : ℕ) (b : Fin (r + 1 + 1) → ℂ) :
    evPoly d (r + 1 + 1) b = (evOne (d + (r + 1)) (b (Fin.last (r + 1)))).comp
      ((MvPolynomial.map (evPoly d (r + 1) fun i => b i.castSucc)).comp
        (splitLast (HolGerm (ComplexModel d)) r)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [evPoly_C, RingHom.comp_apply, splitLast, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C,
      evOne]
    exact (tangentPullback_tangentPullback d (r + 1) a).symm
  · intro i
    induction i using Fin.lastCases with
    | last =>
      simp only [evPoly_X, RingHom.comp_apply, splitLast, MvPolynomial.eval₂Hom_X', Fin.lastCases_last,
        MvPolynomial.map_X, evOne]
      rfl
    | cast j =>
      simp only [evPoly_X, RingHom.comp_apply, splitLast, MvPolynomial.eval₂Hom_X', Fin.lastCases_castSucc,
        MvPolynomial.map_C, evOne, MvPolynomial.eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_add, tangentPullback_coordinateGerm]
      congr 1

theorem evPoly_flat_succ (d r : ℕ) (b : Fin (r + 1 + 1) → ℂ)
    (ih : ∀ b' : Fin (r + 1) → ℂ, (evPoly d (r + 1) b').Flat) : (evPoly d (r + 1 + 1) b).Flat := by
  have h1 : (splitLast (HolGerm (ComplexModel d)) r).Flat :=
    RingHom.Flat.of_bijective (splitLast_bijective _ r)
  have h2 := mvPolynomial_map_flat (σ := Unit) (evPoly d (r + 1) fun i => b i.castSucc)
    (ih fun i => b i.castSucc)
  -- the codomain is ascribed in the form `d + (r + 1 + 1)` of `evPoly` (definitionally `d + (r + 1) + 1`)
  have h3 : (evOne (d + (r + 1)) (b (Fin.last (r + 1))) :
      MvPolynomial Unit (HolGerm (ComplexModel (d + (r + 1)))) →+*
        HolGerm (ComplexModel (d + (r + 1 + 1)))).Flat :=
    evOne_flat (d + (r + 1)) (b (Fin.last (r + 1)))
  have key := RingHom.Flat.comp (RingHom.Flat.comp h1 h2) h3
  rw [evPoly_succ]
  exact key

/-- **N5.c1.**  `H_d[X_0, …, X_{r-1}] → H_{d+r}`, `X_i ↦ b_i + z_{d+i}`, is flat (`r ≥ 1`). -/
theorem evPoly_flat (d r : ℕ) (b : Fin (r + 1) → ℂ) : (evPoly d (r + 1) b).Flat := by
  induction r with
  | zero =>
    rw [evPoly_one]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (AlgEquiv.bijective _)) (evOne_flat d (b 0))
  | succ r ih => exact evPoly_flat_succ d r b ih

end

end Hironaka.Analytic.Unibranch.HironakaG10HtPolynomialGermFlat
