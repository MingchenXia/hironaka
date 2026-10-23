import DeJongAlterations.Algebra.NodeFieldUVJetBasis
import DeJongAlterations.Algebra.NodeFieldCotangentGeneratorsJet

/-! Native tangent coordinates and invertibility from an actual geometric cubic-jet surjection. -/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.Algebra.NodeFieldUVJetTangent

open NodeFormalMorse NodeVariableMorse NodeFieldUVJetKernel NodeFieldCotangentGeneratorsJet

universe u
variable (K : Type u) [Field K]

abbrev Jet := Series K ⧸ jetIdeal K 3

def tangentSeries : Series K →ₗ[K] (Fin 2 → K) :=
  LinearMap.pi (fun i => coeff (Finsupp.single i 1))

def tangentCoordinates : Jet K →ₗ[K] (Fin 2 → K) :=
  let L : (Series K ⧸ (jetIdeal K 3).restrictScalars K) →ₗ[K] (Fin 2 → K) :=
    ((jetIdeal K 3).restrictScalars K).liftQ (tangentSeries K) (by
      intro f hf
      funext i
      exact (mem_jetIdeal_iff 3 f).mp hf _ (by simp) (by fin_cases i <;> simp))
  L.comp (Submodule.Quotient.restrictScalarsEquiv K (jetIdeal K 3)).symm.toLinearMap

theorem tangentCoordinates_mk (f : Series K) :
    tangentCoordinates K (Ideal.Quotient.mk _ f) = tangentSeries K f := rfl

theorem tangentCoordinates_X (i : Fin 2) :
    tangentCoordinates K (Ideal.Quotient.mk _ (X i)) = Pi.single i 1 := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [tangentCoordinates_mk, tangentSeries, X, coeff_monomial,
      Finsupp.ext_iff, Fin.forall_fin_two]

theorem tangentCoordinates_one : tangentCoordinates K (1 : Jet K) = 0 := by
  change tangentSeries K 1 = 0
  funext i
  fin_cases i <;> simp [tangentSeries, coeff_one, Finsupp.ext_iff, Fin.forall_fin_two]

theorem tangentCoordinates_surjective : Function.Surjective (tangentCoordinates K) := by
  intro a
  refine ⟨Ideal.Quotient.mk _ (a 0 • X 0 + a 1 • X 1), ?_⟩
  change tangentSeries K (a 0 • X 0 + a 1 • X 1) = a
  funext i
  fin_cases i <;> simp [tangentSeries, X, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_two]

def coefficientMap : Jet K →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ (seriesConstantMap (K := K)) (by
    intro f hf
    exact (mem_jetIdeal_iff 3 f).mp hf 0 (by simp) (by simp))

theorem coefficientMap_surjective : Function.Surjective (coefficientMap K) := by
  intro a
  exact ⟨algebraMap K (Jet K) a, (coefficientMap K).commutes a⟩

instance jet_nontrivial : Nontrivial (Jet K) := (coefficientMap K).toRingHom.domain_nontrivial

instance jet_isLocalRing : IsLocalRing (Jet K) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem series_maximalIdeal : maximalIdeal (Series K) = variableIdeal K := by
  have hs : Function.Surjective (seriesConstantMap (K := K)) := by
    intro a
    exact ⟨C a, by simp [seriesConstantMap]⟩
  exact (ker_eq_maximalIdeal (seriesConstantMap (K := K)).toRingHom hs).symm.trans
    seriesConstantMap_kernel

theorem maximalPower_eq_map_variables (n : ℕ) :
    maximalIdeal (Jet K) ^ n = (variableIdeal K ^ n).map (Ideal.Quotient.mk _) := by
  rw [Ideal.map_pow, ← series_maximalIdeal K,
    map_maximalIdeal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective]

theorem tangentCoordinates_zero_of_mem_square {z : Jet K}
    (hz : z ∈ maximalIdeal (Jet K) ^ 2) : tangentCoordinates K z = 0 := by
  rw [maximalPower_eq_map_variables] at hz
  obtain ⟨f, hf, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective).mp hz
  exact congrArg Prod.snd ((mem_variableSquare_iff K f).mp hf)

variable (ψ : Series K →ₐ[K] Jet K) (hψ : Function.Surjective ψ)

include hψ in
theorem evaluation_tangent_coordinates (f : Series K) :
    tangentCoordinates K (ψ f) =
      coeff (Finsupp.single 0 1) f • tangentCoordinates K (ψ (X 0)) +
      coeff (Finsupp.single 1 1) f • tangentCoordinates K (ψ (X 1)) := by
  let r := coordinateRepresentative K (coordinates K f)
  have hr : f - r ∈ variableIdeal K ^ 2 := by
    apply (mem_variableSquare_iff K _).mpr
    rw [map_sub, coordinates_representative, sub_self]
  have him : ψ (f - r) ∈ maximalIdeal (Jet K) ^ 2 := by
    have hm : (variableIdeal K ^ 2).map ψ.toRingHom = maximalIdeal (Jet K) ^ 2 := by
      rw [Ideal.map_pow, ← series_maximalIdeal K,
        map_maximalIdeal_of_surjective ψ.toRingHom hψ]
    rw [← hm]
    exact Ideal.mem_map_of_mem _ hr
  have heq : tangentCoordinates K (ψ f) = tangentCoordinates K (ψ r) := by
    apply sub_eq_zero.mp
    simpa only [map_sub] using tangentCoordinates_zero_of_mem_square K him
  rw [heq]
  have hre : r = constantCoeff f • (1 : Series K) +
      coeff (Finsupp.single 0 1) f • X 0 + coeff (Finsupp.single 1 1) f • X 1 := by
    change monomial 0 (constantCoeff f) +
      monomial (Finsupp.single 0 1) (coeff (Finsupp.single 0 1) f) +
      monomial (Finsupp.single 1 1) (coeff (Finsupp.single 1 1) f) = _
    simp only [Algebra.smul_def, MvPowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_one]
    change _ = monomial 0 (constantCoeff f) +
      monomial 0 (coeff (Finsupp.single 0 1) f) * monomial (Finsupp.single 0 1) 1 +
      monomial 0 (coeff (Finsupp.single 1 1) f) * monomial (Finsupp.single 1 1) 1
    simp only [monomial_mul_monomial, zero_add, mul_one]
  rw [hre]
  simp only [map_add, map_smul, map_one, tangentCoordinates_one, smul_zero, zero_add]

def tangentMap : (Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun a := a 0 • tangentCoordinates K (ψ (X 0)) + a 1 • tangentCoordinates K (ψ (X 1))
  map_add' a b := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' a b := by
    simp only [Pi.smul_apply, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]

include hψ in
theorem tangentMap_surjective : Function.Surjective (tangentMap K ψ) := by
  intro a
  obtain ⟨z, hz⟩ := tangentCoordinates_surjective K a
  obtain ⟨f, hf⟩ := hψ z
  refine ⟨fun i => coeff (Finsupp.single i 1) f, ?_⟩
  change _ + _ = a
  rw [← evaluation_tangent_coordinates K ψ hψ, hf, hz]

include hψ in
theorem determinant_ne_zero :
    tangentCoordinates K (ψ (X 0)) 0 * tangentCoordinates K (ψ (X 1)) 1 -
      tangentCoordinates K (ψ (X 0)) 1 * tangentCoordinates K (ψ (X 1)) 0 ≠ 0 := by
  obtain ⟨a, ha⟩ := tangentMap_surjective K ψ hψ (Pi.single 0 1)
  obtain ⟨b, hb⟩ := tangentMap_surjective K ψ hψ (Pi.single 1 1)
  have ha0 := congrFun ha 0
  have ha1 := congrFun ha 1
  have hb0 := congrFun hb 0
  have hb1 := congrFun hb 1
  simp only [tangentMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)] at ha0 ha1 hb0 hb1
  intro hd
  have he :
      (tangentCoordinates K (ψ (X 0)) 0 * tangentCoordinates K (ψ (X 1)) 1 -
        tangentCoordinates K (ψ (X 0)) 1 * tangentCoordinates K (ψ (X 1)) 0) *
        (a 0 * b 1 - a 1 * b 0) = 1 := by
    calc
      _ = (a 0 * tangentCoordinates K (ψ (X 0)) 0 + a 1 * tangentCoordinates K (ψ (X 1)) 0) *
          (b 0 * tangentCoordinates K (ψ (X 0)) 1 + b 1 * tangentCoordinates K (ψ (X 1)) 1) -
        (b 0 * tangentCoordinates K (ψ (X 0)) 0 + b 1 * tangentCoordinates K (ψ (X 1)) 0) *
          (a 0 * tangentCoordinates K (ψ (X 0)) 1 + a 1 * tangentCoordinates K (ψ (X 1)) 1) := by ring
      _ = 1 := by rw [ha0, hb1, hb0, ha1]; ring
  rw [hd, zero_mul] at he
  exact zero_ne_one he

end DeJongAlterations.Algebra.NodeFieldUVJetTangent
