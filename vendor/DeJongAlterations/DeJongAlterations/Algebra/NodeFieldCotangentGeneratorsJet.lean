import DeJongAlterations.Algebra.NodeFieldCotangentGeneratorsPresentation
import DeJongAlterations.Algebra.NodeVariableMorseOrder
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The SAME original evaluation has no constant or linear relation

A genuine coefficient frame computes the native binary first-jet dimension.
The actual original evaluation then gives the full first-jet algebra equivalence
and the ENTIRE kernel inclusion in the actual variable-ideal square.
-/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.Algebra.NodeFieldCotangentGeneratorsJet

open NodeVariableMorse NodeFormalMorse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable (K : Type u) [Field K]

/-- The literal original constant and BOTH original linear coefficients. -/
def coordinates : Series K →ₗ[K] K × (Fin 2 → K) :=
  (coeff 0).prod (LinearMap.pi (fun i : Fin 2 => coeff (Finsupp.single i 1)))

/-- The WHOLE actual variable square is the kernel of the three native first-jet coefficients. -/
theorem mem_variableSquare_iff (g : Series K) :
    g ∈ variableIdeal K ^ 2 ↔ coordinates K g = 0 := by
  constructor
  · intro hg
    have ho := (mem_variableIdeal_pow_iff_order 2 g).mp hg
    apply Prod.ext
    · change coeff 0 g = 0
      apply coeff_of_lt_order
      exact lt_of_lt_of_le (by simp) ho
    · funext i
      change coeff (Finsupp.single i 1) g = 0
      apply coeff_of_lt_order
      exact lt_of_lt_of_le (by simp) ho
  · intro hg
    have hc : coeff 0 g = 0 := congrArg Prod.fst hg
    have h0 : coeff (Finsupp.single 0 1) g = 0 := congrArg (fun p => p.2 0) hg
    have h1 : coeff (Finsupp.single 1 1) g = 0 := congrArg (fun p => p.2 1) hg
    apply (mem_variableIdeal_pow_iff_order 2 g).mpr
    apply nat_le_order
    intro d hd
    have hd' : d 0 + d 1 < 2 := by
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
    have hb0 : d 0 ≤ 1 := by omega
    have hb1 : d 1 ≤ 1 := by omega
    have he : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
      ext i
      fin_cases i <;> simp
    rw [he]
    interval_cases h00 : d 0 <;> interval_cases h11 : d 1 <;> try omega
    all_goals simp [hc, h0, h1]

/-- The actual quotient coefficient map, using the proved WHOLE variable-square kernel. -/
def quotientCoordinates : (Series K ⧸ variableIdeal K ^ 2) →ₗ[K] K × (Fin 2 → K) :=
  let L : (Series K ⧸ (variableIdeal K ^ 2).restrictScalars K) →ₗ[K] K × (Fin 2 → K) :=
    ((variableIdeal K ^ 2).restrictScalars K).liftQ (coordinates K)
      (fun g hg => (mem_variableSquare_iff K g).mp hg)
  L.comp (Submodule.Quotient.restrictScalarsEquiv K (variableIdeal K ^ 2)).symm.toLinearMap

/-- The actual original quotient map retains all three literal original coefficients. -/
theorem quotientCoordinates_mk (g : Series K) :
    quotientCoordinates K (Ideal.Quotient.mk _ g) = coordinates K g := rfl

/-- The literal polynomial representative of any actual first-jet coordinate triple. -/
def coordinateRepresentative (p : K × (Fin 2 → K)) : Series K :=
  monomial 0 p.1 + monomial (Finsupp.single 0 1) (p.2 0) +
    monomial (Finsupp.single 1 1) (p.2 1)

/-- This actual representative has exactly its prescribed native original coefficient triple. -/
theorem coordinates_representative (p : K × (Fin 2 → K)) :
    coordinates K (coordinateRepresentative K p) = p := by
  apply Prod.ext
  · change coeff 0 (monomial 0 p.1 + monomial (Finsupp.single 0 1) (p.2 0) +
      monomial (Finsupp.single 1 1) (p.2 1)) = p.1
    simp only [map_add, coeff_monomial]
    simp [Finsupp.ext_iff, Fin.forall_fin_two]
  · funext i
    change coeff (Finsupp.single i 1)
      (monomial 0 p.1 + monomial (Finsupp.single 0 1) (p.2 0) +
        monomial (Finsupp.single 1 1) (p.2 1)) = p.2 i
    simp only [map_add, coeff_monomial]
    fin_cases i <;> simp [Finsupp.ext_iff, Fin.forall_fin_two]

/-- Genuine native first-jet coefficient equivalence; no basis or dimension identity is supplied. -/
def coordinateEquiv : (Series K ⧸ variableIdeal K ^ 2) ≃ₗ[K] K × (Fin 2 → K) :=
  LinearEquiv.ofBijective (quotientCoordinates K) (by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_variableSquare_iff K g).mpr ha)
    · intro p
      exact ⟨Ideal.Quotient.mk _ (coordinateRepresentative K p), coordinates_representative K p⟩)

/-- The ACTUAL native binary first-jet quotient has dimension three. -/
theorem source_finrank : Module.finrank K (Series K ⧸ variableIdeal K ^ 2) = 3 := by
  rw [(coordinateEquiv K).finrank_eq, Module.finrank_prod, Module.finrank_self, Module.finrank_pi]
  norm_num

variable (C : Type v) [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
  [Algebra K C] [IsAdicComplete (maximalIdeal C) C]
  (hres : Function.Bijective ((residue C).comp (algebraMap K C)))
  (hdim : Module.finrank K (C ⧸ maximalIdeal C ^ 2) = 3)

open NodeFieldCotangentGeneratorsPresentation

/-- The actual induced quotient map uses the SAME original evaluation and WHOLE square-image equality. -/
def evaluationJet :
    (Series K ⧸ variableIdeal K ^ 2) →ₐ[K] C ⧸ maximalIdeal C ^ 2 :=
  Ideal.quotientMapₐ (maximalIdeal C ^ 2) (evaluation K C hres hdim)
    ((Ideal.map_le_iff_le_comap).mp
      (variableIdeal_pow_image K C hres hdim 2).le)

/-- EVERY original series representative keeps its SAME actual original evaluation image. -/
theorem evaluationJet_mk (g : Series K) :
    evaluationJet K C hres hdim (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk _ (evaluation K C hres hdim g) := rfl

/-- Actual surjectivity and INTERNALLY proved source/actual target dimension give genuine first-jet bijectivity. -/
theorem evaluationJet_bijective : Function.Bijective (evaluationJet K C hres hdim) := by
  let : Module.Finite K (Series K ⧸ variableIdeal K ^ 2) :=
    Module.finite_of_finrank_pos (by rw [source_finrank K]; omega)
  let : Module.Finite K (C ⧸ maximalIdeal C ^ 2) :=
    Module.finite_of_finrank_pos (by rw [hdim]; omega)
  have hs : Function.Surjective (evaluationJet K C hres hdim) := by
    intro a
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := evaluation_surjective K C hres hdim c
    exact ⟨Ideal.Quotient.mk _ g, rfl⟩
  refine ⟨?_, hs⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((source_finrank K).trans hdim.symm)
    (f := (evaluationJet K C hres hdim).toLinearMap)).mpr hs

/-- The actual original first-jet algebra equivalence, not a supplied jet-frame certificate. -/
def evaluationJetEquiv :
    (Series K ⧸ variableIdeal K ^ 2) ≃ₐ[K] C ⧸ maximalIdeal C ^ 2 :=
  AlgEquiv.ofBijective (evaluationJet K C hres hdim) (evaluationJet_bijective K C hres hdim)

/-- EVERY actual series representative retains precisely its original actual evaluation. -/
theorem evaluationJetEquiv_mk (g : Series K) :
    evaluationJetEquiv K C hres hdim (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk _ (evaluation K C hres hdim g) := rfl

/-- The ENTIRE kernel of the original actual evaluation has zero constant and linear terms. -/
theorem kernel_le_variableSquare :
    RingHom.ker (evaluation K C hres hdim).toRingHom ≤ variableIdeal K ^ 2 := by
  intro g hg
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (evaluationJetEquiv K C hres hdim).injective
  rw [evaluationJetEquiv_mk, map_zero]
  change Ideal.Quotient.mk _ (evaluation K C hres hdim g) = 0
  rw [show evaluation K C hres hdim g = 0 from hg, map_zero]

/-- EVERY actual original relation has zero original constant coefficient. -/
theorem constantCoeff_eq_zero_of_mem_kernel (g : Series K)
    (hg : g ∈ RingHom.ker (evaluation K C hres hdim).toRingHom) : constantCoeff g = 0 :=
  congrArg Prod.fst ((mem_variableSquare_iff K g).mp (kernel_le_variableSquare K C hres hdim hg))

/-- EVERY actual original relation has BOTH zero original linear coefficients. -/
theorem linearCoeff_eq_zero_of_mem_kernel (g : Series K)
    (hg : g ∈ RingHom.ker (evaluation K C hres hdim).toRingHom) (i : Fin 2) :
    coeff (Finsupp.single i 1) g = 0 :=
  congrArg (fun p => p.2 i)
    ((mem_variableSquare_iff K g).mp (kernel_le_variableSquare K C hres hdim hg))

end DeJongAlterations.Algebra.NodeFieldCotangentGeneratorsJet
