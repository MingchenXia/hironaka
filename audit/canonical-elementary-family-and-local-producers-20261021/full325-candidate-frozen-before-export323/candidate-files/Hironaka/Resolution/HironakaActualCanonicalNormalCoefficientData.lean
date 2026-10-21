/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOriginalReducedVertexBasis
import Hironaka.Resolution.HironakaActualPureNormalVertices
import Hironaka.Resolution.HironakaActualAnalyticVertexCoefficientData
import Hironaka.Resolution.HironakaActualStandardNormalIndependence
import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers
/-!
# Exact canonical analytic coefficient data and genuine whole normal support

Every original ideal internally has one actual analytic coefficient datum
whose unchanged generator Taylor images are the WHOLE canonical reduced
vertex series. Genuine pure normal vertices and whole diagram upperness
force the entire relative coefficient series on diagram labels to be literal
constants zero or one. Actual original coefficient germs retain those exact
identities. Original HS-constant regular centre geometry fixes ONE actual
flattening before deriving all its pure vertices, canonical normal powers,
exact analytic datum and true whole generator normal powers.

All-label support is an identity of original germs, with no infinite common
function-domain or transformed HS persistence equivalence asserted.
Blueprint: `hironaka-actual-canonical-normal-coefficient-data-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCanonicalNormalCoefficientData
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualOriginalFormalTaylor HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualOriginalReducedVertexBasis
  HironakaActualPureNormalVertices HironakaActualAnalyticVertexCoefficientData
  HironakaActualCoefficientPresentationCentrePower HironakaActualCoefficientReducedStrictGenerators
  HironakaActualFormalCoordinatePowerDivision HironakaActualFiniteCoefficientIdeals
  HironakaActualAnalyticFormalNormalPowers HironakaActualHomogeneousInitialHS
  HironakaActualStandardNormalIndependence HironakaActualCoupledNormalFreeness
  HironakaRelativeNormalIdeal HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
variable {d t : ℕ}

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem exists_unshifted_reduced_basis (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) :
    ∃ G : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) → HolGerm (ComplexModel n),
      (∀ a,actualUnshiftedTaylorAlgHom n (G a)=actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a) ∧ Ideal.span (range G)=I := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ J : Ideal (HolGerm (ComplexModel m)),
      ∃ G : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map f.toRingHom J) →
          HolGerm (ComplexModel m),
        (∀ a,f (G a)=actualReducedVertexSeries MonomialOrder.degLex (Ideal.map f.toRingHom J) a) ∧
          Ideal.span (range G)=J
  have h : P (0+n) (originalTaylorAlgHom n) := fun J =>
    ⟨originalReducedVertexBasis J,originalReducedVertexBasis_taylor J,originalReducedVertexBasis_span J⟩
  exact unshiftedTaylor_property n P h I

/-- One true original coefficient datum for the EXACT canonical reduced family, with no incoming prepared family. -/
theorem exists_canonical_reduced_coefficient_data (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t)))) :
    ∃ P : ActualAnalyticVertexCoefficientData k s t I,
      ∀ a,actualUnshiftedTaylorAlgHom ((k+s)+t) (P.generator a)=actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I) a := by
  let n := (k+s)+t
  let J := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  obtain ⟨G,hTG,hspan⟩ := exists_unshifted_reduced_basis n I
  let q := ∑ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) J,
    actualCoefficientCentreVertexWeight k s t a.val
  have hle (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) J) :
      actualCoefficientCentreVertexWeight k s t a.val≤q :=
    Finset.single_le_sum
      (f := fun a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) J =>
        actualCoefficientCentreVertexWeight k s t a.val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  obtain ⟨U,hU,h0,c,hc,hd,hT,_⟩ := exists_actual_finite_local_coefficient_ideals (k+s) t q G
  have hd' (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) J) (γ : Fin t →₀ ℕ)
      (hγ : actualNormalDegree γ<actualCoefficientCentreVertexWeight k s t a.val) :=
    hd a γ (lt_of_lt_of_le hγ (hle a))
  refine ⟨{
    generator := G
    member := fun a => hspan ▸ Ideal.mem_span_range_self (x := a)
    nonzero := fun a => by rw [hTG]; exact actualReducedVertexSeries_ne_zero _ _ a
    initial := fun a => by
      apply actualInitialExponent_eq_of_coefficients
      · rw [hTG,actualReducedVertexSeries_coefficient]
        exact one_ne_zero
      · intro b hb
        rw [hTG]
        exact actualReducedVertexSeries_coefficient_lower _ _ a b hb
    monic := fun a => by rw [hTG];exact actualReducedVertexSeries_coefficient _ _ a
    generates := hspan
    domain := U
    isOpen_domain := hU
    zero_mem_domain := h0
    coefficient := c
    holomorphic := hc
    regular := fun a γ hγ => (hd' a γ hγ).1
    coherent := fun a γ hγ => (hd' a γ hγ).2.1
    coefficient_member := fun a γ hγ => (hd' a γ hγ).2.2
    coefficient_eq := hT },hTG⟩

private theorem joinedExponent_eq_iff (β β' : Fin d →₀ ℕ) (γ γ' : Fin t →₀ ℕ) :
    actualJoinedExponent β γ=actualJoinedExponent β' γ' ↔ β=β' ∧ γ=γ' := by
  constructor
  · intro h
    constructor
    · ext i
      simpa [actualJoinedExponent]
        using congrArg (fun a => a (i.castAdd t)) h
    · ext i
      simpa [actualJoinedExponent]
        using congrArg (fun a => a (i.natAdd d)) h
  · rintro ⟨rfl,rfl⟩
    rfl

/-- Entire relative coefficients on the WHOLE diagram are the true constants, for a pure normal reduced vertex. -/
theorem normalCoefficient_reduced_vertex_of_pure_normal
    (m : MonomialOrder (Fin (d+t))) (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ))
    (a : actualInitialVertices m K) (ha : actualTangentExponent (d := d) (t := t) a.val=0)
    (γ : Fin t →₀ ℕ) (hγ : actualJoinedExponent (0 : Fin d →₀ ℕ) γ∈actualInitialDiagram m K) :
    actualFormalNormalCoefficient (actualReducedVertexSeries m K a) γ=
      MvPowerSeries.C (if γ=actualNormalExponent a.val then (1 : ℂ) else 0) := by
  have he : a.val=actualJoinedExponent (0 : Fin d →₀ ℕ) (actualNormalExponent a.val) := by
    have h := actualJoinedExponent_split (d := d) (t := t) a.val
    rw [ha] at h
    exact h.symm
  apply MvPowerSeries.ext
  intro β
  have hβγ : actualJoinedExponent β γ∈actualInitialDiagram m K :=
    actualInitialDiagram_upper m K _ _ hγ (by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [actualJoinedExponent])
  change MvPowerSeries.coeff (actualJoinedExponent β γ) (actualReducedVertexSeries m K a)=_
  rw [actualReducedVertexSeries_coefficient_diagram m K a _ hβγ]
  have heq : actualJoinedExponent β γ=a.val ↔ β=0 ∧ γ=actualNormalExponent a.val := by
    constructor
    · intro h
      exact (joinedExponent_eq_iff β 0 γ _).mp (h.trans he)
    · intro h
      exact ((joinedExponent_eq_iff β 0 γ _).mpr h).trans he.symm
  simp only [heq,MvPowerSeries.coeff_C]
  by_cases hβ : β=0 <;> by_cases hγα : γ=actualNormalExponent a.val <;> simp [hβ,hγα]

/-- Actual initial tangent stability produces ONE canonical datum before every entire diagram coefficient-germ identity. -/
theorem exists_canonical_coefficient_data_with_diagram_support
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hD : ∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
      F∈actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
      MvPowerSeries.pderiv ℂ (i.castAdd t) F∈actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)) :
    ∃ P : ActualAnalyticVertexCoefficientData d 0 t I,
      (∀ a,actualUnshiftedTaylorAlgHom (d+t) (P.generator a)=actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a) ∧
      ∀ a γ,actualJoinedExponent (0 : Fin d →₀ ℕ) γ∈actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
        HolGerm.mk (P.coefficient a γ) (P.holomorphic a γ)=
          HolGerm.constHom (if γ=actualNormalExponent a.val then (1 : ℂ) else 0) := by
  obtain ⟨P,hP⟩ := exists_canonical_reduced_coefficient_data d 0 t I
  refine ⟨P,hP,?_⟩
  intro a γ hγ
  apply actualUnshiftedTaylorAlgHom_injective d
  have hc : actualFormalNormalCoefficient (actualUnshiftedTaylorAlgHom (d+t) (P.generator a)) γ=
      actualUnshiftedTaylorAlgHom d (HolGerm.mk (P.coefficient a γ) (P.holomorphic a γ)) := by
    simpa only [Nat.add_zero] using P.coefficient_eq a γ
  have hPG : actualUnshiftedTaylorAlgHom (d+t) (P.generator a)=actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a := by
    simpa only [Nat.add_zero] using hP a
  rw [← hc,hPG,normalCoefficient_reduced_vertex_of_pure_normal (d := d) (t := t) MonomialOrder.degLex
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a
    (tangentExponent_vertex_zero_of_initial_tangent_pderiv d t _ hD a) γ hγ]
  exact ((actualUnshiftedTaylorAlgHom d).commutes _).symm

section OriginalCentre
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original HSconstant geometry fixes ONE actual chart, exact canonical coefficient datum and whole normal powers. -/
theorem exists_original_hs_constant_centre_canonical_coefficient_data
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y∈C,∀ ℓ : ℕ,hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source⊆(chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y∈(chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y∈Φ.source →
        (y∈C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y)∈complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      let K0 := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0
      ∃ P : ActualAnalyticVertexCoefficientData d 0 t I0,
        (∀ a,actualUnshiftedTaylorAlgHom (d+t) (P.generator a)=actualReducedVertexSeries MonomialOrder.degLex K0 a) ∧
        (∀ a γ,actualJoinedExponent (0 : Fin d →₀ ℕ) γ∈actualInitialDiagram MonomialOrder.degLex K0 →
          HolGerm.mk (P.coefficient a γ) (P.holomorphic a γ)=
            HolGerm.constHom (if γ=actualNormalExponent a.val then (1 : ℂ) else 0)) ∧
        ∀ a,P.generator a∈normalIdeal d t ^
          Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  obtain ⟨Φ,hsrc,h0,hflat,hfree,hD,_hDP,_hExt⟩ :=
    exists_original_hs_constant_centre_coupled_normal_data C x hreg A hA hhs
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) 0)
  obtain ⟨P,hP,hcoeff⟩ := exists_canonical_coefficient_data_with_diagram_support I0 hD
  have hV := actual_reduced_vertices_mem_normal_powers_of_normal_free_and_initial_stable d t I0
    (fun q => (hfree q).2) hD
  refine ⟨Φ,hsrc,h0,hflat,P,hP,hcoeff,?_⟩
  intro a
  apply (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t _ (P.generator a)).mpr
  rw [hP]
  exact hV a

end OriginalCentre
end
end Hironaka.HironakaActualCanonicalNormalCoefficientData
