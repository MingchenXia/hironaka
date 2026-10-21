/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHomogeneousInitialTangentDerivatives
import Hironaka.Resolution.HironakaActualCoefficientPresentationCentrePower
/-!
# Genuine tangent partial stability forces actual pure normal vertices

A real complex partial derivative of an actual monic minimal vertex witness
would lower any positive coordinate of its leading exponent. The coefficient
formula and translation-invariant SAME monomial order prove the derivative's
literal smaller leading exponent, contradicting whole-diagram minimality.
The actual homogeneous-initial diagram dictionary then gives pure normal
vertices from actual tangent initial stability. Original HS-constant regular
centre geometry supplies the stability and chart internally.

Blueprint: `hironaka-actual-pure-normal-vertices-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPureNormalVertices
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualFormalInitialDiagram HironakaActualHomogeneousInitialHS
  HironakaActualHomogeneousInitialTangentDerivatives HironakaActualCoefficientPresentationCentrePower
  HironakaActualOriginalFormalTaylor HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaHolomorphicJetRankLoci HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
variable {n : ℕ}

/-- Actual partial stability of a WHOLE formal ideal forbids that coordinate in every actual minimal vertex. -/
theorem vertex_coordinate_zero_of_pderiv_stable (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (i : Fin n)
    (hD : ∀ F∈I,MvPowerSeries.pderiv ℂ i F∈I) (a : actualInitialVertices m I) : a.val i=0 := by
  by_contra hzero
  have hai : 0<a.val i := Nat.pos_of_ne_zero hzero
  let b := a.val-Finsupp.single i 1
  have hle : Finsupp.single i 1≤a.val := Finsupp.single_le_iff.mpr hai
  have hba : b+Finsupp.single i 1=a.val := tsub_add_cancel_of_le hle
  obtain ⟨F,hFI,hFne,hinit,hmonic⟩ := exists_actual_monic_vertex_series m I a.val a.property
  have hc : MvPowerSeries.coeff b (MvPowerSeries.pderiv ℂ i F)≠0 := by
    rw [MvPowerSeries.coeff_pderiv,hba,hmonic,one_mul]
    exact_mod_cast Nat.succ_ne_zero (b i)
  have hDne : MvPowerSeries.pderiv ℂ i F≠0 := by
    intro hz
    exact hc (by rw [hz,map_zero])
  have hlow (c : Fin n →₀ ℕ) (hcb : m.toSyn c<m.toSyn b) :
      MvPowerSeries.coeff c (MvPowerSeries.pderiv ℂ i F)=0 := by
    rw [MvPowerSeries.coeff_pderiv]
    have hca : m.toSyn (c+Finsupp.single i 1)<m.toSyn a.val := by
      rw [← hba,map_add,map_add]
      simpa only [add_comm] using add_lt_add_right hcb (m.toSyn (Finsupp.single i 1))
    rw [coeff_eq_zero_of_lt_actualInitialExponent m F hFne _ (hinit.symm ▸ hca),zero_mul]
  have hinitD := actualInitialExponent_eq_of_coefficients m (MvPowerSeries.pderiv ℂ i F) hDne b hc hlow
  have hb : b∈actualInitialDiagram m I := ⟨_,hD F hFI,hDne,hinitD⟩
  have hm : Minimal (·∈actualInitialDiagram m I) a.val := by
    simpa only [actualInitialVertices,Set.Finite.mem_toFinset,mem_ofPred_eq] using a.property
  have hab : a.val≤b := hm.le_of_le hb tsub_le_self
  have hbi := hab i
  have hval : b i=a.val i-1 := by simp only [b,Finsupp.tsub_apply,Finsupp.single_eq_same]
  omega

/-- The genuine SAME degree-lex point vertices have no tangent block under whole initial tangent partial stability. -/
theorem tangentExponent_vertex_zero_of_initial_tangent_pderiv (d t : ℕ)
    (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ))
    (hD : ∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ), F∈actualHomogeneousInitialIdeal K →
      MvPowerSeries.pderiv ℂ (i.castAdd t) F∈actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t))) K) :
    actualTangentExponent (d := d) (t := t) a.val=0 := by
  have ha : a.val∈actualInitialVertices MonomialOrder.degLex (actualHomogeneousInitialIdeal K) := by
    simpa only [actualInitialVertices,actual_homogeneous_initial_ideal_diagram] using a.property
  ext i
  exact vertex_coordinate_zero_of_pderiv_stable MonomialOrder.degLex
    (actualHomogeneousInitialIdeal K) (i.castAdd t) (hD i) ⟨a.val,ha⟩

theorem vertex_eq_joined_normal_of_initial_tangent_pderiv (d t : ℕ)
    (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ))
    (hD : ∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ), F∈actualHomogeneousInitialIdeal K →
      MvPowerSeries.pderiv ℂ (i.castAdd t) F∈actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t))) K) :
    a.val=actualJoinedExponent (0 : Fin d →₀ ℕ) (actualNormalExponent a.val) := by
  have he := actualJoinedExponent_split (d := d) (t := t) a.val
  rw [tangentExponent_vertex_zero_of_initial_tangent_pderiv d t K hD a] at he
  exact he.symm

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original centre geometry ALONE internally supplies pure normal vertices in one genuine actual flattening. -/
theorem exists_original_hs_constant_centre_pure_normal_vertices
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y∈C,∀ ℓ : ℕ,hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y∈(chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y∈Φ.source →
        (y∈C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y)∈complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      ∀ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0),
        actualTangentExponent (d := d) (t := t) a.val=0 := by
  obtain ⟨Φ,hsrc,h0,hflat,_O,_hO,_hxO,_N,_G,_hG,_hgen,_U,_hU,_h0U,_hUT,
    _hMap,_hH,_hhol,_hI,hD,_hDP⟩ := exists_original_hs_constant_centre_initial_tangent_pderiv C x hreg A hA hhs
  exact ⟨Φ,hsrc,h0,hflat,fun a => tangentExponent_vertex_zero_of_initial_tangent_pderiv d t _ hD a⟩

end OriginalCentre
end
end Hironaka.HironakaActualPureNormalVertices
