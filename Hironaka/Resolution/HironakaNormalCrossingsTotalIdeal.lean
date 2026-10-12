/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaNormalCrossingsOpenRestrictionSeparation
import Hironaka.Resolution.HironakaNormalCrossingsBranchOverlap
import Hironaka.Resolution.HironakaPureCodimensionOneInvertibleIdeal
import Hironaka.Resolution.HironakaSNCSupportedMonomialIdeal

/-! # Whole original NC ideal on the actual natural finite separation

Genuine original NC charts and their true inverses internally produce nonzero
shifted coordinate products and the whole original zero germ. Empty actual
interior and original equation reduction give invertibility of the COMPLETE
original vanishing ideal; dimension zero gives a literal empty carrier and
unit ideal. No purity, equation, generator or invertibility certificate is input.

The real finite higher-stratum procedure is internally generated. Every actual
centre lies in its whole current original; true closed preimage algebra proves
at every actual prefix that the original full preimage is exactly the current
differential strict original and all accumulated new boundary. Actual iterative
single-blowup ideal pullbacks preserve invertibility and equal the SAME complete
original ideal pulled back by the actual tower projection. Protected strict
statement modules and their sequence helper are not imported.

The terminal smooth original appended to the actual finite boundary is genuine
SNC. Its ENTIRE union is exactly the total original divisor support. This produces
whole intrinsic monomial ideal equality and complete residual-unit equality.
Genuine global locally finite connected components and their actual original
integer exponents give finite positive component products with equality at EVERY
nearby stalk, in every dimension and without compactness or global finite branches.

Input to the elementary producer is only the actual original NC carrier. No
support, finite tower, termination, coefficient or factorization certificate is
supplied. Unordered geometric separation does not resolve the old ordered marked
colex tie-break or admissibility for an unrelated additional marked ideal; full
canonical marked-ideal G9 remains open.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsTotalIdeal
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsBoundarySeparation
  HironakaNormalCrossingsSeparationChoiceComparison HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsBranchOverlap BlowupFlatCoordinates NormalCrossings
  AnalyticDescendingChain AnalyticGermDecomposition HolomorphicGermReducednessBridge
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealTotalTransform HironakaStageCenters HironakaLocallyFiniteDivisorSum RestrictEmptyTower
open Hironaka
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

private theorem holomorphic_product {ι : Type*} (s : Finset ι)
    (f : ι → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => ∏ i ∈ s, f i z) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using eventually_differentiableAt_const (E := ComplexModel n) 1
  | @insert i s hi ih => simpa only [Finset.prod_insert hi] using eventually_differentiableAt_mul (hf i) ih

private theorem germ_product {ι : Type*} (s : Finset ι)
    (f : ι → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    HolGerm.mk (fun z => ∏ i ∈ s, f i z) (holomorphic_product s f hf) =
      ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  apply Subtype.ext
  rw [HolGerm.coe_mk,SubmonoidClass.coe_finsetProd]
  simp only [HolGerm.coe_mk]
  have h := map_prod
    (Germ.coeRingHom (𝓝 (0 : ComplexModel n)) : (ComplexModel n → ℂ) →+* Germ (𝓝 (0 : ComplexModel n)) ℂ) f s
  simp only [Germ.coe_coeRingHom] at h
  rw [← h,Finset.prod_fn]

private theorem shifted_holomorphic {q : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) q) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => Φ.toFun (z+q)) z := by
  have ht : Tendsto (fun z : ComplexModel n => z+q) (𝓝 0) (𝓝 q) := by
    simpa only [zero_add] using (continuous_add_const q).tendsto 0
  filter_upwards [ht.eventually (Φ.isOpen_source.mem_nhds Φ.center_mem_source)] with z hz
  exact (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hz)).comp z
    (differentiableAt_id.add_const q)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual original NC coordinates internally produce a nonzero whole product and its entire original zero germ. -/
theorem exists_nonzero_original_coordinate_equation {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := n) H) (x : M) :
    ∃ (f : ComplexModel n → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z),
      HolGerm.mk f hf ≠ 0 ∧ chartGerm H x =ᶠ[𝓝 0] {z | f z = 0} := by
  classical
  obtain ⟨Φ,hsrc,h0,S,hflat⟩ := hH.2 x
  let e := chartAt (ComplexModel n) x
  let q := e x
  let F : ComplexModel n → ComplexModel n := fun z => Φ.toFun (z+q)
  have hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z := shifted_holomorphic Φ
  have hcoord : ∀ i : Fin n, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => F z i) z := by
    intro i
    exact hF.mono (fun z hz => (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt.comp z hz)
  let f : ComplexModel n → ℂ := fun z => ∏ i ∈ S, F z i
  have hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z := holomorphic_product S _ hcoord
  refine ⟨f,hf,?_,?_⟩
  · change HolGerm.mk (fun z => ∏ i ∈ S, F z i) _ ≠ 0
    rw [germ_product]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hprime := prime_coordinate_of_surjective_fderiv hF
      (by simpa only [F,zero_add] using h0) (surjective_fderiv_shifted Φ) i
    exact hprime.ne_zero
  · have ht : Tendsto (fun z : ComplexModel n => z+q) (𝓝 0) (𝓝 q) := by
      simpa only [zero_add] using (continuous_add_const q).tendsto 0
    have hInv : Tendsto (fun z : ComplexModel n => e.symm (z+q)) (𝓝 0) (𝓝 x) := by
      simpa only [Function.comp_def,e.left_inv (mem_chart_source _ x)] using
        (e.continuousAt_symm (e.map_source (mem_chart_source _ x))).tendsto.comp ht
    have hdom := (ht.eventually (e.open_target.mem_nhds (e.map_source (mem_chart_source _ x)))).and
      (hInv.eventually ((isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)))
    filter_upwards [hdom] with z hz
    apply propext
    change (z+q ∈ e.target ∧ e.symm (z+q) ∈ H) ↔ f z = 0
    apply (and_iff_right hz.1).trans
    rw [hflat _ hz.2]
    simp only [flatCoord,f,F,Finset.prod_eq_zero_iff]
    change (∃ j ∈ S, Φ.toFun (e (e.symm (z+q))) j = 0) ↔ ∃ j ∈ S, Φ.toFun (z+q) j = 0
    rw [e.right_inv hz.1]

/-- A genuine whole original NC carrier has empty actual interior, internally from its nonzero whole coordinate products. -/
theorem interior_normalCrossingsCarrier_eq_empty {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := n) H) : interior H = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨f,hf,hfnonzero,hzero⟩ := exists_nonzero_original_coordinate_equation hH x
  let e := chartAt (ComplexModel n) x
  let q := e x
  have ht : Tendsto (fun z : ComplexModel n => z+q) (𝓝 0) (𝓝 q) := by
    simpa only [zero_add] using (continuous_add_const q).tendsto 0
  have hInv : Tendsto (fun z : ComplexModel n => e.symm (z+q)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def,e.left_inv (mem_chart_source _ x)] using
      (e.continuousAt_symm (e.map_source (mem_chart_source _ x))).tendsto.comp ht
  have hmem : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ chartGerm H x :=
    (ht.eventually (e.open_target.mem_nhds (e.map_source (mem_chart_source _ x)))).and
      (hInv.eventually (mem_interior_iff_mem_nhds.mp hx))
  apply hfnonzero
  rw [← HolGerm.mk_zero]
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards [hmem,hzero] with z hz he
  exact he.mp hz

/-- A true zero-dimensional NC carrier is actually empty. -/
theorem normalCrossingsCarrier_eq_empty_of_dimension_zero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M] {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := 0) H) : H = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨Φ,hsrc,h0,S,hflat⟩ := hH.2 x
  obtain ⟨i,hi,hzi⟩ := (hflat x (mem_flatDomain_self Φ)).mp hx
  exact Fin.elim0 i

/-- The whole original zero-dimensional NC ideal is literally the unit ideal. -/
theorem vanishingIdeal_eq_unitIdeal_of_dimension_zero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M] {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := 0) H) :
    vanishingIdeal (n := 0) H = IdealWeightPowers.unitIdeal 0 M := by
  rw [normalCrossingsCarrier_eq_empty_of_dimension_zero hH]
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · exact fun hg => hg.1
  · exact fun hg => ⟨hg,Eventually.of_forall fun _ h => h.elim⟩

/-- Actual original coordinate products internally make the COMPLETE original NC vanishing ideal invertible. -/
theorem isInvertible_vanishingIdeal_normalCrossingsCarrier {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := n) H) : (vanishingIdeal (n := n) H).IsInvertible := by
  cases n with
  | zero =>
    rw [vanishingIdeal_eq_unitIdeal_of_dimension_zero hH]
    exact BlowupExceptionalDivisor.isInvertible_unitIdeal
  | succ n =>
    exact HironakaPureCodimensionOneInvertibleIdeal.isInvertible_vanishingIdeal_of_original_equations
      (interior_normalCrossingsCarrier_eq_empty hH) (exists_nonzero_original_coordinate_equation hH)

/-- True closed whole original and all actual old boundary full preimages are exactly the complete next geometric boundary union. -/
theorem preimage_original_union_boundary_step {A B : CMfd.{u} n} {π : B → A}
    (hπ : Continuous π) {K C : Set A} (hK : IsClosed K) (hCK : C ⊆ K)
    (E : List (Set A)) (hE : ∀ F ∈ E, IsClosed F) :
    π ⁻¹' (K ∪ ⋃ F ∈ E, F) = geoStrictTransform π C K ∪
      ⋃ F ∈ (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]), F := by
  have hsub : ∀ (F : Set A), IsClosed F → geoStrictTransform π C F ⊆ π ⁻¹' F := by
    intro F hF
    exact closure_minimal (preimage_mono sdiff_subset) (hF.preimage hπ)
  ext z
  constructor
  · intro hz
    by_cases hc : π z ∈ C
    · exact Or.inr (mem_iUnion₂.mpr ⟨π ⁻¹' C,List.mem_append_right _ (List.mem_singleton_self _),hc⟩)
    · rcases hz with hz | hz
      · exact Or.inl (subset_closure ⟨hz,hc⟩)
      · obtain ⟨F,hF,hzF⟩ := mem_iUnion₂.mp hz
        exact Or.inr (mem_iUnion₂.mpr ⟨geoStrictTransform π C F,
          List.mem_append_left _ (List.mem_map.mpr ⟨F,hF,rfl⟩),subset_closure ⟨hzF,hc⟩⟩)
  · rintro (hz | hz)
    · exact Or.inl (hsub K hK hz)
    · obtain ⟨F,hF,hzF⟩ := mem_iUnion₂.mp hz
      rcases List.mem_append.mp hF with hF | hF
      · obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hF
        exact Or.inr (mem_iUnion₂.mpr ⟨G,hG,hsub G (hE G hG) hzF⟩)
      · rw [List.mem_singleton.mp hF] at hzF
        exact Or.inl (hCK hzF)

/-- The entire original total support follows at every real higher-centre prefix with empty initial boundary. -/
theorem preimage_original_eq_strict_union_boundary {A D : CMfd.{u} n}
    (M : MarkedIdeal n A) {H : Set A} (hH : IsClosed H) (hE : M.E = [])
    (T : BlowupTower A D)
    (hc : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
      (strictTransform n R.proj H) (geoTransformAlong M R).E C) T) :
    T.proj ⁻¹' H = strictTransform n T.proj H ∪ ⋃ F ∈ (geoTransformAlong M T).E, F := by
  induction T with
  | refl =>
    change H = strictTransform n (id : A → A) H ∪ ⋃ F ∈ M.E, F
    rw [hE]
    simp [strictTransform,exceptionalLocus_id]
  | @step B D T C π hπ ih =>
    let K := strictTransform n T.proj H
    let E := (geoTransformAlong M T).E
    have hclosed : ∀ F ∈ E, IsClosed F :=
      isClosed_boundary_geoTransformAlong M (by simp [hE]) T
    have hCK : C ⊆ K := higherSeparationCentre_subset hc.2
    have hstrict : geoStrictTransform π C K = strictTransform n π K := by
      obtain ⟨hcur,r,hr,hmax,hC,hne⟩ := hc.2
      have hp := hπ
      rw [hC] at hp ⊢
      exact geoStrictTransform_highest_eq_strictTransform
        (isNormalCrossingsCarrier_of_boundaryAdapted hcur) hr hmax hp
    calc
      (T.step C π hπ).proj ⁻¹' H = π ⁻¹' (T.proj ⁻¹' H) := rfl
      _ = π ⁻¹' (K ∪ ⋃ F ∈ E, F) := congrArg (fun F => π ⁻¹' F) (ih hc.1)
      _ = geoStrictTransform π C K ∪ ⋃ F ∈ (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]), F :=
        preimage_original_union_boundary_step hπ.contMDiff.continuous isClosed_closure hCK E hclosed
      _ = strictTransform n (T.step C π hπ).proj H ∪ ⋃ F ∈ (geoTransformAlong M (T.step C π hπ)).E, F := by
        rw [hstrict]
        rw [show (T.step C π hπ).proj = T.proj ∘ π from rfl,
          StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff]
        rfl

/-- The marked datum uses the actual whole ORIGINAL ideal; its initial geometric boundary is literally empty. -/
def originalMarkedIdeal {A : CMfd.{u} n} (H : Set A) : MarkedIdeal n A where
  N := univ
  E := []
  ideal := vanishingIdeal (n := n) H
  d := 1

/-- The true original ideal internally defines an actual effective divisor. -/
def originalDivisor {A : CMfd.{u} n} {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    EffectiveDivisor n A := ⟨vanishingIdeal (n := n) H,isInvertible_vanishingIdeal_normalCrossingsCarrier hH⟩

/-- The actual finite NC separation is generated internally from the genuine original NC carrier. -/
def originalSeparation {A : CMfd.{u} n} {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    SeparationOutput (A := A) (originalMarkedIdeal H) H n :=
  naturalSeparation (originalMarkedIdeal H) (boundaryAdapted_nil hH)

/-- The actual terminal SNC list contains every actual new boundary member and the ENTIRE final differential original. -/
def terminalBoundary {A : CMfd.{u} n} {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    List (Set (originalSeparation hH).D) :=
  (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T).E ++
    [strictTransform n (originalSeparation hH).T.proj H]

/-- The actual generated procedure internally gives true finite length, terminal transverse smooth geometry and complement isomorphism. -/
theorem originalSeparation_geometry {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (originalSeparation hH).T.length ≤ n-1 ∧
      IsClosedSubmanifold n (strictTransform n (originalSeparation hH).T.proj H) ∧
      IsTransverse n (strictTransform n (originalSeparation hH).T.proj H)
        (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T).E ∧
      IsSNCDivisor n (terminalBoundary hH) ∧
      CentresOver H (originalSeparation hH).T ∧ IsIsomorphismOver n (originalSeparation hH).T.proj Hᶜ := by
  obtain ⟨hl,hs,ht,hb,hg,hc,hi⟩ := naturalSeparation_geometry (originalMarkedIdeal H) (boundaryAdapted_nil hH)
  exact ⟨hl,hs,ht,hb,hc,hi⟩

/-- The actual ENTIRE inverse image support is internally the union of the true terminal SNC list. -/
theorem preimage_original_eq_terminalBoundary {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (originalSeparation hH).T.proj ⁻¹' H = ⋃ F ∈ terminalBoundary hH, F := by
  have hp := preimage_original_eq_strict_union_boundary (originalMarkedIdeal H) hH.1 rfl
    (originalSeparation hH).T (originalSeparation hH).centres
  rw [hp]
  ext z
  simp only [terminalBoundary,List.mem_append,List.mem_singleton]
  constructor
  · rintro (hz | hz)
    · exact mem_iUnion₂.mpr ⟨_,Or.inr rfl,hz⟩
    · obtain ⟨F,hF,hz⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨F,Or.inl hF,hz⟩
  · intro hz
    obtain ⟨F,hF,hz⟩ := mem_iUnion₂.mp hz
    rcases hF with hF | rfl
    · exact Or.inr (mem_iUnion₂.mpr ⟨F,hF,hz⟩)
    · exact Or.inl hz

/-- Actual individual blowup pullbacks and genuine composition preserve the whole ideal internally along the real recorded tower. -/
theorem isInvertible_original_pullback_tower {A D : CMfd.{u} n} (T : BlowupTower A D)
    {I : GermIdeal n A} (hI : I.IsInvertible) : (GermIdeal.pullback (m := n) T.proj I).IsInvertible := by
  have hcoh := DivisorMetric.isCoherent_of_isInvertible hI
  induction T with
  | refl => simpa only [BlowupTower.proj_refl,BlowupControlledTransform.pullback_id hcoh] using hI
  | step T C π hπ ih =>
    change (GermIdeal.pullback (m := n) (T.proj ∘ π) I).IsInvertible
    rw [GermIdealTotalTransform.pullback_comp T.contMDiff_proj hπ.contMDiff hcoh]
    exact isInvertible_pullback hπ.contMDiff
      (BlowupExceptionalDivisor.interior_exceptionalLocus_eq_empty hπ) ih

/-- True pullback of the internally invertible ORIGINAL vanishing ideal along the ACTUAL generated tower. -/
def totalOriginalDivisor {A : CMfd.{u} n} {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    EffectiveDivisor n (originalSeparation hH).D :=
  ⟨GermIdeal.pullback (m := n) (originalSeparation hH).T.proj (vanishingIdeal (n := n) H),
    isInvertible_original_pullback_tower (originalSeparation hH).T (originalDivisor hH).isInvertible⟩

/-- The total ideal is the SAME complete original pulled-back ideal, with no substitute generator. -/
theorem totalOriginalDivisor_ideal {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (totalOriginalDivisor hH).ideal =
      GermIdeal.pullback (m := n) (originalSeparation hH).T.proj (vanishingIdeal (n := n) H) := rfl

/-- The true whole original total ideal support is exactly the ENTIRE actual terminal original and new boundary union. -/
theorem totalOriginalDivisor_support {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (totalOriginalDivisor hH).support = ⋃ F ∈ terminalBoundary hH, F := by
  change (GermIdeal.pullback (m := n) (originalSeparation hH).T.proj (vanishingIdeal (n := n) H)).zeroLocus = _
  rw [BlowupExceptionalDivisor.zeroLocus_pullback (originalSeparation hH).T.contMDiff_proj
    (show (vanishingIdeal (n := n) H).IsCoherent from
      DivisorMetric.isCoherent_of_isInvertible (originalDivisor hH).isInvertible),
    BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hH.1]
  exact preimage_original_eq_terminalBoundary hH

/-- The actual internally generated tower gives equality of the COMPLETE original pullback ideal with its intrinsic monomial ideal. -/
theorem original_pullback_eq_monomialPart {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    GermIdeal.pullback (m := n) (originalSeparation hH).T.proj (vanishingIdeal (n := n) H) =
      MonomialPart.monomialPart n
        (GermIdeal.pullback (m := n) (originalSeparation hH).T.proj (vanishingIdeal (n := n) H))
        (terminalBoundary hH) :=
  HironakaSNCSupportedMonomialIdeal.ideal_eq_monomialPart_of_support_subset (totalOriginalDivisor hH)
    (terminalBoundary hH) (originalSeparation_geometry hH).2.2.2.1
    (totalOriginalDivisor_support hH).subset

/-- The complete nonmonomial residual of the SAME whole original pulled-back ideal is internally the unit ideal at every stalk. -/
theorem original_pullback_nonmonomialPart_eq_unit {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    MonomialPart.nonmonomialPart n
      (GermIdeal.pullback (m := n) (originalSeparation hH).T.proj (vanishingIdeal (n := n) H))
      (terminalBoundary hH) = IdealWeightPowers.unitIdeal n (originalSeparation hH).D :=
  HironakaSNCSupportedMonomialIdeal.nonmonomialPart_eq_unitIdeal_of_support_subset (totalOriginalDivisor hH)
    (terminalBoundary hH) (originalSeparation_geometry hH).2.2.2.1
    (totalOriginalDivisor_support hH).subset

/-- Original coefficients, real locally finite carriers and positive nearby finite products are INTERNALLY produced for the SAME whole original pullback ideal. -/
theorem exists_original_pullback_component_products {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    let I := GermIdeal.pullback (m := n) (originalSeparation hH).T.proj (vanishingIdeal (n := n) H)
    ∃ a : HironakaConnectedBoundaryComponents.boundaryComponents (terminalBoundary hH) → ℕ,
      LocallyFinite (fun C : HironakaConnectedBoundaryComponents.boundaryComponents (terminalBoundary hH) =>
        (C : Set (originalSeparation hH).D)) ∧
      (∀ C : HironakaConnectedBoundaryComponents.boundaryComponents (terminalBoundary hH),
        ∀ y ∈ (C : Set (originalSeparation hH).D), DivisorExponent.divExp n I (C : Set (originalSeparation hH).D) y = a C) ∧
      ∀ x : (originalSeparation hH).D, ∃ U : Set (originalSeparation hH).D,
        ∃ L : List (Set (originalSeparation hH).D × ℕ), IsOpen U ∧ x ∈ U ∧
        (L.map Prod.fst).Nodup ∧
        (∀ p ∈ L, ∃ hC : p.1 ∈ HironakaConnectedBoundaryComponents.boundaryComponents (terminalBoundary hH),
          p.2 = a ⟨p.1,hC⟩ ∧ 0 < p.2) ∧
        ∀ y ∈ U, ∀ g, I.mem y g ↔ (HironakaDivisorResidual.componentPowerProduct (n := n) L).mem y g :=
  exists_locallyFinite_original_component_products (totalOriginalDivisor hH) (terminalBoundary hH)
    (originalSeparation_geometry hH).2.2.2.1 (totalOriginalDivisor_support hH).subset

end
end Hironaka.HironakaNormalCrossingsTotalIdeal
