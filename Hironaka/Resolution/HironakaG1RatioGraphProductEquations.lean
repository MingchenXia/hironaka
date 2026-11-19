import Hironaka.Resolution.HironakaG1ActualPairedRatioGraph
import Hironaka.Analytic.FibreDimensionLowerBound
import Hironaka.Resolution.HironakaG1ReaderProductSubmersions
import Hironaka.Resolution.HironakaG1FixedReaderComplementExtensions
import Hironaka.Analytic.AnalyticSubsetPreimage

/-! Exact product graph equations for the paired ratio lift and its local analyticity. -/
set_option autoImplicit false
open Set TopologicalSpace Filter
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1RatioGraphProductEquations
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupFlatCoordinates
  HironakaG1RelativeBoundaryProjections HironakaG1SNCReaderNormalization
  HironakaG1RelativeReaderWindow HironakaG1ReaderProductSubmersions
  HironakaG1FixedReaderComplementExtensions HironakaSmoothSubmersionMonomialChartPullback

variable {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m} {p : M} {q : N}
  {E : List (Set M)} {F : List (Set N)} {τ : Fin E.length ≃ Fin F.length}
  (R : RelativeReaders p q E F τ)

private abbrev A := Ambient R.r R.a R.b
private abbrev L (z : readerUnitWindow R) : M := firstReaderMap R z
private abbrev P (z : readerUnitWindow R) : N := secondReaderMap R z

def lPoint (z : readerUnitWindow R) : readerSource R.Φ₁ :=
  R.sourceDiffeomorph.symm ⟨joinBlock R.r R.a (leftProjection R.r R.a R.b z.val), z.property.1.2⟩

def rPoint (z : readerUnitWindow R) : readerSource R.Φ₂ :=
  R.targetDiffeomorph.symm ⟨joinBlock R.r R.b (rightProjection R.r R.a R.b z.val), z.property.2⟩

private theorem lBase (z : readerUnitWindow R) :
    (sourceProduct R.r R.a R.b z.val).1 = (R.sourceDiffeomorph (lPoint R z)).val := by
  let y : R.sourceCoordinateOpen := ⟨joinBlock R.r R.a (leftProjection R.r R.a R.b z.val),
    z.property.1.2⟩
  exact (congrArg Subtype.val (R.sourceDiffeomorph.apply_symm_apply y)).symm

private theorem rBase (z : readerUnitWindow R) :
    (targetProduct R.r R.a R.b (unitScaling R.r R.a R.b z.val)).1 =
      (R.targetDiffeomorph (rPoint R z)).val := by
  let y : R.targetCoordinateOpen := ⟨joinBlock R.r R.b (rightProjection R.r R.a R.b z.val),
    z.property.2⟩
  exact (congrArg Subtype.val (R.targetDiffeomorph.apply_symm_apply y)).symm

private theorem lComplement (z : readerUnitWindow R) (i : Fin R.a) :
    z.val.2.1 i = (R.sourceDiffeomorph (lPoint R z)).val (i.natAdd R.r) := by
  rw [← lBase R z]
  change z.val.2.1 i = joinCoordinates R.r R.a
    (euclideanBlock R.r z.val.1.1) (euclideanBlock R.a z.val.2.1) (i.natAdd R.r)
  rw [← blockProjection_apply, blockProjection_join]
  rfl

private theorem rComplement (z : readerUnitWindow R) (i : Fin R.b) :
    z.val.2.2 i = (R.targetDiffeomorph (rPoint R z)).val (i.natAdd R.r) := by
  rw [← rBase R z]
  change z.val.2.2 i = joinCoordinates R.r R.b
    (euclideanBlock R.r (fun j => z.val.1.2 j * z.val.1.1 j))
    (euclideanBlock R.b z.val.2.2) (i.natAdd R.r)
  rw [← blockProjection_apply, blockProjection_join]
  rfl

/-- The complementary block for the source-side holomorphic graph
contains both the ratio units and the extended target complement. -/
def leftGraphValue (a : Fin R.r → M → ℂ) (forward : M → ComplexModel R.b) (x : M) :
    ComplexModel (R.r+R.b) :=
  joinBlock R.r R.b (fun j => a j x, (euclideanBlock R.b).symm (forward x))

/-- The complementary block for the scaled target-side graph. -/
def rightGraphValue (b : Fin R.r → N → ℂ) (backward : N → ComplexModel R.a) (y : N) :
    ComplexModel (R.r+R.a) :=
  joinBlock R.r R.a (fun j => b j y, (euclideanBlock R.a).symm (backward y))

set_option maxHeartbeats 600000 in
/-- The paired ratio lift is the literal graph of its prescribed extension
in the source product coordinates and in the scaled target product coordinates. -/
theorem paired_ratio_graph_iff_product
    {C : Set M} {D : Set N} {U : Opens M} {V : Opens N} {G : Set (readerUnitWindow R)}
    (a : Fin R.r → M → ℂ) (b : Fin R.r → N → ℂ)
    (forward : M → ComplexModel R.b) (backward : N → ComplexModel R.a)
    (hL : BijOn (L R) G (C ∩ (U : Set M))) (hP : BijOn (P R) G (D ∩ (V : Set N)))
    (hGL : ∀ z ∈ G, z.val.1.2 = (fun j => a j (L R z)) ∧
      ∀ i : Fin R.b, forward (L R z) i = (R.targetDiffeomorph (rPoint R z)).val (i.natAdd R.r))
    (hGP : ∀ z ∈ G, z.val.1.2 = (fun j => b j (P R z)) ∧
      ∀ i : Fin R.a, backward (P R z) i = (R.sourceDiffeomorph (lPoint R z)).val (i.natAdd R.r)) :
    (∀ z : readerUnitWindow R, z ∈ G ↔ L R z ∈ C ∩ (U : Set M) ∧
      (sourceProduct R.r R.a R.b z.val).2 = leftGraphValue R a forward (L R z)) ∧
    (∀ z : readerUnitWindow R, z ∈ G ↔ P R z ∈ D ∩ (V : Set N) ∧
      (targetProduct R.r R.a R.b (unitScaling R.r R.a R.b z.val)).2 =
        rightGraphValue R b backward (P R z)) := by
  have lh (z : readerUnitWindow R) (hz : z ∈ G) :
      (sourceProduct R.r R.a R.b z.val).2 = leftGraphValue R a forward (L R z) := by
    change joinBlock R.r R.b (z.val.1.2,z.val.2.2) =
      joinBlock R.r R.b ((fun j => a j (L R z)), (euclideanBlock R.b).symm (forward (L R z)))
    apply congrArg (joinBlock R.r R.b)
    refine Prod.ext (hGL z hz).1 ?_
    funext i
    exact (rComplement R z i).trans ((hGL z hz).2 i).symm
  have rh (z : readerUnitWindow R) (hz : z ∈ G) :
      (targetProduct R.r R.a R.b (unitScaling R.r R.a R.b z.val)).2 =
        rightGraphValue R b backward (P R z) := by
    change joinBlock R.r R.a (z.val.1.2,z.val.2.1) =
      joinBlock R.r R.a ((fun j => b j (P R z)), (euclideanBlock R.a).symm (backward (P R z)))
    apply congrArg (joinBlock R.r R.a)
    refine Prod.ext (hGP z hz).1 ?_
    funext i
    exact (lComplement R z i).trans ((hGP z hz).2 i).symm
  constructor
  · intro z
    refine ⟨fun hz => ⟨hL.1 hz, lh z hz⟩, ?_⟩
    rintro ⟨hz, hEq⟩
    obtain ⟨w, hw, he⟩ := hL.2.2 hz
    have hp : lPoint R w = lPoint R z := Subtype.ext he
    have hProd : sourceProduct R.r R.a R.b w.val = sourceProduct R.r R.a R.b z.val := by
      apply Prod.ext
      · rw [lBase R w, lBase R z, hp]
      · rw [lh w hw, hEq, he]
    have hwz : w = z := Subtype.ext ((sourceProduct R.r R.a R.b).injective hProd)
    exact hwz ▸ hw
  · intro z
    refine ⟨fun hz => ⟨hP.1 hz, rh z hz⟩, ?_⟩
    rintro ⟨hz, hEq⟩
    obtain ⟨w, hw, he⟩ := hP.2.2 hz
    have hp : rPoint R w = rPoint R z := Subtype.ext he
    have hProd : targetProduct R.r R.a R.b (unitScaling R.r R.a R.b w.val) =
        targetProduct R.r R.a R.b (unitScaling R.r R.a R.b z.val) := by
      apply Prod.ext
      · rw [rBase R w, rBase R z, hp]
      · rw [rh w hw, hEq, he]
    have hh := congrArg (unitUnscaling R.r R.a R.b) ((targetProduct R.r R.a R.b).injective hProd)
    rw [unitUnscaling_unitScaling _ _ _ _ w.property.1.1,
      unitUnscaling_unitScaling _ _ _ _ z.property.1.1] at hh
    exact (Subtype.ext hh : w = z) ▸ hw

open AnalyticSubsetPreimage FibreDimensionLowerBound

section Analyticity
private abbrev d := (R.r+R.a)+(R.r+R.b)

private theorem first_euclidean_hol :
    ContMDiff 𝓘(ℂ,ComplexModel (d R)) 𝓘(ℂ,ComplexModel n) ∞
      (firstReaderMap R ∘ euclideanReaderChange R) :=
  (euclidean_reader_maps_submersions R).1.isSubmersion.contMDiff

private theorem second_euclidean_hol :
    ContMDiff 𝓘(ℂ,ComplexModel (d R)) 𝓘(ℂ,ComplexModel m) ∞
      (secondReaderMap R ∘ euclideanReaderChange R) :=
  (euclidean_reader_maps_submersions R).2.isSubmersion.contMDiff

/-- The simultaneous Euclidean graph window where both original reader maps
land in the chosen ambient opens. -/
def graphEquationWindow (U : Opens M) (V : Opens N) : Opens (euclideanReaderWindow R) :=
  ⟨(firstReaderMap R ∘ euclideanReaderChange R) ⁻¹' (U : Set M) ∩
    (secondReaderMap R ∘ euclideanReaderChange R) ⁻¹' (V : Set N),
    (U.isOpen.preimage (first_euclidean_hol R).continuous).inter
      (V.isOpen.preimage (second_euclidean_hol R).continuous)⟩

/-- Projection to the original ratio window, retaining the exact graph points. -/
def graphEquationWindowToRatio (U : Opens M) (V : Opens N) :
    graphEquationWindow R U V → readerUnitWindow R :=
  fun x => euclideanReaderChange R x.val

theorem leftGraphValue_hol (U : Opens M) (a : Fin R.r → M → ℂ)
    (forward : M → ComplexModel R.b)
    (ha : ∀ x ∈ U, ∀ i, HolomorphicAt n (a i) x)
    (hf : ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel R.b) ∞ forward U) :
    ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (R.r+R.b)) ∞
      (leftGraphValue R a forward) U := by
  have hPi : ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,Block R.r) ∞
      (fun x i => a i x) U := by
    intro x hx
    have h : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,Block R.r) ∞ (fun x i => a i x) x :=
      contMDiffAt_pi_space.mpr (fun i => contMDiffAt_of_eventually_mdifferentiableAt (ha x hx i))
    exact h.contMDiffWithinAt
  exact (joinBlock R.r R.b).contDiff.contMDiff.comp_contMDiffOn
    (hPi.prodMk_space ((euclideanBlock R.b).symm.contDiff.contMDiff.comp_contMDiffOn hf))

set_option maxHeartbeats 700000 in
/-- The exact graph equation is analytic in the simultaneous Euclidean
window, by the original carrier and the holomorphic complementary residual. -/
theorem analytic_ratio_graph_of_equation
    {C : Set M} (hC : IsComplexAnalyticSubset (n := n) C)
    (U : Opens M) (V : Opens N) (G : Set (readerUnitWindow R))
    (a : Fin R.r → M → ℂ) (forward : M → ComplexModel R.b)
    (ha : ∀ x ∈ U, ∀ j, HolomorphicAt n (a j) x)
    (hf : ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel R.b) ∞ forward U)
    (hEq : ∀ z : readerUnitWindow R, z ∈ G ↔
      L R z ∈ C ∩ (U : Set M) ∧
        (sourceProduct R.r R.a R.b z.val).2 = leftGraphValue R a forward (L R z)) :
    IsComplexAnalyticSubset (n := d R) (graphEquationWindowToRatio R U V ⁻¹' G) := by
  let P := graphEquationWindow R U V
  let baseMap : P → M := firstReaderMap R ∘ graphEquationWindowToRatio R U V
  have hBase : ContMDiff 𝓘(ℂ,ComplexModel (d R)) 𝓘(ℂ,ComplexModel n) ∞ baseMap :=
    (first_euclidean_hol R).comp contMDiff_subtype_val
  let E := ambientEuclidean R.r R.a R.b
  let normalMap : P → ComplexModel (R.r+R.b) := fun x =>
    (sourceProduct R.r R.a R.b (E.symm x.val.val)).2
  have hNormal : ContMDiff 𝓘(ℂ,ComplexModel (d R)) 𝓘(ℂ,ComplexModel (R.r+R.b)) ∞ normalMap := by
    exact (ContinuousLinearMap.snd ℂ (ComplexModel (R.r+R.a)) (ComplexModel (R.r+R.b))).contMDiff.comp
      ((sourceProduct R.r R.a R.b).contDiff.contMDiff.comp
        (E.symm.contDiff.contMDiff.comp (contMDiff_subtype_val.comp contMDiff_subtype_val)))
  have hmaps : MapsTo baseMap univ (U : Set M) := fun x _ => x.property.1
  have hValue : ContMDiff 𝓘(ℂ,ComplexModel (d R)) 𝓘(ℂ,ComplexModel (R.r+R.b)) ∞
      (leftGraphValue R a forward ∘ baseMap) :=
    contMDiffOn_univ.mp ((leftGraphValue_hol R U a forward ha hf).comp hBase.contMDiffOn hmaps)
  let h : P → ComplexModel (R.r+R.b) := fun x => normalMap x - leftGraphValue R a forward (baseMap x)
  have hh : ContMDiff 𝓘(ℂ,ComplexModel (d R)) 𝓘(ℂ,ComplexModel (R.r+R.b)) ∞ h :=
    hNormal.sub hValue
  have hSet : graphEquationWindowToRatio R U V ⁻¹' G =
      baseMap ⁻¹' C ∩ h ⁻¹' ({0} : Set (ComplexModel (R.r+R.b))) := by
    ext x
    change graphEquationWindowToRatio R U V x ∈ G ↔ baseMap x ∈ C ∧ h x = 0
    rw [hEq, sub_eq_zero]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, x.property.1⟩, h.2⟩⟩
  rw [hSet]
  exact (isComplexAnalyticSubset_preimage hBase hC).inter
    (isComplexAnalyticSubset_preimage hh (isComplexAnalyticSubset_singleton (0 : ComplexModel (R.r+R.b))))

end Analyticity

open CategoryTheory HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
  HironakaActualIntrinsicLabelledBoundaryIdeals HironakaG1ActualPairedRatioGraph

set_option maxHeartbeats 700000 in
/-- The actual intrinsic pair produces a closed analytic overlap on the
Euclidean ratio window, given by literal holomorphic graph equations in
both original reader projections. -/
theorem exists_actual_paired_ratio_graph_equations
    {C : Set M} {D : Set N}
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
    (p₀ : C) (R₀ : RelativeReaders p₀.val (e.hom.base p₀).val E F τ)
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (hI : ∀ i : Fin E.length, Ideal.map (e.hom.stalkMap p₀).hom
      (actualLabelledBoundaryTraceIdeal D F (τ i) (e.hom.base p₀)) =
        actualLabelledBoundaryTraceIdeal C E i p₀)
    (hC : IsComplexAnalyticSubset (n := n) C) :
    ∃ (U : Opens M) (V : Opens N) (G : Set (readerUnitWindow R₀))
      (a : Fin R₀.r → M → ℂ) (b : Fin R₀.r → N → ℂ)
      (forward : M → ComplexModel R₀.b) (backward : N → ComplexModel R₀.a),
      p₀.val ∈ U ∧ (e.hom.base p₀).val ∈ V ∧
      (U : Set M) ⊆ flatDomain R₀.Φ₁ ∧ (V : Set N) ⊆ flatDomain R₀.Φ₂ ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel R₀.b) ∞ forward U ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel R₀.a) ∞ backward V ∧
      (∀ x ∈ U, ∀ j, HolomorphicAt n (a j) x ∧ a j x ≠ 0) ∧
      (∀ y ∈ V, ∀ j, HolomorphicAt m (b j) y ∧ b j y ≠ 0) ∧
      BijOn (firstReaderMap R₀) G (C ∩ (U : Set M)) ∧
      BijOn (secondReaderMap R₀) G (D ∩ (V : Set N)) ∧
      (∀ z : readerUnitWindow R₀, z ∈ G ↔ firstReaderMap R₀ z ∈ C ∩ (U : Set M) ∧
        (sourceProduct R₀.r R₀.a R₀.b z.val).2 = leftGraphValue R₀ a forward (firstReaderMap R₀ z)) ∧
      (∀ z : readerUnitWindow R₀, z ∈ G ↔ secondReaderMap R₀ z ∈ D ∩ (V : Set N) ∧
        (targetProduct R₀.r R₀.a R₀.b (unitScaling R₀.r R₀.a R₀.b z.val)).2 =
          rightGraphValue R₀ b backward (secondReaderMap R₀ z)) ∧
      IsComplexAnalyticSubset (n := (R₀.r+R₀.a)+(R₀.r+R₀.b))
        (graphEquationWindowToRatio R₀ U V ⁻¹' G) := by
  obtain ⟨U,V,G,a,b,forward,backward,hp,hp',hU,hV,hF,hB,ha,hb,hL,hR,hGraph⟩ :=
    exists_actual_paired_ratio_graph e p₀ R₀ he hI
  have hGL : ∀ z ∈ G, z.val.1.2 = (fun j => a j (firstReaderMap R₀ z)) ∧
      ∀ i : Fin R₀.b, forward (firstReaderMap R₀ z) i =
        (R₀.targetDiffeomorph (rPoint R₀ z)).val (i.natAdd R₀.r) := by
    intro z hz
    obtain ⟨_, _, _, hRat, _, h⟩ := hGraph z hz
    exact ⟨hRat, fun i => (h.1 i).trans (targetComplement_eq_normalized e p₀ R₀ (rPoint R₀ z) i)⟩
  have hGP : ∀ z ∈ G, z.val.1.2 = (fun j => b j (secondReaderMap R₀ z)) ∧
      ∀ i : Fin R₀.a, backward (secondReaderMap R₀ z) i =
        (R₀.sourceDiffeomorph (lPoint R₀ z)).val (i.natAdd R₀.r) := by
    intro z hz
    obtain ⟨_, _, _, _, hRat, _, h⟩ := hGraph z hz
    exact ⟨hRat, fun i => (h i).trans (sourceComplement_eq_normalized e p₀ R₀ (lPoint R₀ z) i)⟩
  obtain ⟨hEqL,hEqR⟩ := paired_ratio_graph_iff_product R₀ a b forward backward hL hR hGL hGP
  exact ⟨U,V,G,a,b,forward,backward,hp,hp',hU,hV,hF,hB,ha,hb,hL,hR,hEqL,hEqR,
    analytic_ratio_graph_of_equation R₀ hC U V G a forward (fun x hx i => (ha x hx i).1) hF hEqL⟩

end
end Hironaka.HironakaG1RatioGraphProductEquations
