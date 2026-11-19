import Hironaka.Resolution.HironakaActualRelativeNormalGeometry
import Hironaka.Resolution.HironakaActualCoherentWeightedCoefficientMarked

/-! Literal weighted padding on the genuine normal product over the original
open, preserving the entire compressed ideal, common mark and ordered boundary.
Blueprint: hironaka-actual-weighted-normal-padding-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualWeightedNormalPadding
noncomputable section
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  GermIdealPullbackCalculus InvertibleIdealQuotient MarkedIdeals RestrictedIdealExtension
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  HironakaActualCentreJointJets HironakaActualZeroCoordinateContactSeed

/-- Entire actual finite generated ideals pull back along any holomorphic map,
including maps between different ambient dimensions. -/
theorem finiteFunctionIdeal_pullback
    {n m : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) X] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold m X] [IsComplexManifold n Y]
    {τ : Type*} (c : τ → Y → ℂ)
    (hc : ∀ i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f) :
    GermIdeal.pullback (m := m) f (finiteFunctionIdeal (n := n) c)=
      finiteFunctionIdeal (n := m) (fun i => c i ∘ f) := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨?_,?_⟩)
  · intro hg
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    refine IsInSpanAt.mono ?_ (isInSpanAt_comp hf ha)
    rintro _ ⟨b,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hg)
    rintro _ ⟨i,rfl⟩
    exact ⟨c i,isInSpanAt_self ⟨i,rfl⟩ (Eventually.of_forall fun y => hc i y),rfl⟩

private theorem finiteFunctionIdeal_sum
    {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] {ι κ : Type*} (c : ι → X → ℂ) (d : κ → X → ℂ)
    (hc : ∀ i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i))
    (hd : ∀ j,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (d j)) :
    finiteFunctionIdeal (n := n) (Sum.elim c d)=sumIdeal (n := n) (finiteFunctionIdeal c) (finiteFunctionIdeal d) := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨?_,?_⟩)
  · intro hg
    change IsInSpanAt (n := n) (fun s => (finiteFunctionIdeal c).mem x s ∨ (finiteFunctionIdeal d).mem x s) x g
    refine IsInSpanAt.mono ?_ hg
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl i => exact Or.inl (isInSpanAt_self ⟨i,rfl⟩ (Eventually.of_forall fun y => hc i y))
    | inr j => exact Or.inr (isInSpanAt_self ⟨j,rfl⟩ (Eventually.of_forall fun y => hd j y))
  · intro hg
    change IsInSpanAt (n := n) (fun s => (finiteFunctionIdeal c).mem x s ∨ (finiteFunctionIdeal d).mem x s) x g at hg
    refine IsInSpanAt.trans ?_ hg
    intro a ha
    rcases ha with ha | ha
    · refine IsInSpanAt.mono ?_ ha
      rintro _ ⟨i,rfl⟩
      exact ⟨Sum.inl i,rfl⟩
    · refine IsInSpanAt.mono ?_ ha
      rintro _ ⟨j,rfl⟩
      exact ⟨Sum.inr j,rfl⟩

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The original weights and one actual normal member of weight one. -/
def paddingWeight (w : ι → ℕ) : ι ⊕ Unit → ℕ := Sum.elim w (fun _ => 1)

/-- Literal old functions pulled back to the actual product, and its normal coordinate. -/
def paddingFunction (U : Opens (ComplexModel n)) (c : ι → U → ℂ) :
    ι ⊕ Unit → productOpen U → ℂ :=
  Sum.elim (fun i => c i ∘ projection U) (fun _ => relativeNormalCoordinate U)

/-- The singleton added weight does not alter even an empty original product. -/
theorem padding_common_mark (w : ι → ℕ) :
    weightedCommonMark (paddingWeight w)=weightedCommonMark w := by
  simp [weightedCommonMark,paddingWeight,Fintype.prod_sum_type]

/-- The genuine normal coordinate is holomorphic on the original product. -/
theorem normalCoordinate_mdifferentiable (U : Opens (ComplexModel n)) :
    MDifferentiable 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) (relativeNormalCoordinate U) := by
  have h : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) ∞
      (fun z : productOpen U => actualJointNormalProjection n 1 z.val 0) :=
    ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contMDiff.comp
    (actualJointNormalProjection n 1).contMDiff).comp
    (contMDiff_subtype_val (U := productOpen U))
  simpa [relativeNormalCoordinate,addedCoordinate,HironakaActualGraphFunctionalIdeal.graphFunction,
    zeroFunction,Function.comp_def] using h.mdifferentiable

/-- The full compressed ideal is the original pullback plus the normal M-th power. -/
theorem entire_padding_ideal (U : Opens (ComplexModel n)) (w : ι → ℕ) (c : ι → U → ℂ)
    (hc : ∀ i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i)) :
    weightedFunctionIdeal (paddingWeight w) (paddingFunction U c)=
      sumIdeal (n := n+1) (GermIdeal.pullback (m := n+1) (projection U) (weightedFunctionIdeal (n := n) w c))
        (finiteFunctionIdeal (fun _ : Unit => fun z : productOpen U =>
          relativeNormalCoordinate U z^weightedCommonMark w)) := by
  rw [weightedFunctionIdeal,padding_common_mark]
  have he : (fun i z => paddingFunction U c i z^(weightedCommonMark w/paddingWeight w i))=
      Sum.elim (fun i z => c i (projection U z)^(weightedCommonMark w/w i))
        (fun _ : Unit => fun z : productOpen U => relativeNormalCoordinate U z^weightedCommonMark w) := by
    funext i z
    cases i <;> simp [paddingFunction,paddingWeight]
  rw [he,finiteFunctionIdeal_sum]
  · rw [weightedFunctionIdeal,finiteFunctionIdeal_pullback
      (fun i y => c i y^(weightedCommonMark w/w i)) (fun i => (hc i).pow _)
      (projection U) (projection_contMDiff U)]
    rfl
  · intro i
    exact ((hc i).comp ((projection_contMDiff U).mdifferentiable (by simp))).pow _
  · intro _
    exact (normalCoordinate_mdifferentiable U).pow _

/-- The padded full marked record retains every old boundary position. -/
def paddingMarked (U : Opens (ComplexModel n)) (w : ι → ℕ) (c : ι → U → ℂ)
    (E : List (Set U)) : MarkedIdeal (n+1) (productOpen U) :=
  ⟨univ,E.map ((projection U) ⁻¹' ·),
    weightedFunctionIdeal (paddingWeight w) (paddingFunction U c),weightedCommonMark (paddingWeight w)⟩

/-- Equality of entire marked records with the original mark and ordered boundary. -/
theorem entire_padding_record (U : Opens (ComplexModel n)) (w : ι → ℕ) (c : ι → U → ℂ)
    (hc : ∀ i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i)) (E : List (Set U)) :
    paddingMarked U w c E=
      (⟨univ,E.map ((projection U) ⁻¹' ·),
        sumIdeal (n := n+1) (GermIdeal.pullback (m := n+1) (projection U) (weightedFunctionIdeal (n := n) w c))
          (finiteFunctionIdeal (fun _ : Unit => fun z : productOpen U =>
            relativeNormalCoordinate U z^weightedCommonMark w)),weightedCommonMark w⟩ :
        MarkedIdeal (n+1) (productOpen U)) := by
  unfold paddingMarked
  rw [entire_padding_ideal U w c hc,padding_common_mark]

end
end Hironaka.HironakaActualWeightedNormalPadding
