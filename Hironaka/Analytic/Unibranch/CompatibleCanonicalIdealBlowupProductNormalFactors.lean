import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges

/-! Original zero-plane normal functions and their full native strict-quotient
stalk factors. The defining monomial equation retains epsilon at every point,
including epsilon zero. Existing actual quotient maps and scalar actions are
used throughout. No raw-fibre cancellation, point from a compatible pair,
canonical-history comparison or flattening/termination statement is asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupProductNormalFactors
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualWholeStalkHolomorphicPullback
  CompatibleCanonicalIdealBlowupExplicitProductCharts CompatibleCanonicalIdealBlowupMonomialLift
  CompatibleCanonicalIdealBlowupPivotChart CompatibleCanonicalIdealBlowupPivotOpenRanges
open scoped ProductComplexManifold

private theorem native_original_function {a b : ℕ} {S T : Type}
    [TopologicalSpace S] [TopologicalSpace T]
    [ChartedSpace (ComplexModel a) S] [IsComplexManifold a S]
    [ChartedSpace (ComplexModel b) T] [IsComplexManifold b T]
    {f : S → T} (hf : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel b) ∞ f)
    (z : S) (g : T → ℂ) (hg : HolomorphicAt b g (f z)) :
    (ChartedSpace.locallyRingedSpaceMap f hf).stalkMap z
        (actualOriginalFunctionGerm (f z) g hg) =
      actualOriginalFunctionGerm z (g ∘ f)
        (hg.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt)) := by
  apply (actualStalkChartEquiv (n := a) z).injective
  rw [actualNativeStalk_chart_pullback,actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function,actualOriginalFunctionGerm_chart]

private theorem original_germ_congr {n : ℕ} {S : Type}
    [TopologicalSpace S] [ChartedSpace (ComplexModel n) S] [IsComplexManifold n S]
    (z : S) (f g : S → ℂ) (hf : HolomorphicAt n f z) (hg : HolomorphicAt n g z)
    (hfg : f =ᶠ[𝓝 z] g) :
    actualOriginalFunctionGerm z f hf = actualOriginalFunctionGerm z g hg := by
  apply (actualStalkChartEquiv (n := n) z).injective
  rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original z f g hf hg hfg

private theorem original_germ_mul {n : ℕ} {S : Type}
    [TopologicalSpace S] [ChartedSpace (ComplexModel n) S] [IsComplexManifold n S]
    (z : S) (f g : S → ℂ) (hf : HolomorphicAt n f z) (hg : HolomorphicAt n g z) :
    actualOriginalFunctionGerm z (fun w => f w*g w) (hf.mul hg) =
      actualOriginalFunctionGerm z f hf * actualOriginalFunctionGerm z g hg := by
  apply (actualStalkChartEquiv (n := n) z).injective
  rw [map_mul,actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

private theorem monomial_normal {n r : ℕ} (j i : Fin r) (w : ComplexModel (n+r)) :
    monomial n (j.natAdd n) w (i.natAdd n) =
      if i=j then w (i.natAdd n) else w (i.natAdd n)*w (j.natAdd n) := by
  by_cases h : i=j
  · subst i
    simp [monomial_apply]
  · have hij : i.natAdd n ≠ j.natAdd n := by simpa using h
    rw [monomial_apply,if_pos ⟨by simp,hij⟩,if_neg h]

private theorem stalk_comp_apply {A B C : LocallyRingedSpace.{0}}
    (f : A ⟶ B) (g : B ⟶ C) (z : A)
    (r : (C.presheaf.stalk (g.base (f.base z))).carrier) :
    (f ≫ g).stalkMap z r = f.stalkMap z (g.stalkMap (f.base z) r) :=
  ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp f g z) r

section ProductCharts
variable {n r : ℕ} {P : Type} [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]

/-- The original normal-coordinate function on the projected product base. -/
def originalNormalFunction (a : ProductNormalCharts n r P) (j i : Fin r) :
    productChartOpen a j → ℂ := fun z => z.val.base.2 i

/-- The pivot ratio is one; the remaining ratios are the original chart slots. -/
def normalRatioFunction (a : ProductNormalCharts n r P) (j i : Fin r) :
    productChartOpen a j → ℂ :=
  if i=j then fun _ => 1 else productNormalFunction a j i

theorem original_normal_epsilon_ratio (a : ProductNormalCharts n r P)
    (j i : Fin r) (z : productChartOpen a j) :
    originalNormalFunction a j i z =
      productNormalFunction a j j z * normalRatioFunction a j i z := by
  have h := congrArg (fun w : ComplexModel (n+r) => w (i.natAdd n))
    ((productNormalChart (n := n) a.base j).monomial_toFun z.property)
  change monomial n (j.natAdd n) (productChartCoordinates a j z) (i.natAdd n) =
    (productNormalChart (n := n) a.base j).τ (i.natAdd n) z.val.base at h
  rw [monomial_normal,productNormalChart_normal] at h
  by_cases hij : i=j
  · subst i
    simpa [originalNormalFunction,productNormalFunction,normalRatioFunction] using h.symm
  · simpa [originalNormalFunction,productNormalFunction,normalRatioFunction,hij,mul_comm] using h.symm

theorem normal_function_holomorphic (a : ProductNormalCharts n r P) (j i : Fin r)
    (z : productChartOpen a j) : HolomorphicAt (n+r) (productNormalFunction a j i) z :=
  ((productNormalChart (n := n) a.base j).holomorphicAt_coord z.property (i.natAdd n)).comp_contMDiff
    (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)

theorem original_normal_holomorphic (a : ProductNormalCharts n r P) (j i : Fin r)
    (z : productChartOpen a j) : HolomorphicAt (n+r) (originalNormalFunction a j i) z := by
  have he : originalNormalFunction a j i =
      fun z => productNormalFunction a j j z * normalRatioFunction a j i z :=
    funext (original_normal_epsilon_ratio a j i)
  rw [he]
  by_cases hij : i=j
  · simp only [normalRatioFunction,if_pos hij]
    exact (normal_function_holomorphic a j j z).mul (holomorphicAt_const 1)
  · simp only [normalRatioFunction,if_neg hij]
    exact (normal_function_holomorphic a j j z).mul (normal_function_holomorphic a j i z)

/-- The entire native quotient-stalk class of a chart normal slot. -/
def strictNormalClass (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (j i : Fin r) (z : strictChartCarrier a W j) :=
  (actualSubspaceInclusion (n := n+r) (M := productChartOpen a j) (strictChartCarrier a W j)).stalkMap z
    (actualOriginalFunctionGerm (M := productChartOpen a j) z.val (productNormalFunction a j i)
      (normal_function_holomorphic a j i z.val))

theorem local_original_normal_class (a : ProductNormalCharts n r P)
    (W : Set (P × ComplexModel r)) (j i : Fin r) (z : strictChartCarrier a W j) :
    (actualSubspaceInclusion (n := n+r) (M := productChartOpen a j) (strictChartCarrier a W j)).stalkMap z
        (actualOriginalFunctionGerm (M := productChartOpen a j) z.val (originalNormalFunction a j i)
          (original_normal_holomorphic a j i z.val)) =
      strictNormalClass a W j j z * (if i=j then 1 else strictNormalClass a W j i z) := by
  classical
  let Q := (actualSubspaceInclusion (n := n+r) (M := productChartOpen a j) (strictChartCarrier a W j)).stalkMap z
  by_cases hij : i=j
  · subst i
    rw [if_pos (show j=j from rfl),mul_one]
    change Q _ = Q _
    apply congrArg Q
    apply original_germ_congr
    exact Eventually.of_forall fun w => by
      simpa [normalRatioFunction] using original_normal_epsilon_ratio a j j w
  · rw [if_neg hij]
    change Q _ = Q _ * Q _
    rw [← map_mul]
    apply congrArg Q
    exact (original_germ_congr (S := productChartOpen a j) z.val (originalNormalFunction a j i)
      (fun w => productNormalFunction a j j w * productNormalFunction a j i w)
      (original_normal_holomorphic a j i z.val)
      ((normal_function_holomorphic a j j z.val).mul (normal_function_holomorphic a j i z.val))
      (Eventually.of_forall fun w => by
        simpa [normalRatioFunction,hij] using original_normal_epsilon_ratio a j i w)).trans
      (original_germ_mul (S := productChartOpen a j) z.val (productNormalFunction a j j) (productNormalFunction a j i)
        (normal_function_holomorphic a j j z.val) (normal_function_holomorphic a j i z.val))

/-- Pulling the independent original global normal class through the genuine
open inclusion gives the exceptional factor times the ratio in the ENTIRE
local strict quotient stalk, not just its residue at the query point. -/
theorem strict_original_normal_factor (a : ProductNormalCharts n r P)
    (W : Set (P × ComplexModel r)) (j i : Fin r) (z : strictChartCarrier a W j) :
    (strictChartInclusion a W j).stalkMap z
        (geometricCoordinateClass W (productNormalChart (n := n) a.base j)
          ((strictChartInclusion a W j).base z)
          (by rw [a.domain j]; trivial) (i.natAdd n)) =
      strictNormalClass a W j j z * (if i=j then 1 else strictNormalClass a W j i z) := by
  let p := (strictChartInclusion a W j).base z
  let c := productNormalChart (n := n) a.base j
  let f := c.τ (i.natAdd n) ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0}
  have hp : p.val.base ∈ c.dom := by rw [a.domain j]; trivial
  have hf : HolomorphicAt (n+r) f p.val :=
    (holomorphicAt_flatCoord c.Φ (i.natAdd n) hp).comp_contMDiff
      (Eventually.of_forall fun _ => contMDiff_blowupProj.contMDiffAt)
  let v := (Subtype.val : productChartOpen a j →
    BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0})
  let inc := actualSubspaceInclusion (n := n+r) (strictChartCarrier a W j)
  have hs := ConcreteCategory.congr_hom
    (actualSubspaceRingedMap_stalk_square (f := v) contMDiff_subtype_val
      (fun _ hx => hx) z) (actualOriginalFunctionGerm p.val f hf)
  have hv : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (n+r)) ∞ v :=
    contMDiff_subtype_val
  have ht := native_original_function (S := productChartOpen a j) (f := v) hv z.val f hf
  have hcomp : HolomorphicAt (n+r) (f ∘ v) z.val :=
    hf.comp_contMDiff (f := v) (y := z.val) (Eventually.of_forall fun _ => hv.contMDiffAt)
  have he : actualOriginalFunctionGerm (M := productChartOpen a j) z.val (f ∘ v) hcomp =
      actualOriginalFunctionGerm (M := productChartOpen a j) z.val (originalNormalFunction a j i)
        (original_normal_holomorphic a j i z.val) := by
    apply original_germ_congr
    exact Eventually.of_forall fun w => productNormalChart_normal a.base j i w.val.base
  change (strictChartInclusion a W j).stalkMap z
    ((actualSubspaceInclusion (n := n+r) (actualStrictCarrier (n := n) W)).stalkMap p
      (actualOriginalFunctionGerm p.val f hf)) = _
  exact hs.trans ((congrArg (inc.stalkMap z) (ht.trans he)).trans
    (local_original_normal_class a W j i z))

/-- The existing actual native normal dictionary yields its full epsilon-ratio factor. -/
theorem strict_section_original_normal_factor {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    (j i : Fin r) (z : strictChartCarrier a W j)
    (s : (A.presheaf.stalk (K.base ((strictChartInclusion a W j).base z))).carrier)
    (hs : K.stalkMap ((strictChartInclusion a W j).base z) s =
      geometricCoordinateClass W (productNormalChart (n := n) a.base j)
        ((strictChartInclusion a W j).base z) (by rw [a.domain j]; trivial) (i.natAdd n)) :
    (strictChartTo a W K j).stalkMap z s =
      strictNormalClass a W j j z * (if i=j then 1 else strictNormalClass a W j i z) :=
  (stalk_comp_apply (strictChartInclusion a W j) K z s).trans
    ((congrArg ((strictChartInclusion a W j).stalkMap z) hs).trans
      (strict_original_normal_factor a W j i z))

end ProductCharts
end
end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupProductNormalFactors
