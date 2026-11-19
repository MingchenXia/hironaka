import Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
import Hironaka.Analytic.Unibranch.HironakaG10OpenChartHelpers
import Hironaka.Resolution.HironakaChowRelativeGraphPresentation
import Hironaka.Resolution.HironakaG10FlatOrdinaryPointFlattener

/-!
# The graph row of an ordinary morphism chart (G10-01-04/05, lane G10MW, run 0081)

For a holomorphic ambient lift `φ : U → V` of a morphism of reduced complex spaces (source carrier
`C ⊆ U ⊆ ℂ^m`, base chart point `c ∈ ℂ^d`) and finitely many functions `g` whose germs generate the
WHOLE vanishing ideal of `C` at a point `x`, ONE finite row
`F(u,z) = (u_k + c_k − ψ(z)_k)_k ⧺ (g_j(z))_j` on `ℂ^d × ℂ^m` presents, at the graph point
`(ψ x − c, x)`, exactly the native relative graph ideal whose quotient is the native source stalk
(`nativeRelativeGraphEquiv`).  Off the graph, the same row generates the unit ideal, so its cokernel
vanishes and is flat over every quotient of the parameter germ ring.

No named input; no analytic theorem is used beyond the existing germ calculus.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10MwGraphRow

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm OkaRelationSheaf OkaGermBridge
  HironakaRelativeNormalIdeal HironakaActualJointBaseFibre HironakaActualCentreJointJets
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaActualWholeStalkHolomorphicPullback HironakaChowRelativeGraphPresentation
  HironakaG10FlatOrdinaryPointFlattener
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen Hironaka.Analytic.Unibranch.HironakaG10OpenCoherentProjectionFlatOpen

variable {d m r : ℕ}

/-! ### The row -/

/-- **The graph row** of a chart: `u_k + c_k − ψ(z)_k` (`k < d`) followed by `g_j(z)` (`j < r`). -/
def graphRow (φ : ComplexModel m → ComplexModel d) (c : ComplexModel d)
    (g : Fin r → ComplexModel m → ℂ) :
    Fin 1 → Fin (d + r) → ComplexModel d × ComplexModel m → ℂ :=
  fun _ => Fin.addCases (motive := fun _ => ComplexModel d × ComplexModel m → ℂ)
    (fun k q => q.1 k + c k - φ q.2 k) (fun j q => g j q.2)

@[simp] theorem graphRow_castAdd (φ : ComplexModel m → ComplexModel d) (c : ComplexModel d)
    (g : Fin r → ComplexModel m → ℂ) (i : Fin 1) (k : Fin d) :
    graphRow φ c g i (Fin.castAdd r k) = fun q => q.1 k + c k - φ q.2 k := by
  simp [graphRow]

@[simp] theorem graphRow_natAdd (φ : ComplexModel m → ComplexModel d) (c : ComplexModel d)
    (g : Fin r → ComplexModel m → ℂ) (i : Fin 1) (j : Fin r) :
    graphRow φ c g i (Fin.natAdd d j) = fun q => g j q.2 := by
  simp [graphRow]

theorem range_addCases {α : Type*} (f : Fin (d + r) → α) :
    Set.range f = Set.range (f ∘ Fin.castAdd r) ∪ Set.range (f ∘ Fin.natAdd d) := by
  ext a
  constructor
  · rintro ⟨j, rfl⟩
    induction j using Fin.addCases with
    | left k => exact Or.inl ⟨k, rfl⟩
    | right j => exact Or.inr ⟨j, rfl⟩
  · rintro (⟨k, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- The row is holomorphic on `ℂ^d × W` when `ψ` and `g` are holomorphic on `W`. -/
theorem graphRow_differentiableOn (φ : ComplexModel m → ComplexModel d) (c : ComplexModel d)
    (g : Fin r → ComplexModel m → ℂ) {W : Set (ComplexModel m)}
    (hφ : DifferentiableOn ℂ φ W) (hg : ∀ j, DifferentiableOn ℂ (g j) W) :
    ∀ i j, DifferentiableOn ℂ (graphRow φ c g i j) (univ ×ˢ W) := by
  intro i j
  have hsnd : MapsTo Prod.snd (univ ×ˢ W : Set (ComplexModel d × ComplexModel m)) W :=
    fun q hq => hq.2
  induction j using Fin.addCases with
  | left k =>
    rw [graphRow_castAdd]
    have h1 : DifferentiableOn ℂ (fun q : ComplexModel d × ComplexModel m => q.1 k) (univ ×ˢ W) :=
      ((EuclideanSpace.proj k : ComplexModel d →L[ℂ] ℂ).comp
        (ContinuousLinearMap.fst ℂ (ComplexModel d) (ComplexModel m))).differentiableOn
    have h2 : DifferentiableOn ℂ (fun q : ComplexModel d × ComplexModel m => φ q.2 k) (univ ×ˢ W) :=
      (EuclideanSpace.proj k : ComplexModel d →L[ℂ] ℂ).differentiable.comp_differentiableOn
        (hφ.comp differentiableOn_snd hsnd)
    exact (h1.add_const (c k)).sub h2
  | right j =>
    rw [graphRow_natAdd]
    exact (hg j).comp differentiableOn_snd hsnd

theorem holAt_graphRow (φ : ComplexModel m → ComplexModel d) (c : ComplexModel d)
    (g : Fin r → ComplexModel m → ℂ) {W : Set (ComplexModel m)} (hW : IsOpen W)
    (hφ : DifferentiableOn ℂ φ W) (hg : ∀ j, DifferentiableOn ℂ (g j) W)
    {q : ComplexModel d × ComplexModel m} (hq : q.2 ∈ W) :
    ∀ i j, HolAt (graphRow φ c g i j) q := fun i j =>
  holAt_of_differentiableOn (isOpen_univ.prod hW) (graphRow_differentiableOn φ c g hφ hg i j)
    ⟨mem_univ _, hq⟩

/-! ### Germ computations -/

theorem splitModel_snd (d t : ℕ) (w : ComplexModel (d + t)) :
    (splitModel d t w).2 = actualJointNormalProjection d t w := by
  rfl

theorem normalProjection_splitModel_symm (d t : ℕ) (w : ComplexModel d × ComplexModel t) :
    actualJointNormalProjection d t ((splitModel d t).symm w) = w.2 := by
  rw [← splitModel_snd, ContinuousLinearEquiv.apply_symm_apply]

theorem splitModel_symm_castAdd (d t : ℕ) (w : ComplexModel d × ComplexModel t) (k : Fin d) :
    ((splitModel d t).symm w) (Fin.castAdd t k) = w.1 k := by
  rw [← tangentProjection_apply, tangentProjection_splitModel_symm]

/-- The source pullback of a germ, read on the product: the germ of `(u,z) ↦ h(z)`. -/
theorem ambientGermEquiv_jointNormalPullback (d t : ℕ) (p : ComplexModel d) (z : ComplexModel t)
    (h : ComplexModel t → ℂ) (hh : HolAt h z) :
    ambientGermEquiv d t (jointNormalPullback d t (germAt z h)) =
      germAt ((p, z) : ComplexModel d × ComplexModel t) (fun q => h q.2) := by
  have hh' : HolAt (fun q : ComplexModel d × ComplexModel t => h q.2) (p, z) :=
    HolAt.comp (φ := Prod.snd) (y := (p, z)) hh continuous_snd fun _ => differentiableAt_snd
  rw [germAt_of_holAt hh, germAt_of_holAt hh']
  unfold jointNormalPullback ambientGermEquiv
  rw [compAlgHom_mk, HolGerm.comapEquiv_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun q => by
    change h (z + actualJointNormalProjection d t ((splitModel d t).symm q)) = h (z + q.2)
    rw [normalProjection_splitModel_symm]

/-- The comap of a fibre germ along the second projection is its germ on the product. -/
theorem comap_snd_germAt (p : ComplexModel d) (z : ComplexModel m)
    (h : ComplexModel m → ℂ) (hh : HolAt h z) :
    HolGerm.comap (ContinuousLinearMap.snd ℂ (ComplexModel d) (ComplexModel m)) (germAt z h) =
      germAt ((p, z) : ComplexModel d × ComplexModel m) (fun q => h q.2) := by
  have hh' : HolAt (fun q : ComplexModel d × ComplexModel m => h q.2) (p, z) :=
    HolAt.comp (φ := Prod.snd) (y := (p, z)) hh continuous_snd fun _ => differentiableAt_snd
  rw [germAt_of_holAt hh, germAt_of_holAt hh', HolGerm.comap_mk]
  exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun q => rfl)

theorem isUnit_germAt {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {f : Z → ℂ} {y : Z}
    (hf : HolAt f y) (h : f y ≠ 0) : IsUnit (germAt y f) := by
  rw [germAt_of_holAt hf, isUnit_iff_eval_ne_zero, eval_mk]
  simpa using h

/-! ### The whole-ideal identity at graph points -/

section Graph

variable {U : Opens (ComplexModel m)} {V : Opens (ComplexModel d)} (φ : U → V)
  (hφ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞ φ)

/-- The translated lift is the literal difference of the ambient extension, near `0`. -/
theorem eventually_actualTranslatedMap_eq (ψ : ComplexModel m → ComplexModel d)
    (hψ : ∀ y (hy : y ∈ U), ψ y = (φ ⟨y, hy⟩).val) (x : U) :
    ∀ᶠ w in 𝓝 (0 : ComplexModel m),
      actualTranslatedMap (n := d) (m := m) φ x w = ψ (x.val + w) - ψ x.val := by
  have hU : ∀ᶠ w in 𝓝 (0 : ComplexModel m), x.val + w ∈ U :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      (by simpa only [Pi.add_apply, Function.id_def, add_zero] using U.isOpen.mem_nhds x.property)
  filter_upwards [hU] with w hw
  have h := actualTranslatedMap_open_apply (M := ComplexModel m) (O := U) φ x.val (x.val + w)
    x.property hw (by rw [chartAt_self_eq]; trivial)
  have hl : (chartAt (ComplexModel m) x.val) (x.val + w) - (chartAt (ComplexModel m) x.val) x.val = w := by
    change (x.val + w) - x.val = w
    abel
  rw [hl] at h
  refine h.trans ?_
  rw [hψ _ hw, hψ _ x.property]
  rfl

/-- **The graph-row ideal is the native relative graph ideal** at every graph point: under the block
equivalence `ambientGermEquiv`, the whole ideal `nativeRelativeGraphIdeal φ C x` (whose quotient is the
native source stalk over the base germ ring) is generated by the germs of the ONE row at
`(ψ x − c, x)`, provided the germs of `g` at `x` generate the whole vanishing ideal of `C` at `x`. -/
theorem map_nativeRelativeGraphIdeal_eq_idealAt (C : Set U) (x : C)
    (ψ : ComplexModel m → ComplexModel d) (hψ : ∀ y (hy : y ∈ U), ψ y = (φ ⟨y, hy⟩).val)
    (hψhol : ∀ k, HolAt (fun w => ψ w k) x.val.val)
    (c : ComplexModel d) (g : Fin r → ComplexModel m → ℂ) (hg : ∀ j, HolAt (g j) x.val.val)
    (hgen : wholeChartStalkIdeal (vanishingIdeal (n := m) C) x.val x.val (mem_chart_source _ x.val) =
      Ideal.span (Set.range fun j => germAt x.val.val (g j))) :
    Ideal.map (ambientGermEquiv d m).toRingHom (nativeRelativeGraphIdeal hφ C x) =
      idealAt d m (graphRow ψ c g) (ψ x.val.val - c, x.val.val) := by
  have hdef : nativeRelativeGraphIdeal hφ C x = relativeGraphIdeal d m
      (actualTranslatedMap (n := d) (m := m) φ x.val) (actualTranslatedMap_holomorphic hφ x.val)
      (wholeChartStalkIdeal (vanishingIdeal (n := m) C) x.val x.val (mem_chart_source _ x.val)) := rfl
  -- source generators
  have hsrc : ∀ j, ambientGermEquiv d m (relativeSourcePullback d m (germAt x.val.val (g j))) =
      germAt ((ψ x.val.val - c, x.val.val) : ComplexModel d × ComplexModel m)
        (graphRow ψ c g 0 (Fin.natAdd d j)) := by
    intro j
    rw [relativeSourcePullback_eq_normalPullback, graphRow_natAdd]
    exact ambientGermEquiv_jointNormalPullback d m _ _ (g j) (hg j)
  -- graph-equation generators
  have heqn : ∀ k : Fin d, ambientGermEquiv d m
      (coordinateGerm (Fin.castAdd m k) - jointNormalPullback d m
        (compAlgHom (actualTranslatedMap (n := d) (m := m) φ x.val)
          (actualTranslatedMap_holomorphic hφ x.val) (actualTranslatedMap_zero (n := d) (m := m) φ x.val)
          (coordinateGerm k))) =
      germAt ((ψ x.val.val - c, x.val.val) : ComplexModel d × ComplexModel m)
        (graphRow ψ c g 0 (Fin.castAdd r k)) := by
    intro k
    have hcoord : HolAt (fun q : ComplexModel d × ComplexModel m => q.1 k)
        (ψ x.val.val - c, x.val.val) :=
      Eventually.of_forall fun _ =>
        ((EuclideanSpace.proj k : ComplexModel d →L[ℂ] ℂ).comp
          (ContinuousLinearMap.fst ℂ (ComplexModel d) (ComplexModel m))).differentiableAt
    have hφq : HolAt (fun q : ComplexModel d × ComplexModel m => ψ q.2 k)
        (ψ x.val.val - c, x.val.val) :=
      HolAt.comp (φ := Prod.snd) (y := (ψ x.val.val - c, x.val.val)) (hψhol k) continuous_snd
        fun _ => differentiableAt_snd
    have hrow : HolAt (fun q : ComplexModel d × ComplexModel m => q.1 k + c k - ψ q.2 k)
        (ψ x.val.val - c, x.val.val) :=
      (hcoord.add (holAt_const (c k) _)).sub hφq
    rw [graphRow_castAdd, germAt_of_holAt hrow, map_sub]
    unfold coordinateGerm jointNormalPullback ambientGermEquiv
    rw [compAlgHom_mk, compAlgHom_mk, HolGerm.comapEquiv_mk, HolGerm.comapEquiv_mk]
    refine (HolGerm.mk_sub _ _ _ _).symm.trans ?_
    apply HolGerm.mk_eq_mk_iff.mpr
    have hT := eventually_actualTranslatedMap_eq φ ψ hψ x.val
    have hT' : ∀ᶠ q in 𝓝 (0 : ComplexModel d × ComplexModel m),
        actualTranslatedMap (n := d) (m := m) φ x.val q.2 =
          ψ (x.val.val + q.2) - ψ x.val.val :=
      (continuous_snd.tendsto' (0 : ComplexModel d × ComplexModel m) 0 rfl).eventually hT
    filter_upwards [hT'] with q hq
    change ((splitModel d m).symm q) (Fin.castAdd m k) -
        actualTranslatedMap (n := d) (m := m) φ x.val
          (actualJointNormalProjection d m ((splitModel d m).symm q)) k =
      (ψ x.val.val - c + q.1) k + c k - ψ (x.val.val + q.2) k
    rw [splitModel_symm_castAdd, normalProjection_splitModel_symm, hq]
    simp only [PiLp.add_apply, PiLp.sub_apply]
    ring
  rw [hdef, relativeGraphIdeal, Ideal.map_sup, hgen,
    relativeGraphEquations_eq_span d m _ _ (actualTranslatedMap_zero (n := d) (m := m) φ x.val),
    Ideal.map_map, Ideal.map_span, Ideal.map_span, idealAt, range_addCases (d := d) (r := r),
    Ideal.span_union, sup_comm]
  congr 1
  · apply congrArg Ideal.span
    ext a
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, (heqn k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, heqn k⟩
  · apply congrArg Ideal.span
    ext a
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (hsrc j).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, hsrc j⟩

end Graph

/-! ### Off the graph the row generates the unit ideal -/

/-- If the base coordinate is not on the graph, a graph entry is a unit. -/
theorem idealAt_graphRow_eq_top_of_ne (ψ : ComplexModel m → ComplexModel d) (c : ComplexModel d)
    (g : Fin r → ComplexModel m → ℂ) (p : ComplexModel d) (z : ComplexModel m)
    (hψhol : ∀ k, HolAt (fun w => ψ w k) z) (k : Fin d) (hk : p k + c k - ψ z k ≠ 0) :
    idealAt d m (graphRow ψ c g) (p, z) = ⊤ := by
  have hcoord : HolAt (fun q : ComplexModel d × ComplexModel m => q.1 k) (p, z) :=
    Eventually.of_forall fun _ =>
      ((EuclideanSpace.proj k : ComplexModel d →L[ℂ] ℂ).comp
        (ContinuousLinearMap.fst ℂ (ComplexModel d) (ComplexModel m))).differentiableAt
  have hφq : HolAt (fun q : ComplexModel d × ComplexModel m => ψ q.2 k) (p, z) :=
    HolAt.comp (φ := Prod.snd) (y := (p, z)) (hψhol k) continuous_snd
      fun _ => differentiableAt_snd
  have hrow : HolAt (fun q : ComplexModel d × ComplexModel m => q.1 k + c k - ψ q.2 k) (p, z) :=
    (hcoord.add (holAt_const (c k) _)).sub hφq
  have hmem : germAt ((p, z) : ComplexModel d × ComplexModel m) (graphRow ψ c g 0 (Fin.castAdd r k)) ∈
      idealAt d m (graphRow ψ c g) (p, z) :=
    Ideal.subset_span ⟨Fin.castAdd r k, rfl⟩
  have hu : IsUnit (germAt ((p, z) : ComplexModel d × ComplexModel m)
      (graphRow ψ c g 0 (Fin.castAdd r k))) := by
    rw [graphRow_castAdd]
    exact isUnit_germAt hrow hk
  exact Ideal.eq_top_of_isUnit_mem _ hmem hu

/-- If the germs of `g` at `z` generate the unit ideal (`z` off the source carrier), so does the row. -/
theorem idealAt_graphRow_eq_top_of_span (ψ : ComplexModel m → ComplexModel d) (c : ComplexModel d)
    (g : Fin r → ComplexModel m → ℂ) (p : ComplexModel d) (z : ComplexModel m)
    (hg : ∀ j, HolAt (g j) z) (htop : Ideal.span (Set.range fun j => germAt z (g j)) = ⊤) :
    idealAt d m (graphRow ψ c g) (p, z) = ⊤ := by
  have hle : Ideal.map (HolGerm.comap (ContinuousLinearMap.snd ℂ (ComplexModel d) (ComplexModel m)))
      (Ideal.span (Set.range fun j => germAt z (g j))) ≤ idealAt d m (graphRow ψ c g) (p, z) := by
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    apply Ideal.subset_span
    refine ⟨Fin.natAdd d j, ?_⟩
    show germAt ((p, z) : ComplexModel d × ComplexModel m) (graphRow ψ c g 0 (Fin.natAdd d j)) =
      HolGerm.comap (ContinuousLinearMap.snd ℂ (ComplexModel d) (ComplexModel m)) (germAt z (g j))
    rw [graphRow_natAdd]
    exact (comap_snd_germAt p z (g j) (hg j)).symm
  rw [htop, Ideal.map_top] at hle
  exact top_le_iff.mp hle

/-! ### A row with unit ideal has the zero cokernel -/

local instance (d : ℕ) : Algebra ℂ (HolGerm (ComplexModel d)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel d)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

theorem range_mulVecLin_eq_top {A : Type*} [CommRing A] {b : ℕ} (M : Matrix (Fin 1) (Fin b) A)
    (h : Ideal.span (Set.range (M 0)) = ⊤) : LinearMap.range (Matrix.mulVecLin M) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v 0 ∈ Ideal.span (Set.range (M 0)) := by rw [h]; trivial
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hv
  refine ⟨c, ?_⟩
  funext i
  rw [Subsingleton.elim i 0]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  rw [← hc]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **Off the graph the cokernel is flat over every quotient of the base.** -/
theorem flat_of_idealAt_eq_top (ψ : ComplexModel m → ComplexModel d) (c : ComplexModel d)
    (g : Fin r → ComplexModel m → ℂ) (q : ComplexModel d × ComplexModel m)
    (htop : idealAt d m (graphRow ψ c g) q = ⊤) (I : Ideal (HolGerm (ComplexModel d))) :
    Module.Flat (HolGerm (ComplexModel d) ⧸ I)
      ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
        ((Fin 1 → HolGerm (ComplexModel d × ComplexModel m)) ⧸ LinearMap.range
          (Matrix.mulVecLin (fun i j => germAt q (graphRow ψ c g i j))))) := by
  have hr : LinearMap.range (Matrix.mulVecLin (fun i j => germAt q (graphRow ψ c g i j))) = ⊤ :=
    range_mulVecLin_eq_top _ htop
  have : Subsingleton ((Fin 1 → HolGerm (ComplexModel d × ComplexModel m)) ⧸ LinearMap.range
      (Matrix.mulVecLin (fun i j => germAt q (graphRow ψ c g i j)))) :=
    Submodule.Quotient.subsingleton_iff.mpr hr
  infer_instance

end

end Hironaka.Analytic.Unibranch.HironakaG10MwGraphRow
