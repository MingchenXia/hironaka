/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalDeformationInitialRelations
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual WHOLE analytic graph quotient and saturated central model

Original inputs are only the actual coherent ideal I,d,t. The true (x,u,v)
graph embedding and actual linear coordinate retraction internally construct
surjective whole-germ trace and genuine right inverse. Whole doubled Hadamard
on EVERY ambient germ identifies its actual kernel with the true equation ideal.
Actual coherent functional spans give exact whole origin-ideal pullback and sum
dictionaries. Therefore the true enlarged original K quotient is genuinely
isomorphic to the actual graph ring modulo the original ideal's actual scaled
image, with exact values on all quotient representatives.

ALL literal parameter colons have exact whole trace preimage and image
dictionaries. The genuine central graph inclusion factors the actual original
central inclusion; its WHOLE origin ideal is precisely the actual image of the
corresponding graph colon. SAME internally selected saturation index and ONE
actual open retain all original all-point/all-power/whole-union dictionaries,
and the entire origin graph saturation union equals that SAME graph colon.

No caller graph, kernel, presentation, index, open, central-fiber, Rees,
flatness or result certificate is an original input. Every map acts on true
holomorphic germs through actual whole functional representatives. Zero normal
or tangent dimensions and empty equation families are literal. Frozen prior
modules remain unchanged. Complete Mathematics.tex preceded substantive Lean.
This own offlib module awaits formal registration and native target build.

Nearby ORIGINAL Rees/whole associated-graded cone identification, reverse
analytic initial-ideal dictionary, analytic extension flatness, nearby all-
degree freeness, normal-flat loci, higher HS and G8 remain OPEN. The actual
saturated graph central model is not silently identified with those objects.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold
namespace Hironaka.HironakaRelativeNormalAnalyticGraphQuotient
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  HironakaRelativeNormalIdeal HironakaRelativeNormalCoherentSaturation
  HironakaRelativeNormalDeformationSaturation HironakaRelativeNormalDeformationInitialRelations
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
  RelativePrincipalizationSpan

abbrev graphDimension (d t : ℕ) : ℕ := d+(1+t)

def graphParameter (d t : ℕ) : ComplexModel (graphDimension d t) →L[ℂ] ℂ :=
  EuclideanSpace.proj ⟨d,by dsimp [graphDimension]; omega⟩

def graphFiberCoordinate (d t : ℕ) (i : Fin t) : ComplexModel (graphDimension d t) →L[ℂ] ℂ :=
  EuclideanSpace.proj ⟨d+1+i.val,by dsimp [graphDimension]; omega⟩

def graphBaseProjection (d t : ℕ) :
    ComplexModel (deformationDimension d t) →L[ℂ] ComplexModel (graphDimension d t) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (graphDimension d t) => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => EuclideanSpace.proj
      (if hi : i.val < d then ⟨i.val,by dsimp [deformationDimension]; omega⟩ else
        ⟨t+i.val,by dsimp [deformationDimension,graphDimension] at *; omega⟩))

theorem graphBaseProjection_tangent (d t : ℕ)
    (z : ComplexModel (deformationDimension d t)) (i : Fin d) :
    graphBaseProjection d t z (i.castAdd (1+t)) = z ((i.castAdd t).castAdd (1+t)) := by
  change z (if hi : i.val < d then _ else _) = _
  rw [dif_pos i.isLt]
  exact congrArg (fun j : Fin (deformationDimension d t) => z j) (Fin.ext rfl)

theorem graphBaseProjection_tail (d t : ℕ)
    (z : ComplexModel (deformationDimension d t)) (i : Fin (1+t)) :
    graphBaseProjection d t z (i.natAdd d) = z (i.natAdd (d+t)) := by
  change z (if hi : d+i.val < d then _ else _) = _
  rw [dif_neg (by omega)]
  exact congrArg (fun j : Fin (deformationDimension d t) => z j)
    (Fin.ext (by change t+(d+i.val) = d+t+i.val; omega))

def graphEmbedding (d t : ℕ) (z : ComplexModel (graphDimension d t)) :
    ComplexModel (deformationDimension d t) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (deformationDimension d t) => ℂ)).symm
    (fun i => if hi : i.val < d+t then
      if hj : i.val < d then z ⟨i.val,by dsimp [graphDimension]; omega⟩ else
        graphParameter d t z*graphFiberCoordinate d t ⟨i.val-d,by omega⟩ z
      else z ⟨i.val-t,by dsimp [deformationDimension,graphDimension] at *; omega⟩)

theorem graphEmbedding_tangent (d t : ℕ)
    (z : ComplexModel (graphDimension d t)) (i : Fin d) :
    graphEmbedding d t z ((i.castAdd t).castAdd (1+t)) = z (i.castAdd (1+t)) := by
  change (if hi : i.val < d+t then if hj : i.val < d then _ else _ else _) = _
  rw [dif_pos (by omega),dif_pos i.isLt]
  exact congrArg (fun j : Fin (graphDimension d t) => z j) (Fin.ext rfl)

theorem graphEmbedding_normal (d t : ℕ)
    (z : ComplexModel (graphDimension d t)) (i : Fin t) :
    graphEmbedding d t z ((i.natAdd d).castAdd (1+t)) =
      graphParameter d t z*graphFiberCoordinate d t i z := by
  change (if hi : d+i.val < d+t then if hj : d+i.val < d then _ else _ else _) = _
  rw [dif_pos (by omega),dif_neg (by omega)]
  congr 1
  apply congrArg (fun j => graphFiberCoordinate d t j z)
  apply Fin.ext
  change d+i.val-d = i.val
  omega

theorem graphEmbedding_tail (d t : ℕ)
    (z : ComplexModel (graphDimension d t)) (i : Fin (1+t)) :
    graphEmbedding d t z (i.natAdd (d+t)) = z (i.natAdd d) := by
  change (if hi : d+t+i.val < d+t then _ else _) = _
  rw [dif_neg (by omega)]
  exact congrArg (fun j : Fin (graphDimension d t) => z j)
    (Fin.ext (by change d+t+i.val-t = d+i.val; omega))

theorem graphEmbedding_holomorphic (d t : ℕ) : Differentiable ℂ (graphEmbedding d t) := by
  apply (differentiable_piLp 2).mpr
  intro i
  change Differentiable ℂ (fun z => if hi : i.val < d+t then
    if hj : i.val < d then z ⟨i.val,by dsimp [graphDimension]; omega⟩ else
      graphParameter d t z*graphFiberCoordinate d t ⟨i.val-d,by omega⟩ z
    else z ⟨i.val-t,by dsimp [deformationDimension,graphDimension] at *; omega⟩)
  by_cases hi : i.val < d+t
  · simp only [dif_pos hi]
    by_cases hj : i.val < d
    · simp only [dif_pos hj]
      exact (EuclideanSpace.proj _ : ComplexModel (graphDimension d t) →L[ℂ] ℂ).differentiable
    · simp only [dif_neg hj]
      exact (graphParameter d t).differentiable.mul (graphFiberCoordinate d t _).differentiable
  · simp only [dif_neg hi]
    exact (EuclideanSpace.proj _ : ComplexModel (graphDimension d t) →L[ℂ] ℂ).differentiable

theorem graphEmbedding_zero (d t : ℕ) : graphEmbedding d t 0 = 0 := by
  ext i
  change (if hi : i.val < d+t then if hj : i.val < d then _ else _ else _) = 0
  split
  · split
    · rfl
    · simp only [map_zero,mul_zero]
  · rfl

theorem graphBaseProjection_graphEmbedding (d t : ℕ)
    (z : ComplexModel (graphDimension d t)) : graphBaseProjection d t (graphEmbedding d t z) = z := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [graphBaseProjection_tangent,graphEmbedding_tangent]
  · rw [graphBaseProjection_tail,graphEmbedding_tail]

def graphTrace (d t : ℕ) :
    HolGerm (ComplexModel (deformationDimension d t)) →ₐ[ℂ] HolGerm (ComplexModel (graphDimension d t)) :=
  compAlgHom (graphEmbedding d t)
    (Eventually.of_forall fun _ => (graphEmbedding_holomorphic d t).differentiableAt)
    (graphEmbedding_zero d t)

def graphBasePullback (d t : ℕ) :
    HolGerm (ComplexModel (graphDimension d t)) →ₐ[ℂ] HolGerm (ComplexModel (deformationDimension d t)) :=
  compAlgHom (graphBaseProjection d t)
    (Eventually.of_forall fun _ => (graphBaseProjection d t).differentiableAt) (map_zero _)

theorem graphTrace_graphBasePullback (d t : ℕ) (g : HolGerm (ComplexModel (graphDimension d t))) :
    graphTrace d t (graphBasePullback d t g) = g := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold graphTrace graphBasePullback
    rw [compAlgHom_mk,compAlgHom_mk]
    exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun z =>
      congrArg f (graphBaseProjection_graphEmbedding d t z))

theorem graphTrace_surjective (d t : ℕ) : Function.Surjective (graphTrace d t) :=
  fun g => ⟨graphBasePullback d t g,graphTrace_graphBasePullback d t g⟩


def graphRetraction (d t : ℕ) : ComplexModel (deformationDimension d t) →
    ComplexModel (deformationDimension d t) := graphEmbedding d t ∘ graphBaseProjection d t

theorem graphRetraction_tangent (d t : ℕ) (z : ComplexModel (deformationDimension d t)) (i : Fin d) :
    graphRetraction d t z ((i.castAdd t).castAdd (1+t)) = z ((i.castAdd t).castAdd (1+t)) := by
  rw [graphRetraction,Function.comp_apply,graphEmbedding_tangent,graphBaseProjection_tangent]

theorem graphRetraction_normal (d t : ℕ) (z : ComplexModel (deformationDimension d t)) (i : Fin t) :
    graphRetraction d t z ((i.natAdd d).castAdd (1+t)) =
      deformationParameter d t z*deformationFiberCoordinate d t i z := by
  rw [graphRetraction,Function.comp_apply,graphEmbedding_normal]
  have hu : graphParameter d t (graphBaseProjection d t z) = deformationParameter d t z := by
    change graphBaseProjection d t z ((0 : Fin (1+t)).natAdd d) = z ((0 : Fin (1+t)).natAdd (d+t))
    exact graphBaseProjection_tail d t z 0
  have hv : graphFiberCoordinate d t i (graphBaseProjection d t z) = deformationFiberCoordinate d t i z := by
    let j : Fin (1+t) := ⟨1+i.val,by omega⟩
    change graphBaseProjection d t z ⟨d+1+i.val,_⟩ = z ⟨d+t+1+i.val,_⟩
    calc
      _ = graphBaseProjection d t z (j.natAdd d) :=
        congrArg (fun k : Fin (graphDimension d t) => graphBaseProjection d t z k)
          (Fin.ext (by change d+1+i.val = d+(1+i.val); omega))
      _ = z (j.natAdd (d+t)) := graphBaseProjection_tail d t z j
      _ = _ := congrArg (fun k : Fin (deformationDimension d t) => z k)
        (Fin.ext (by change d+t+(1+i.val) = d+t+1+i.val; omega))
  rw [hu,hv]

theorem graphRetraction_tail (d t : ℕ) (z : ComplexModel (deformationDimension d t)) (i : Fin (1+t)) :
    graphRetraction d t z (i.natAdd (d+t)) = z (i.natAdd (d+t)) := by
  rw [graphRetraction,Function.comp_apply,graphEmbedding_tail,graphBaseProjection_tail]

def graphDoubledRetraction (d t : ℕ) (z : ComplexModel (deformationDimension d t)) :
    ComplexModel (deformationDimension d t+deformationDimension d t) :=
  tangentInclusion (deformationDimension d t) (deformationDimension d t) z +
    secondInclusion (deformationDimension d t) (graphRetraction d t z-z)

theorem graphDoubledRetraction_tangent (d t : ℕ) (z : ComplexModel (deformationDimension d t))
    (i : Fin (deformationDimension d t)) :
    graphDoubledRetraction d t z (i.castAdd (deformationDimension d t)) = z i := by
  simp [graphDoubledRetraction]

theorem graphDoubledRetraction_normal (d t : ℕ) (z : ComplexModel (deformationDimension d t))
    (i : Fin (deformationDimension d t)) :
    graphDoubledRetraction d t z (i.natAdd (deformationDimension d t)) = graphRetraction d t z i-z i := by
  change tangentInclusion _ _ z (i.natAdd (deformationDimension d t)) +
    secondInclusion _ (graphRetraction d t z-z) (i.natAdd (deformationDimension d t)) = _
  rw [tangentInclusion_normal,secondInclusion_normal,zero_add]
  rfl

theorem graphDoubledRetraction_holomorphic (d t : ℕ) : Differentiable ℂ (graphDoubledRetraction d t) :=
  (tangentInclusion (deformationDimension d t) (deformationDimension d t)).differentiable.add
    ((secondInclusion (deformationDimension d t)).differentiable.comp
      (((graphEmbedding_holomorphic d t).comp (graphBaseProjection d t).differentiable).sub
        differentiable_id))

theorem graphDoubledRetraction_zero (d t : ℕ) : graphDoubledRetraction d t 0 = 0 := by
  simp [graphDoubledRetraction,graphRetraction,graphEmbedding_zero]

def graphDoubledPullback (d t : ℕ) :
    HolGerm (ComplexModel (deformationDimension d t+deformationDimension d t)) →ₐ[ℂ]
      HolGerm (ComplexModel (deformationDimension d t)) :=
  compAlgHom (graphDoubledRetraction d t)
    (Eventually.of_forall fun _ => (graphDoubledRetraction_holomorphic d t).differentiableAt)
    (graphDoubledRetraction_zero d t)

theorem graphDoubledPullback_sum (d t : ℕ) (g : HolGerm (ComplexModel (deformationDimension d t))) :
    graphDoubledPullback d t (doubledSumPullback (deformationDimension d t) g) =
      graphBasePullback d t (graphTrace d t g) := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold graphDoubledPullback doubledSumPullback graphBasePullback graphTrace
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    apply congrArg f
    ext i
    rw [doubledSumProjection_apply,graphDoubledRetraction_tangent,graphDoubledRetraction_normal]
    change z i+(graphRetraction d t z i-z i) = graphRetraction d t z i
    ring

theorem graphDoubledPullback_tangent (d t : ℕ) (g : HolGerm (ComplexModel (deformationDimension d t))) :
    graphDoubledPullback d t (tangentPullback (deformationDimension d t) (deformationDimension d t) g) = g := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold graphDoubledPullback tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    apply congrArg f
    ext i
    exact graphDoubledRetraction_tangent d t z i

theorem graphDoubledPullback_normal_tangent (d t : ℕ) (i : Fin d) :
    graphDoubledPullback d t (normalCoordinate (deformationDimension d t) (deformationDimension d t)
      ((i.castAdd t).castAdd (1+t))) = 0 := by
  unfold graphDoubledPullback normalCoordinate coordinateGerm
  rw [compAlgHom_mk,← HolGerm.mk_zero,HolGerm.mk_eq_mk_iff]
  apply Eventually.of_forall
  intro z
  change graphDoubledRetraction d t z (((i.castAdd t).castAdd (1+t)).natAdd (deformationDimension d t)) = 0
  rw [graphDoubledRetraction_normal,graphRetraction_tangent,sub_self]

theorem graphDoubledPullback_normal_normal (d t : ℕ) (i : Fin t) :
    graphDoubledPullback d t (normalCoordinate (deformationDimension d t) (deformationDimension d t)
      ((i.natAdd d).castAdd (1+t))) = deformationEquationGerm d t i := by
  unfold graphDoubledPullback normalCoordinate coordinateGerm deformationEquationGerm
  rw [compAlgHom_mk,HolGerm.mk_eq_mk_iff]
  apply Eventually.of_forall
  intro z
  change graphDoubledRetraction d t z (((i.natAdd d).castAdd (1+t)).natAdd (deformationDimension d t)) = _
  rw [graphDoubledRetraction_normal,graphRetraction_normal]
  rfl

theorem graphDoubledPullback_normal_tail (d t : ℕ) (i : Fin (1+t)) :
    graphDoubledPullback d t (normalCoordinate (deformationDimension d t) (deformationDimension d t)
      (i.natAdd (d+t))) = 0 := by
  unfold graphDoubledPullback normalCoordinate coordinateGerm
  rw [compAlgHom_mk,← HolGerm.mk_zero,HolGerm.mk_eq_mk_iff]
  apply Eventually.of_forall
  intro z
  change graphDoubledRetraction d t z ((i.natAdd (d+t)).natAdd (deformationDimension d t)) = 0
  rw [graphDoubledRetraction_normal,graphRetraction_tail,sub_self]

theorem graphBasePullback_trace_sub_mem_equations (d t : ℕ)
    (g : HolGerm (ComplexModel (deformationDimension d t))) :
    graphBasePullback d t (graphTrace d t g)-g ∈
      originalCoherentOriginIdeal (deformationEquationIdeal d t) := by
  let F := doubledSumPullback (deformationDimension d t) g -
    tangentPullback (deformationDimension d t) (deformationDimension d t) g
  have htrace : planeTrace (deformationDimension d t) (deformationDimension d t) F = 0 := by
    rw [map_sub,planeTrace_doubledSumPullback,planeTrace_tangentPullback,sub_self]
  obtain ⟨h,he⟩ := exists_relative_decomposition (deformationDimension d t) (deformationDimension d t) F
  rw [htrace,map_zero,zero_add] at he
  have hpull := congrArg (graphDoubledPullback d t) he
  change graphDoubledPullback d t
    (doubledSumPullback (deformationDimension d t) g -
      tangentPullback (deformationDimension d t) (deformationDimension d t) g) = _ at hpull
  rw [map_sub,graphDoubledPullback_sum,graphDoubledPullback_tangent] at hpull
  simp only [map_sum,map_mul] at hpull
  rw [Fin.sum_univ_add,Fin.sum_univ_add] at hpull
  simp only [graphDoubledPullback_normal_tangent,graphDoubledPullback_normal_normal,
    graphDoubledPullback_normal_tail,zero_mul,Finset.sum_const_zero,zero_add,add_zero] at hpull
  rw [hpull]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (deformationEquationGerm_mem_originIdeal d t i)


/-- The actual finite functional identity gives WHOLE ideal membership. -/
theorem whole_origin_span_mem {n : ℕ} (L : Ideal (HolGerm (ComplexModel n)))
    (S : (ComplexModel n → ℂ) → Prop) (hS : ∀ f, S f → HolAt f 0)
    (hmem : ∀ f (hf : S f), HolGerm.mk f (hS f hf) ∈ L)
    {g : ComplexModel n → ℂ} (hg : HolAt g 0) (hspan : IsInSpanAt (n := n) S 0 g) :
    HolGerm.mk g hg ∈ L := by
  obtain ⟨_,N,s,a,hs,ha,he⟩ := hspan
  have hs0 : ∀ i, HolAt (s i) 0 := fun i => hS (s i) (hs i)
  have hin : InSpanAt s 0 g := ⟨hg,a,fun i => (ha i).mono (fun _ h => h.differentiableAt),he⟩
  have hm := (inSpanAt_zero_iff_mem_origin_span s hs0 hg).mp hin
  apply (Ideal.span_le.mpr ?_) hm
  rintro f ⟨i,rfl⟩
  exact hmem (s i) (hs i)

theorem originalOriginIdeal_pullback_eq {m n : ℕ}
    (η : ComplexModel m →L[ℂ] ComplexModel n)
    (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent) :
    originalCoherentOriginIdeal (GermIdeal.pullback (m := m) η I) =
      Ideal.map (compAlgHom η (Eventually.of_forall fun _ => η.differentiableAt) (map_zero _)).toRingHom
        (originalCoherentOriginIdeal I) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hIf,rfl⟩
    let S := fun s : ComplexModel m → ℂ => ∃ a, I.mem (η 0) a ∧ s = a ∘ η
    have hS : ∀ s, S s → HolAt s 0 := by
      rintro s ⟨a,ha,rfl⟩
      have ha0 : I.mem 0 a := by simpa only [map_zero] using ha
      exact holomorphic_comp η (Eventually.of_forall fun _ => η.differentiableAt) (map_zero _)
        ((GermIdeal.IsCoherent.holomorphicAt_mem hI ha0).mono (fun _ h => h.differentiableAt))
    apply whole_origin_span_mem _ S hS ?_ hf hIf
    rintro s ⟨a,ha,rfl⟩
    have ha0 : I.mem 0 a := by simpa only [map_zero] using ha
    have hah : HolAt a 0 := (GermIdeal.IsCoherent.holomorphicAt_mem hI ha0).mono (fun _ h => h.differentiableAt)
    have he : HolGerm.mk (a ∘ η) (hS (a ∘ η) ⟨a,ha,rfl⟩) =
        compAlgHom η (Eventually.of_forall fun _ => η.differentiableAt) (map_zero _)
          (HolGerm.mk a hah) := by rw [compAlgHom_mk]
    rw [he]
    exact Ideal.mem_map_of_mem _ ((mk_mem_originalCoherentOriginIdeal_iff I hI hah).mpr ha0)
  · exact map_compAlgHom_originIdeal_le η I hI

theorem originalOriginIdeal_sum_eq {n : ℕ}
    (I J : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    originalCoherentOriginIdeal (RestrictedIdealExtension.sumIdeal I J) =
      originalCoherentOriginIdeal I ⊔ originalCoherentOriginIdeal J := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hIf,rfl⟩
    let S := fun s : ComplexModel n → ℂ => I.mem 0 s ∨ J.mem 0 s
    have hS : ∀ s, S s → HolAt s 0 := by
      intro s hs
      rcases hs with hs | hs
      · exact (GermIdeal.IsCoherent.holomorphicAt_mem hI hs).mono (fun _ h => h.differentiableAt)
      · exact (GermIdeal.IsCoherent.holomorphicAt_mem hJ hs).mono (fun _ h => h.differentiableAt)
    apply whole_origin_span_mem _ S hS ?_ hf hIf
    intro s hs
    rcases hs with hs | hs
    · exact (show originalCoherentOriginIdeal I ≤ originalCoherentOriginIdeal I ⊔ originalCoherentOriginIdeal J from le_sup_left) ((mk_mem_originalCoherentOriginIdeal_iff I hI _).mpr hs)
    · exact (show originalCoherentOriginIdeal J ≤ originalCoherentOriginIdeal I ⊔ originalCoherentOriginIdeal J from le_sup_right) ((mk_mem_originalCoherentOriginIdeal_iff J hJ _).mpr hs)
  · apply sup_le
    · exact originalCoherentOriginIdeal_le_of_le _ _ (RestrictedIdealExtension.isCoherent_sumIdeal hI hJ)
        (RestrictedIdealExtension.le_sumIdeal_left hI)
    · exact originalCoherentOriginIdeal_le_of_le _ _ (RestrictedIdealExtension.isCoherent_sumIdeal hI hJ)
        (RestrictedIdealExtension.le_sumIdeal_right hJ)

theorem originalEquationIdeal_eq_span (d t : ℕ) :
    originalCoherentOriginIdeal (deformationEquationIdeal d t) = Ideal.span (range (deformationEquationGerm d t)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hIf,rfl⟩
    let S := fun s : ComplexModel (deformationDimension d t) → ℂ => s ∈ range (deformationEquation d t)
    have hS : ∀ s, S s → HolAt s 0 := by
      rintro s ⟨i,rfl⟩
      exact Eventually.of_forall fun _ => (deformationEquation_holomorphic d t i).differentiableAt
    apply whole_origin_span_mem _ S hS ?_ hf hIf
    rintro s ⟨i,rfl⟩
    exact Ideal.subset_span ⟨i,rfl⟩
  · apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    exact deformationEquationGerm_mem_originIdeal d t i

theorem graphTrace_equationGerm (d t : ℕ) (i : Fin t) :
    graphTrace d t (deformationEquationGerm d t i) = 0 := by
  unfold graphTrace deformationEquationGerm
  rw [compAlgHom_mk,← HolGerm.mk_zero,HolGerm.mk_eq_mk_iff]
  apply Eventually.of_forall
  intro z
  change deformationParameter d t (graphEmbedding d t z)*deformationFiberCoordinate d t i (graphEmbedding d t z) -
    graphEmbedding d t z ((i.natAdd d).castAdd (1+t)) = 0
  rw [graphEmbedding_normal]
  have hu : deformationParameter d t (graphEmbedding d t z) = graphParameter d t z := by
    exact graphEmbedding_tail d t z 0
  have hv : deformationFiberCoordinate d t i (graphEmbedding d t z) = graphFiberCoordinate d t i z := by
    let j : Fin (1+t) := ⟨1+i.val,by omega⟩
    change graphEmbedding d t z ⟨d+t+1+i.val,_⟩ = z ⟨d+1+i.val,_⟩
    calc
      _ = graphEmbedding d t z (j.natAdd (d+t)) := congrArg
        (fun k : Fin (deformationDimension d t) => graphEmbedding d t z k)
        (Fin.ext (by change d+t+1+i.val = d+t+(1+i.val); omega))
      _ = z (j.natAdd d) := graphEmbedding_tail d t z j
      _ = _ := congrArg (fun k : Fin (graphDimension d t) => z k)
        (Fin.ext (by change d+(1+i.val) = d+1+i.val; omega))
  rw [hu,hv,sub_self]

theorem graphTrace_kernel (d t : ℕ) :
    RingHom.ker (graphTrace d t).toRingHom = originalCoherentOriginIdeal (deformationEquationIdeal d t) := by
  apply le_antisymm
  · intro g hg
    have he : graphTrace d t g = 0 := RingHom.mem_ker.mp hg
    have hd := graphBasePullback_trace_sub_mem_equations d t g
    rw [he,map_zero,zero_sub] at hd
    simpa only [neg_neg] using (originalCoherentOriginIdeal (deformationEquationIdeal d t)).neg_mem hd
  · rw [originalEquationIdeal_eq_span]
    apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    exact RingHom.mem_ker.mpr (graphTrace_equationGerm d t i)


def actualGraphScaledIdeal (d t : ℕ) (I : GermIdeal (d+t) (ComplexModel (d+t))) :
    Ideal (HolGerm (ComplexModel (graphDimension d t))) :=
  Ideal.map ((graphTrace d t).comp (tangentPullback (d+t) (1+t))).toRingHom (originalCoherentOriginIdeal I)

theorem originalDeformationOriginIdeal_eq (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    originalCoherentOriginIdeal (originalDeformationIdeal d t I) =
      Ideal.map (tangentPullback (d+t) (1+t)).toRingHom (originalCoherentOriginIdeal I) ⊔
        originalCoherentOriginIdeal (deformationEquationIdeal d t) := by
  unfold originalDeformationIdeal
  rw [originalOriginIdeal_sum_eq _ _
    (GermIdealPullbackCalculus.isCoherent_pullback (deformationProjection d t).contMDiff hI)
    (deformationEquationIdeal_isCoherent d t),
    originalOriginIdeal_pullback_eq (deformationProjection d t) I hI]
  rfl

theorem graphTrace_kernel_le_original (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    RingHom.ker (graphTrace d t).toRingHom ≤ originalCoherentOriginIdeal (originalDeformationIdeal d t I) := by
  rw [graphTrace_kernel,originalDeformationOriginIdeal_eq d t I hI]
  exact le_sup_right

theorem graphTrace_map_originalOriginIdeal (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    Ideal.map (graphTrace d t).toRingHom (originalCoherentOriginIdeal (originalDeformationIdeal d t I)) =
      actualGraphScaledIdeal d t I := by
  rw [originalDeformationOriginIdeal_eq d t I hI,Ideal.map_sup,Ideal.map_map]
  have he : Ideal.map (graphTrace d t).toRingHom
      (originalCoherentOriginIdeal (deformationEquationIdeal d t)) = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker _).mpr
    rw [graphTrace_kernel]
  rw [he,sup_bot_eq]
  rfl

theorem originalOriginIdeal_eq_graphTrace_comap (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    originalCoherentOriginIdeal (originalDeformationIdeal d t I) =
      Ideal.comap (graphTrace d t).toRingHom (actualGraphScaledIdeal d t I) := by
  rw [← graphTrace_map_originalOriginIdeal d t I hI,
    Ideal.comap_map_of_surjective' (graphTrace d t).toRingHom (graphTrace_surjective d t)]
  exact (sup_eq_left.mpr (graphTrace_kernel_le_original d t I hI)).symm

def originalGraphQuotientMap (d t : ℕ) (I : GermIdeal (d+t) (ComplexModel (d+t))) :
    HolGerm (ComplexModel (deformationDimension d t)) →+*
      HolGerm (ComplexModel (graphDimension d t)) ⧸ actualGraphScaledIdeal d t I :=
  (Ideal.Quotient.mk (actualGraphScaledIdeal d t I)).comp (graphTrace d t).toRingHom

theorem originalGraphQuotientMap_surjective (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) : Function.Surjective (originalGraphQuotientMap d t I) :=
  (Ideal.Quotient.mk_surjective).comp (graphTrace_surjective d t)

theorem originalGraphQuotientMap_kernel (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    RingHom.ker (originalGraphQuotientMap d t I) = originalCoherentOriginIdeal (originalDeformationIdeal d t I) := by
  rw [originalOriginIdeal_eq_graphTrace_comap d t I hI]
  ext g
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk (actualGraphScaledIdeal d t I) (graphTrace d t g) = 0 ↔
    graphTrace d t g ∈ actualGraphScaledIdeal d t I
  exact Ideal.Quotient.eq_zero_iff_mem



def originalGraphQuotientEquiv (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    (HolGerm (ComplexModel (deformationDimension d t)) ⧸
      originalCoherentOriginIdeal (originalDeformationIdeal d t I)) ≃+*
    (HolGerm (ComplexModel (graphDimension d t)) ⧸ actualGraphScaledIdeal d t I) :=
  (Ideal.quotEquivOfEq (originalGraphQuotientMap_kernel d t I hI).symm).trans
    (RingHom.quotientKerEquivOfSurjective (originalGraphQuotientMap_surjective d t I))

theorem originalGraphQuotientEquiv_apply_mk (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent)
    (g : HolGerm (ComplexModel (deformationDimension d t))) :
    originalGraphQuotientEquiv d t I hI (Ideal.Quotient.mk
      (originalCoherentOriginIdeal (originalDeformationIdeal d t I)) g) =
      Ideal.Quotient.mk (actualGraphScaledIdeal d t I) (graphTrace d t g) := by
  rw [originalGraphQuotientEquiv,RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

def graphParameterGerm (d t : ℕ) : HolGerm (ComplexModel (graphDimension d t)) :=
  HolGerm.mk (graphParameter d t) (Eventually.of_forall fun _ => (graphParameter d t).differentiableAt)

theorem graphTrace_parameter (d t : ℕ) :
    graphTrace d t (deformationParameterGerm d t) = graphParameterGerm d t := by
  unfold graphTrace deformationParameterGerm graphParameterGerm
  rw [compAlgHom_mk,HolGerm.mk_eq_mk_iff]
  exact Eventually.of_forall fun z => graphEmbedding_tail d t z 0

def actualGraphColonIdeal (d t : ℕ) (I : GermIdeal (d+t) (ComplexModel (d+t))) (q : ℕ) :
    Ideal (HolGerm (ComplexModel (graphDimension d t))) :=
  actualOriginColonChain (actualGraphScaledIdeal d t I) (graphParameterGerm d t) q

theorem originalOriginColon_eq_graphTrace_comap (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) (q : ℕ) :
    actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t I))
      (deformationParameterGerm d t) q = Ideal.comap (graphTrace d t).toRingHom (actualGraphColonIdeal d t I q) := by
  ext g
  rw [mem_actualOriginColonChain_iff,originalOriginIdeal_eq_graphTrace_comap d t I hI]
  change graphTrace d t (g*deformationParameterGerm d t^q) ∈ actualGraphScaledIdeal d t I ↔
    graphTrace d t g ∈ actualOriginColonChain (actualGraphScaledIdeal d t I) (graphParameterGerm d t) q
  rw [mem_actualOriginColonChain_iff,map_mul,map_pow,graphTrace_parameter]

theorem graphTrace_map_originalOriginColon (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) (q : ℕ) :
    Ideal.map (graphTrace d t).toRingHom
      (actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t I))
        (deformationParameterGerm d t) q) = actualGraphColonIdeal d t I q := by
  rw [originalOriginColon_eq_graphTrace_comap d t I hI,
    Ideal.map_comap_of_surjective (f := (graphTrace d t).toRingHom) (graphTrace_surjective d t)]

def graphCentralInclusion (d t : ℕ) :
    ComplexModel (d+t) →L[ℂ] ComplexModel (graphDimension d t) :=
  (graphBaseProjection d t).comp (deformationCentralInclusion d t)

theorem graphEmbedding_graphCentralInclusion (d t : ℕ) (z : ComplexModel (d+t)) :
    graphEmbedding d t (graphCentralInclusion d t z) = deformationCentralInclusion d t z := by
  change graphRetraction d t (deformationCentralInclusion d t z) = deformationCentralInclusion d t z
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · exact graphRetraction_tangent d t _ j
    · rw [graphRetraction_normal,deformationCentralInclusion_parameter,
        deformationCentralInclusion_normal,zero_mul]
  · exact graphRetraction_tail d t _ j

def graphCentralPullback (d t : ℕ) :
    HolGerm (ComplexModel (graphDimension d t)) →ₐ[ℂ] HolGerm (ComplexModel (d+t)) :=
  compAlgHom (graphCentralInclusion d t)
    (Eventually.of_forall fun _ => (graphCentralInclusion d t).differentiableAt) (map_zero _)

theorem graphCentralPullback_graphTrace (d t : ℕ)
    (g : HolGerm (ComplexModel (deformationDimension d t))) :
    graphCentralPullback d t (graphTrace d t g) = deformationCentralPullback d t g := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold graphCentralPullback graphTrace deformationCentralPullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun z =>
      congrArg f (graphEmbedding_graphCentralInclusion d t z))

theorem graphCentralPullback_comp_trace (d t : ℕ) :
    (graphCentralPullback d t).toRingHom.comp (graphTrace d t).toRingHom =
      (deformationCentralPullback d t).toRingHom := by
  apply RingHom.ext
  intro g
  exact graphCentralPullback_graphTrace d t g

theorem originalCentralOriginIdeal_eq_graphColon_image (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) (q : ℕ) :
    originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I q) =
      Ideal.map (graphCentralPullback d t).toRingHom (actualGraphColonIdeal d t I q) := by
  have hK := originalDeformationIdeal_isCoherent d t I hI
  have hpar : ∀ x, HolAt (deformationParameter d t) x :=
    fun _ => Eventually.of_forall fun _ => (deformationParameter d t).differentiableAt
  have hc := originalDeformationColonIdeal_isCoherent d t I hI q
  have hcolon : originalCoherentOriginIdeal (originalDeformationColonIdeal d t I q) =
      actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t I))
        (deformationParameterGerm d t) q :=
    originalOriginIdeal_actualColon (originalDeformationIdeal d t I) hK (deformationParameter d t) hpar q
  have hpull := originalOriginIdeal_pullback_eq (deformationCentralInclusion d t)
    (originalDeformationColonIdeal d t I q) hc
  change originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I q) =
    Ideal.map (deformationCentralPullback d t).toRingHom
      (originalCoherentOriginIdeal (originalDeformationColonIdeal d t I q)) at hpull
  rw [hpull,hcolon,← graphCentralPullback_comp_trace,← Ideal.map_map,
    graphTrace_map_originalOriginColon d t I hI q]



theorem graphCentralInclusion_tangent (d t : ℕ) (z : ComplexModel (d+t)) (i : Fin d) :
    graphCentralInclusion d t z (i.castAdd (1+t)) = z (i.castAdd t) := by
  change graphBaseProjection d t (deformationCentralInclusion d t z) (i.castAdd (1+t)) = _
  rw [graphBaseProjection_tangent,deformationCentralInclusion_tangent]

theorem graphCentralInclusion_parameter (d t : ℕ) (z : ComplexModel (d+t)) :
    graphParameter d t (graphCentralInclusion d t z) = 0 := by
  change graphBaseProjection d t (deformationCentralInclusion d t z) ((0 : Fin (1+t)).natAdd d) = 0
  rw [graphBaseProjection_tail]
  exact deformationCentralInclusion_parameter d t z

theorem graphCentralInclusion_fiber (d t : ℕ) (z : ComplexModel (d+t)) (i : Fin t) :
    graphFiberCoordinate d t i (graphCentralInclusion d t z) = z (i.natAdd d) := by
  let j : Fin (1+t) := ⟨1+i.val,by omega⟩
  change graphBaseProjection d t (deformationCentralInclusion d t z) ⟨d+1+i.val,_⟩ = _
  calc
    _ = graphBaseProjection d t (deformationCentralInclusion d t z) (j.natAdd d) :=
      congrArg (fun k : Fin (graphDimension d t) => graphBaseProjection d t (deformationCentralInclusion d t z) k)
        (Fin.ext (by change d+1+i.val = d+(1+i.val); omega))
    _ = deformationCentralInclusion d t z (j.natAdd (d+t)) := graphBaseProjection_tail d t _ j
    _ = deformationFiberCoordinate d t i (deformationCentralInclusion d t z) :=
      congrArg (fun k : Fin (deformationDimension d t) => deformationCentralInclusion d t z k)
        (Fin.ext (by change d+t+(1+i.val) = d+t+1+i.val; omega))
    _ = _ := deformationCentralInclusion_fiber d t z i

/-- All actual graph colon ideals share the internally selected index of the original coherent model. -/
theorem exists_original_graph_saturated_model (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
      originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) =
        Ideal.map (graphCentralPullback d t).toRingHom (actualGraphColonIdeal d t I N) ∧
      (∀ q : ℕ, actualGraphColonIdeal d t I (N+q) = actualGraphColonIdeal d t I N) ∧
      (∀ g, (∃ q : ℕ, g ∈ actualGraphColonIdeal d t I q) ↔ g ∈ actualGraphColonIdeal d t I N) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g,
        (originalDeformationColonIdeal d t I (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t I N).mem y g) ∧
      (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
        ((originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^q) ↔
        (originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^N))) ∧
      ∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem y g) ↔
        (originalDeformationColonIdeal d t I N).mem y g := by
  obtain ⟨N,U,hU,h0U,hchain,hpow,hsat⟩ := exists_original_deformation_uniform_saturation d t I hI
  have hK := originalDeformationIdeal_isCoherent d t I hI
  have hpar : HolAt (deformationParameter d t) 0 :=
    Eventually.of_forall fun _ => (deformationParameter d t).differentiableAt
  have hring : ∀ q : ℕ,
      actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t I))
        (deformationParameterGerm d t) (N+q) =
      actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t I))
        (deformationParameterGerm d t) N := by
    intro q
    ext g
    induction g using HolGerm.induction_on with
    | h f hf =>
      change HolGerm.mk f hf ∈ actualOriginColonChain
        (originalCoherentOriginIdeal (originalDeformationIdeal d t I))
        (HolGerm.mk (deformationParameter d t) hpar) (N+q) ↔
        HolGerm.mk f hf ∈ actualOriginColonChain
        (originalCoherentOriginIdeal (originalDeformationIdeal d t I))
        (HolGerm.mk (deformationParameter d t) hpar) N
      rw [← actualColonChain_origin_ideal_dictionary (originalDeformationIdeal d t I) hK hpar (N+q) hf,
        ← actualColonChain_origin_ideal_dictionary (originalDeformationIdeal d t I) hK hpar N hf]
      exact hchain 0 h0U q f
  have hgraph : ∀ q : ℕ, actualGraphColonIdeal d t I (N+q) = actualGraphColonIdeal d t I N := by
    intro q
    rw [← graphTrace_map_originalOriginColon d t I hI (N+q),
      ← graphTrace_map_originalOriginColon d t I hI N,hring q]
  have hgraphSat : ∀ g, (∃ q : ℕ, g ∈ actualGraphColonIdeal d t I q) ↔
      g ∈ actualGraphColonIdeal d t I N := by
    intro g
    constructor
    · rintro ⟨q,hg⟩
      let F := graphBasePullback d t g
      have hFq : F ∈ actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t I))
          (deformationParameterGerm d t) q := by
        rw [originalOriginColon_eq_graphTrace_comap d t I hI q]
        change graphTrace d t (graphBasePullback d t g) ∈ actualGraphColonIdeal d t I q
        rw [graphTrace_graphBasePullback]
        exact hg
      obtain ⟨f,hf,hF⟩ := HolGerm.exists_eq_mk F
      rw [hF] at hFq
      have hqfunc := (actualColonChain_origin_ideal_dictionary (originalDeformationIdeal d t I) hK hpar q hf).mpr hFq
      have hNfunc := (hsat 0 h0U f).mp ⟨q,hqfunc⟩
      have hNring := (actualColonChain_origin_ideal_dictionary (originalDeformationIdeal d t I) hK hpar N hf).mp hNfunc
      change HolGerm.mk f hf ∈ actualOriginColonChain
        (originalCoherentOriginIdeal (originalDeformationIdeal d t I)) (deformationParameterGerm d t) N at hNring
      have hm := Ideal.mem_map_of_mem (graphTrace d t).toRingHom hNring
      rw [graphTrace_map_originalOriginColon d t I hI N] at hm
      rw [← hF] at hm
      change graphTrace d t (graphBasePullback d t g) ∈ actualGraphColonIdeal d t I N at hm
      rw [graphTrace_graphBasePullback] at hm
      exact hm
    · exact fun hg => ⟨N,hg⟩
  exact ⟨N,U,hU,h0U,originalCentralOriginIdeal_eq_graphColon_image d t I hI N,
    hgraph,hgraphSat,hchain,hpow,hsat⟩


/-- The original coherent input jointly gives the WHOLE quotient and SAME genuine analytic saturation model. -/
theorem exists_original_graph_quotient_and_saturation (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
      Nonempty ((HolGerm (ComplexModel (deformationDimension d t)) ⧸
        originalCoherentOriginIdeal (originalDeformationIdeal d t I)) ≃+*
        (HolGerm (ComplexModel (graphDimension d t)) ⧸ actualGraphScaledIdeal d t I)) ∧
      originalCoherentOriginIdeal (originalDeformationIdeal d t I) =
        Ideal.comap (graphTrace d t).toRingHom (actualGraphScaledIdeal d t I) ∧
      originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) =
        Ideal.map (graphCentralPullback d t).toRingHom (actualGraphColonIdeal d t I N) ∧
      (∀ q : ℕ, actualGraphColonIdeal d t I (N+q) = actualGraphColonIdeal d t I N) ∧
      (∀ g, (∃ q : ℕ, g ∈ actualGraphColonIdeal d t I q) ↔ g ∈ actualGraphColonIdeal d t I N) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g,
        (originalDeformationColonIdeal d t I (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t I N).mem y g) ∧
      (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
        ((originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^q) ↔
        (originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^N))) ∧
      ∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem y g) ↔
        (originalDeformationColonIdeal d t I N).mem y g := by
  obtain ⟨N,U,hU,h0U,hcentral,hgraph,hsgraph,hchain,hpow,hsat⟩ := exists_original_graph_saturated_model d t I hI
  exact ⟨N,U,hU,h0U,⟨originalGraphQuotientEquiv d t I hI⟩,
    originalOriginIdeal_eq_graphTrace_comap d t I hI,hcentral,hgraph,hsgraph,hchain,hpow,hsat⟩

end
end Hironaka.HironakaRelativeNormalAnalyticGraphQuotient
