/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaRelativeNormalCoherentSaturation
import Hironaka.Resolution.HironakaRelativeNormalIdeal
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Data.Fintype.EquivFin

/-! # ORIGINAL coherent ideal internally produces its ACTUAL deformation saturation

The literal enlarged ambient coordinates (x,y,u,v) internally produce the
actual original projection, actual parameter and fiber coordinates, and the
entire equations u*v_i-y_i. Their finite whole equation ideal plus the actual
ORIGINAL coherent ideal pullback is internally coherent. Actual Oka coherence
at EVERY Euclidean point internally produces each literal repeated parameter
colon as a genuine coherent GermIdeal. Genuine reindexing of the actual finite
Oka generators gives the full manifold finite-span dictionary.

ONLY the ORIGINAL coherent GermIdeal supplies ONE internally selected N and
ONE actual origin neighborhood U. At EVERY point of SAME U, ALL subsequent
parameter colons agree, ALL literal u^q memberships stabilize for q>=N, and
the ENTIRE increasing saturation union equals the ACTUAL coherent Nth colon.
The actual continuous linear central inclusion (x,v)->(x,0,0,v) supplies its
ENTIRE coordinate dictionary and the exact vanishing of every true equation.
The literal central pullback of each actual colon is internally coherent.

No caller equation ideal, colon generators, exponent, neighborhood, stability,
saturation or result certificate enters the original consumer. Zero tangent
or normal dimensions, empty equation families and arbitrary original coherent
ideals are literal. The dimension abbreviation is only coordinate notation.
No map from all origin germs into arbitrary nearby stalks is invented.

This ACTUAL analytic equation saturation and its ACTUAL central restriction
are NOT identified here with the nearby ENTIRE original Rees algebra or whole
associated graded cone. Those dictionaries remain independent obligations.
Nearby ALL-degree freeness, analytic normal-flat neighborhoods, higher HS
and general G8 remain OPEN. No whole normal-cone or flattening claim is made.
Blueprint: hironaka-relative-normal-deformation-saturation-extension.tex.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold
namespace Hironaka.HironakaRelativeNormalDeformationSaturation
noncomputable section
open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf OkaIdealOperations
  HironakaRelativeNormalIdeal HironakaRelativeNormalCoherentSaturation

/-- Literal enlarged ambient dimension for the ORIGINAL equation model. -/
abbrev deformationDimension (d t : ℕ) : ℕ := (d+t)+(1+t)

/-- The actual enlarged-to-original first-coordinate projection. -/
def deformationProjection (d t : ℕ) :
    ComplexModel (deformationDimension d t) →L[ℂ] ComplexModel (d+t) :=
  tangentProjection (d+t) (1+t)

/-- The actual scalar deformation parameter, not a supplied representative. -/
def deformationParameter (d t : ℕ) :
    ComplexModel (deformationDimension d t) →L[ℂ] ℂ :=
  EuclideanSpace.proj ⟨d+t,by dsimp [deformationDimension]; omega⟩

/-- The actual added fiber coordinate. -/
def deformationFiberCoordinate (d t : ℕ) (i : Fin t) :
    ComplexModel (deformationDimension d t) →L[ℂ] ℂ :=
  EuclideanSpace.proj ⟨d+t+1+i.val,by dsimp [deformationDimension]; omega⟩

/-- The literal entire equation u*v_i - ORIGINAL y_i. -/
def deformationEquation (d t : ℕ) (i : Fin t)
    (z : ComplexModel (deformationDimension d t)) : ℂ :=
  deformationParameter d t z * deformationFiberCoordinate d t i z -
    z ((i.natAdd d).castAdd (1+t))

theorem deformationParameter_holomorphic (d t : ℕ) :
    Differentiable ℂ (deformationParameter d t) :=
  (deformationParameter d t).differentiable

theorem deformationEquation_holomorphic (d t : ℕ) (i : Fin t) :
    Differentiable ℂ (deformationEquation d t i) :=
  ((deformationParameter d t).differentiable.mul
    (deformationFiberCoordinate d t i).differentiable).sub
      (EuclideanSpace.proj ((i.natAdd d).castAdd (1+t)) :
        ComplexModel (deformationDimension d t) →L[ℂ] ℂ).differentiable

/-- The ACTUAL finite whole equation ideal at every enlarged ambient point. -/
def deformationEquationIdeal (d t : ℕ) :
    GermIdeal (deformationDimension d t) (ComplexModel (deformationDimension d t)) where
  mem y := IsInSpanAt (n := deformationDimension d t) (· ∈ range (deformationEquation d t)) y

theorem deformationEquationIdeal_isCoherent (d t : ℕ) :
    (deformationEquationIdeal d t).IsCoherent := by
  intro y
  refine ⟨univ,isOpen_univ,mem_univ y,t,deformationEquation d t,?_,?_⟩
  · exact fun i => mdifferentiableOn_iff_differentiableOn.mpr
      (deformationEquation_holomorphic d t i).differentiableOn
  · exact fun _ _ _ => Iff.rfl

/-- The ORIGINAL ideal's actual pullback plus the actual deformation equations. -/
def originalDeformationIdeal (d t : ℕ) (I : GermIdeal (d+t) (ComplexModel (d+t))) :
    GermIdeal (deformationDimension d t) (ComplexModel (deformationDimension d t)) :=
  RestrictedIdealExtension.sumIdeal
    (GermIdeal.pullback (m := deformationDimension d t) (deformationProjection d t) I)
    (deformationEquationIdeal d t)

theorem originalDeformationIdeal_isCoherent (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    (originalDeformationIdeal d t I).IsCoherent :=
  RestrictedIdealExtension.isCoherent_sumIdeal
    (GermIdealPullbackCalculus.isCoherent_pullback (deformationProjection d t).contMDiff hI)
    (deformationEquationIdeal_isCoherent d t)

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- True original coherent finite spans at an ARBITRARY actual Euclidean point. -/
theorem germIdeal_finitely_generated_at {n : ℕ}
    (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent) (x : ComplexModel n) :
    IdealFGAt I.mem x := by
  obtain ⟨U,hU,hx,N,s,hs,hsI⟩ := hI x
  refine ⟨U,hU,hx,Fin N,inferInstance,s,
    fun i => mdifferentiableOn_iff_differentiableOn.mp (hs i),?_⟩
  intro y hy g
  rw [hsI y hy g,CoherentIdealColon.isInSpanAt_range_iff]
  constructor
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h => h.differentiableAt),a,
      fun i => (ha i).mono (fun _ h => h.differentiableAt),he⟩
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h => h.mdifferentiableAt),a,
      fun i => (ha i).mono (fun _ h => h.mdifferentiableAt),he⟩

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Actual finite analytic presentations at ALL points give genuine sheaf coherence. -/
theorem finitely_generated_at_isCoherent {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (hI : ∀ x, IdealFGAt I.mem x) : I.IsCoherent := by
  classical
  intro x
  obtain ⟨U,hU,hx,μ,hμ,s,hs,hsI⟩ := hI x
  let := hμ
  let e := Fintype.equivFin μ
  refine ⟨U,hU,hx,Fintype.card μ,fun i => s (e.symm i),
    fun i => mdifferentiableOn_iff_differentiableOn.mpr (hs (e.symm i)),?_⟩
  intro y hy g
  rw [hsI y hy g,CoherentIdealColon.isInSpanAt_range_iff]
  constructor
  · rintro ⟨hg,a,ha,he⟩
    refine ⟨hg.mono (fun _ h => h.mdifferentiableAt),fun i => a (e.symm i),
      fun i => (ha (e.symm i)).mono (fun _ h => h.mdifferentiableAt),?_⟩
    filter_upwards [he] with z hz
    rw [hz]
    exact (e.symm.sum_comp (fun i => a i z*s i z)).symm
  · rintro ⟨hg,a,ha,he⟩
    refine ⟨hg.mono (fun _ h => h.differentiableAt),fun i => a (e i),
      fun i => (ha (e i)).mono (fun _ h => h.differentiableAt),?_⟩
    filter_upwards [he] with z hz
    rw [hz]
    simpa only [Equiv.symm_apply_apply] using
      (e.sum_comp (fun i => a i z*s (e.symm i) z)).symm

/-- Genuine GermIdeal whose entire predicate is the literal recursive functional colon. -/
def actualColonGermIdeal {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (h : ComplexModel n → ℂ) (q : ℕ) : GermIdeal n (ComplexModel n) where
  mem := actualColonChain I.mem h q

theorem actualColonGermIdeal_isCoherent {n : ℕ}
    (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent)
    (h : ComplexModel n → ℂ) (hh : ∀ x, HolAt h x) (q : ℕ) :
    (actualColonGermIdeal I h q).IsCoherent := by
  apply finitely_generated_at_isCoherent
  intro x
  change IdealFGAt (actualColonChain I.mem h q) x
  induction q with
  | zero => exact germIdeal_finitely_generated_at I hI x
  | succ q ih => exact ih.colon (OkaCoherence.okaProperty_euclidean n) (hh x)

/-- The ORIGINAL equation model's actual qth parameter colon. -/
def originalDeformationColonIdeal (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (q : ℕ) :
    GermIdeal (deformationDimension d t) (ComplexModel (deformationDimension d t)) :=
  actualColonGermIdeal (originalDeformationIdeal d t I) (deformationParameter d t) q

theorem originalDeformationColonIdeal_isCoherent (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) (q : ℕ) :
    (originalDeformationColonIdeal d t I q).IsCoherent :=
  actualColonGermIdeal_isCoherent _ (originalDeformationIdeal_isCoherent d t I hI) _
    (fun _ => Eventually.of_forall fun _ => (deformationParameter d t).differentiableAt) q

/-- ONLY the ORIGINAL coherent ideal internally produces one U/N and ALL powers of actual u. -/
theorem exists_original_deformation_uniform_saturation (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g,
        (originalDeformationColonIdeal d t I (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t I N).mem y g) ∧
      (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
        ((originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^q) ↔
          (originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^N))) ∧
      ∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem y g) ↔
        (originalDeformationColonIdeal d t I N).mem y g := by
  obtain ⟨N,U,hU,h0U,_,he,hp,hs⟩ := exists_original_germIdeal_exact_uniform_saturation
    (originalDeformationIdeal d t I) (originalDeformationIdeal_isCoherent d t I hI)
    (Eventually.of_forall fun _ => (deformationParameter d t).differentiableAt)
  exact ⟨N,U,hU,h0U,he,hp,hs⟩

/-- Literal effective central inclusion (x,v) ↦ (x,0,0,v). -/
def deformationCentralInclusion (d t : ℕ) :
    ComplexModel (d+t) →L[ℂ] ComplexModel (deformationDimension d t) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (deformationDimension d t) => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k : Fin (deformationDimension d t) =>
      if hk : k.val < d then
        (EuclideanSpace.proj ⟨k.val,by omega⟩ : ComplexModel (d+t) →L[ℂ] ℂ)
      else if hk : d+t+1 ≤ k.val then
        (EuclideanSpace.proj ⟨k.val-(1+t),by
          have hklt : k.val < (d+t)+(1+t) := k.isLt
          omega⟩ :
          ComplexModel (d+t) →L[ℂ] ℂ)
      else 0)

theorem deformationCentralInclusion_tangent (d t : ℕ) (z : ComplexModel (d+t)) (i : Fin d) :
    deformationCentralInclusion d t z ((i.castAdd t).castAdd (1+t)) = z (i.castAdd t) := by
  change (if hk : i.val < d then
    (EuclideanSpace.proj ⟨i.val,by omega⟩ : ComplexModel (d+t) →L[ℂ] ℂ)
    else if hk : d+t+1 ≤ i.val then
      (EuclideanSpace.proj ⟨i.val-(1+t),by omega⟩ : ComplexModel (d+t) →L[ℂ] ℂ)
    else 0) z = _
  rw [dif_pos i.isLt]
  rfl

theorem deformationCentralInclusion_normal (d t : ℕ) (z : ComplexModel (d+t)) (i : Fin t) :
    deformationCentralInclusion d t z ((i.natAdd d).castAdd (1+t)) = 0 := by
  change (if hk : d+i.val < d then
    (EuclideanSpace.proj ⟨d+i.val,by omega⟩ : ComplexModel (d+t) →L[ℂ] ℂ)
    else if hk : d+t+1 ≤ d+i.val then
      (EuclideanSpace.proj ⟨d+i.val-(1+t),by omega⟩ : ComplexModel (d+t) →L[ℂ] ℂ)
    else 0) z = _
  rw [dif_neg (by omega),dif_neg (by omega)]
  rfl

theorem deformationCentralInclusion_parameter (d t : ℕ) (z : ComplexModel (d+t)) :
    deformationParameter d t (deformationCentralInclusion d t z) = 0 := by
  change (if hk : d+t < d then
    (EuclideanSpace.proj ⟨d+t,by omega⟩ : ComplexModel (d+t) →L[ℂ] ℂ)
    else if hk : d+t+1 ≤ d+t then
      (EuclideanSpace.proj ⟨d+t-(1+t),by omega⟩ : ComplexModel (d+t) →L[ℂ] ℂ)
    else 0) z = _
  rw [dif_neg (by omega),dif_neg (by omega)]
  rfl

theorem deformationCentralInclusion_fiber (d t : ℕ) (z : ComplexModel (d+t)) (i : Fin t) :
    deformationFiberCoordinate d t i (deformationCentralInclusion d t z) = z (i.natAdd d) := by
  change (if hk : d+t+1+i.val < d then
    (EuclideanSpace.proj ⟨d+t+1+i.val,by omega⟩ : ComplexModel (d+t) →L[ℂ] ℂ)
    else if hk : d+t+1 ≤ d+t+1+i.val then
      (EuclideanSpace.proj ⟨d+t+1+i.val-(1+t),by omega⟩ : ComplexModel (d+t) →L[ℂ] ℂ)
    else 0) z = _
  rw [dif_neg (by omega),dif_pos (by omega)]
  change z ⟨d+t+1+i.val-(1+t),_⟩ = z (i.natAdd d)
  apply congrArg (fun j : Fin (d+t) => z j)
  apply Fin.ext
  change d+t+1+i.val-(1+t) = d+i.val
  omega

theorem deformationEquation_central (d t : ℕ) (z : ComplexModel (d+t)) (i : Fin t) :
    deformationEquation d t i (deformationCentralInclusion d t z) = 0 := by
  simp only [deformationEquation,deformationCentralInclusion_parameter,
    deformationCentralInclusion_normal,zero_mul,sub_zero]

/-- ACTUAL coherent central restriction; its normal-cone identification is still separate. -/
def originalDeformationCentralIdeal (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (N : ℕ) : GermIdeal (d+t) (ComplexModel (d+t)) :=
  GermIdeal.pullback (m := d+t) (deformationCentralInclusion d t)
    (originalDeformationColonIdeal d t I N)

theorem originalDeformationCentralIdeal_isCoherent (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) (N : ℕ) :
    (originalDeformationCentralIdeal d t I N).IsCoherent :=
  GermIdealPullbackCalculus.isCoherent_pullback (deformationCentralInclusion d t).contMDiff
    (originalDeformationColonIdeal_isCoherent d t I hI N)

/-- ONLY original coherent data jointly produce SAME actual equation saturation and central model. -/
theorem exists_original_deformation_saturated_model (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
      (originalDeformationColonIdeal d t I N).IsCoherent ∧
      (originalDeformationCentralIdeal d t I N).IsCoherent ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g,
        (originalDeformationColonIdeal d t I (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t I N).mem y g) ∧
      (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
        ((originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^q) ↔
          (originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^N))) ∧
      ∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem y g) ↔
        (originalDeformationColonIdeal d t I N).mem y g := by
  obtain ⟨N,U,hU,h0U,he,hp,hs⟩ := exists_original_deformation_uniform_saturation d t I hI
  exact ⟨N,U,hU,h0U,originalDeformationColonIdeal_isCoherent d t I hI N,
    originalDeformationCentralIdeal_isCoherent d t I hI N,he,hp,hs⟩

end
end Hironaka.HironakaRelativeNormalDeformationSaturation
