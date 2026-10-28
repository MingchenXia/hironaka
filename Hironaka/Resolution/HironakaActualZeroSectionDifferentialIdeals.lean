/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualZeroCoordinateContactSeed
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.Analytic.FiniteGermIdealPullbackGenerators

/-!
# Whole actual derivative ideals through a closed zero section

The literal closed zero section restricts the ENTIRE along-carrier derivative
ideal to the intrinsic derivative ideal, for every original coherent ideal.
Actual finite generators, tangent chain rule and vanishing normal coordinates
prove both whole-span inclusions; coherence gives every iterated derivative.
No smooth cylinder projection or incoming differential/value/history equality
is used. Canonical closed-contact invariant-tail and history descent remain open.
Blueprint: `hironaka-actual-zero-section-differential-ideals-extension.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualZeroSectionDifferentialIdeals
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualZeroCoordinateContactSeed HironakaActualIntrinsicStableAmbientIso
  DerivativeIdeal DerivativeIdealAlong DerivativeIdealAlongCoherent
  BlowupFlatCoordinates GiraudAlong RelativePrincipalizationSpan
  GermIdealPullbackCalculus InvertibleIdealQuotient
variable {n : ℕ}

private def identityFlat {k : ℕ} (x : ComplexModel k) :
    LocalHolomorphicEquivAt (n := k) (chartAt (ComplexModel k) x x) where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := id
  invFun := id
  toFun_holomorphic := differentiableOn_id
  invFun_holomorphic := differentiableOn_id
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

private theorem zeroPlane_eq_coordinatePlane (n : ℕ) :
    zeroPlane n = complexCoordinatePlane (n+1) n := by
  ext z
  constructor
  · intro hz
    have hq : actualJointNormalProjection n 1 z=0 := hz
    have he : tangentInclusion n 1 (tangentProjection n 1 z)=z := by
      simpa only [HironakaActualIntrinsicStableAmbientIso.join,hq,map_zero,add_zero]
        using join_projections (n := n) (m := 1) z
    rw [←he]
    exact tangentInclusion_mem_plane n 1 _
  · intro hz
    ext i
    exact hz (i.natAdd n) (by simp)

private theorem identityFlat_domain {k : ℕ} (x : ComplexModel k) :
    flatDomain (identityFlat x)=univ := by
  simp [flatDomain,identityFlat]

private theorem identityFlat_partial {k : ℕ} (x y : ComplexModel k)
    (g : ComplexModel k → ℂ) (hg : HolomorphicAt k g y) (j : Fin k) :
    flatPartial (identityFlat x) j g y=
      chartDeriv (complexChartAt x) (EuclideanSpace.single j 1) g y := by
  have hy : y∈flatDomain (identityFlat x) := by rw [identityFlat_domain];exact mem_univ y
  have h := flatPartial_eq hy hg j
  change flatPartial (identityFlat x) j g y=fderiv ℂ g y (EuclideanSpace.single j 1) at h
  exact h

private theorem section_single (n : ℕ) (i : Fin n) :
    tangentInclusion n 1 (EuclideanSpace.single i 1)=EuclideanSpace.single (i.castAdd 1) 1 := by
  ext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp
  · have hne : k.natAdd n≠i.castAdd 1 := by
      intro he
      have h := congrArg Fin.val he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at h
      omega
    simp [hne]

/-- The genuine differential chain rule uses this same closed zero section. -/
theorem tangent_derivative_zero_section (x : ComplexModel n) (g : ComplexModel (n+1) → ℂ)
    (hg : HolomorphicAt (n+1) g (tangentInclusion n 1 x)) (i : Fin n) :
    chartDeriv (complexChartAt x) (EuclideanSpace.single i 1) (g ∘ tangentInclusion n 1)
      =ᶠ[𝓝 x] (chartDeriv (complexChartAt (tangentInclusion n 1 x))
        (EuclideanSpace.single (i.castAdd 1) 1) g) ∘ tangentInclusion n 1 := by
  filter_upwards [(tangentInclusion n 1).continuous.continuousAt.eventually hg] with y hy
  have hd : DifferentiableAt ℂ g (tangentInclusion n 1 y) :=
    mdifferentiableAt_iff_differentiableAt.mp hy
  have hc := (hd.hasFDerivAt.comp y (tangentInclusion n 1).hasFDerivAt).fderiv
  change fderiv ℂ (g ∘ tangentInclusion n 1) y (EuclideanSpace.single i 1)=
    fderiv ℂ g (tangentInclusion n 1 y) (EuclideanSpace.single (i.castAdd 1) 1)
  rw [hc]
  change fderiv ℂ g (tangentInclusion n 1 y)
    (tangentInclusion n 1 (EuclideanSpace.single i 1))=_
  rw [section_single]

private theorem pullback_span_iff {ι : Type*} (J : GermIdeal (n+1) (ComplexModel (n+1)))
    (x : ComplexModel n) (G : ι → ComplexModel (n+1) → ℂ)
    (hG : ∀ i,HolomorphicAt (n+1) (G i) (tangentInclusion n 1 x))
    (hgen : ∀ a,J.mem (tangentInclusion n 1 x) a ↔
      IsInSpanAt (n := n+1) (·∈range G) (tangentInclusion n 1 x) a)
    (F : ComplexModel n → ℂ) :
    (GermIdeal.pullback (m := n) (tangentInclusion n 1) J).mem x F ↔
      IsInSpanAt (n := n) (·∈range fun i => G i ∘ tangentInclusion n 1) x F := by
  constructor
  · intro h
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp h)
    rintro _ ⟨a,ha,rfl⟩
    apply IsInSpanAt.mono ?_ (isInSpanAt_comp (tangentInclusion n 1).contMDiff ((hgen a).mp ha))
    rintro _ ⟨b,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · intro h
    apply GermIdeal.mem_pullback_iff.mpr
    apply IsInSpanAt.mono ?_ h
    rintro _ ⟨i,rfl⟩
    exact ⟨G i,(hgen _).mpr (isInSpanAt_self ⟨i,rfl⟩ (hG i)),rfl⟩

private theorem flat_tangent_section (x : ComplexModel n) (g : ComplexModel (n+1) → ℂ)
    (hg : HolomorphicAt (n+1) g (tangentInclusion n 1 x)) (i : Fin n) :
    (flatPartial (identityFlat (tangentInclusion n 1 x)) (i.castAdd 1) g) ∘ tangentInclusion n 1
      =ᶠ[𝓝 x] chartDeriv (complexChartAt x) (EuclideanSpace.single i 1) (g ∘ tangentInclusion n 1) := by
  filter_upwards [(tangentInclusion n 1).continuous.continuousAt.eventually hg.eventually,
    tangent_derivative_zero_section x g hg i] with y hy he
  change flatPartial (identityFlat (tangentInclusion n 1 x)) (i.castAdd 1) g
    (tangentInclusion n 1 y)=_
  rw [identityFlat_partial _ _ g hy]
  exact he.symm

private theorem flat_normal_section (x : ComplexModel n) (i : Fin (n+1)) (hi : n ≤ i.val) :
    flatCoord (identityFlat (tangentInclusion n 1 x)) i ∘ tangentInclusion n 1=fun _ => 0 := by
  funext y
  change tangentInclusion n 1 y i=0
  exact tangentInclusion_mem_plane n 1 y i hi

private theorem zero_mem_span {k : ℕ} (x : ComplexModel k) (S : (ComplexModel k → ℂ) → Prop) :
    IsInSpanAt (n := k) S x (fun _ => 0) := by
  refine ⟨holomorphicAt_const 0,0,Fin.elim0,Fin.elim0,(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),?_⟩
  exact Eventually.of_forall fun _ => by simp

private theorem restricted_derivative_family_iff {r : ℕ} (x : ComplexModel n)
    (G : Fin r → ComplexModel (n+1) → ℂ)
    (hG : ∀ i,HolomorphicAt (n+1) (G i) (tangentInclusion n 1 x)) (F : ComplexModel n → ℂ) :
    IsInSpanAt (n := n)
        (·∈range fun c => derivFamilyAlong (identityFlat (tangentInclusion n 1 x)) n G c ∘ tangentInclusion n 1) x F ↔
      IsInSpanAt (n := n) (·∈range (DerivativeIdeal.derivFamily (complexChartAt (n := n) x) (fun i => G i ∘ tangentInclusion n 1))) x F := by
  have hcomp (i : Fin r) : HolomorphicAt n (G i ∘ tangentInclusion n 1) x :=
    (hG i).comp_contMDiff (Eventually.of_forall fun _ => (tangentInclusion n 1).contMDiff.contMDiffAt)
  constructor
  · intro h
    refine IsInSpanAt.trans ?_ h
    rintro _ ⟨c,rfl⟩
    rcases c with i | j | ⟨i,j⟩
    · exact isInSpanAt_self ⟨.inl i,rfl⟩ (hcomp i)
    · have he : derivFamilyAlong (identityFlat (tangentInclusion n 1 x)) n G (.inr (.inl j)) ∘
          tangentInclusion n 1=fun _ => 0 := by
        by_cases hj : n ≤ j.val
        · simpa only [derivFamilyAlong,if_pos hj] using flat_normal_section x j hj
        · simp only [derivFamilyAlong,if_neg hj,Function.comp_def]
      change IsInSpanAt (n := n)
        (·∈range (DerivativeIdeal.derivFamily (complexChartAt (n := n) x)
          (fun i => G i ∘ tangentInclusion n 1))) x
        (derivFamilyAlong (identityFlat (tangentInclusion n 1 x)) n G (.inr (.inl j)) ∘ tangentInclusion n 1)
      rw [he]
      exact zero_mem_span _ _
    · by_cases hj : j.val<n
      · let k : Fin n := ⟨j.val,hj⟩
        have he : k.castAdd 1=j := Fin.ext rfl
        have hmem : IsInSpanAt (n := n)
            (·∈range (DerivativeIdeal.derivFamily (complexChartAt (n := n) x) (fun i => G i ∘ tangentInclusion n 1))) x
            (chartDeriv (complexChartAt x) (EuclideanSpace.single k 1) (G i ∘ tangentInclusion n 1)) :=
          isInSpanAt_self ⟨.inr (i,k),rfl⟩ (holomorphicAt_chartDeriv (mem_complexChartAt_source x) (hcomp i))
        simp only [derivFamilyAlong,if_pos hj]
        rw [←he]
        exact isInSpanAt_congr hmem (flat_tangent_section x (G i) (hG i) k).symm
      · simp only [derivFamilyAlong,if_neg hj,Function.comp_def]
        exact zero_mem_span _ _
  · intro h
    refine IsInSpanAt.trans ?_ h
    rintro _ ⟨c,rfl⟩
    rcases c with i | ⟨i,j⟩
    · exact isInSpanAt_self ⟨.inl i,rfl⟩ (hcomp i)
    · have he : derivFamilyAlong (identityFlat (tangentInclusion n 1 x)) n G (.inr (.inr (i,j.castAdd 1))) ∘
          tangentInclusion n 1=flatPartial (identityFlat (tangentInclusion n 1 x)) (j.castAdd 1) (G i) ∘
            tangentInclusion n 1 := by simp only [derivFamilyAlong,Fin.val_castAdd,if_pos j.isLt]
      have hhol : HolomorphicAt n
          (flatPartial (identityFlat (tangentInclusion n 1 x)) (j.castAdd 1) (G i) ∘ tangentInclusion n 1) x :=
        (holomorphicAt_flatPartial (j.castAdd 1)
          (by rw [identityFlat_domain];exact mem_univ _) (hG i)).comp_contMDiff
            (Eventually.of_forall fun _ => (tangentInclusion n 1).contMDiff.contMDiffAt)
      have hmem : IsInSpanAt (n := n)
          (·∈range fun c => derivFamilyAlong (identityFlat (tangentInclusion n 1 x)) n G c ∘ tangentInclusion n 1) x
          (flatPartial (identityFlat (tangentInclusion n 1 x)) (j.castAdd 1) (G i) ∘ tangentInclusion n 1) :=
        isInSpanAt_self ⟨.inr (.inr (i,j.castAdd 1)),he⟩ hhol
      exact isInSpanAt_congr hmem (flat_tangent_section x (G i) (hG i) j)

/-- The ENTIRE derivative ideal along the closed zero plane restricts to the
genuine intrinsic derivative of the SAME original ideal pullback. -/
theorem zero_section_derivIdealAlong (J : GermIdeal (n+1) (ComplexModel (n+1)))
    (hJ : J.IsCoherent) :
    GermIdeal.pullback (m := n) (tangentInclusion n 1) (derivIdealAlong (zeroPlane n) J)=
      derivIdeal (GermIdeal.pullback (m := n) (tangentInclusion n 1) J) := by
  apply GermIdeal.ext
  funext x F
  apply propext
  obtain ⟨U,hU,hxU,r,G,hG,hgen⟩ := hJ (tangentInclusion n 1 x)
  have hGh : ∀ i z,z∈U → HolomorphicAt (n+1) (G i) z :=
    fun i z hz => holomorphicAt_of_mdifferentiableOn hU (hG i) hz
  let Φ := identityFlat (tangentInclusion n 1 x)
  have hΦsrc : Φ.source⊆(chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x)).target := by
    simp [Φ,identityFlat]
  have hflat : ∀ {z : ComplexModel (n+1)},
      z∈(chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x)).source →
      chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x) z∈Φ.source →
      (z∈zeroPlane n ↔ Φ.toFun (chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x) z)∈
        complexCoordinatePlane (n+1) n) := by
    intro z _ _
    change z∈zeroPlane n ↔ z∈complexCoordinatePlane (n+1) n
    rw [zeroPlane_eq_coordinatePlane]
  have hUΦ : U⊆flatDomain Φ := by
    rw [show flatDomain Φ=univ from identityFlat_domain _]
    exact subset_univ _
  have hD : ∀ a,(derivIdealAlong (zeroPlane n) J).mem (tangentInclusion n 1 x) a ↔
      IsInSpanAt (n := n+1) (·∈range (derivFamilyAlong Φ n G)) (tangentInclusion n 1 x) a :=
    fun a => derivIdealAlong_mem_iff_of_generators hΦsrc hflat hU hUΦ hG hgen hxU a
  have hxΦ : tangentInclusion n 1 x∈flatDomain Φ := hUΦ hxU
  have hDf : ∀ c,HolomorphicAt (n+1) (derivFamilyAlong Φ n G c) (tangentInclusion n 1 x) := by
    rintro (i | j | ⟨i,j⟩)
    · exact hGh i _ hxU
    · by_cases hj : n ≤ j.val
      · simpa only [derivFamilyAlong,if_pos hj] using holomorphicAt_flatCoord Φ j hxΦ
      · simpa only [derivFamilyAlong,if_neg hj] using
          (holomorphicAt_const (n := n+1) (x := tangentInclusion n 1 x) (0 : ℂ))
    · by_cases hj : j.val<n
      · simpa only [derivFamilyAlong,if_pos hj] using holomorphicAt_flatPartial j hxΦ (hGh i _ hxU)
      · simpa only [derivFamilyAlong,if_neg hj] using
          (holomorphicAt_const (n := n+1) (x := tangentInclusion n 1 x) (0 : ℂ))
  let V := (tangentInclusion n 1) ⁻¹' U
  have hV : IsOpen V := hU.preimage (tangentInclusion n 1).continuous
  have hxV : x∈V := hxU
  have hfat : ∀ {y : ComplexModel n},∀ᶠ z in 𝓝 y,
      ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+1)) ∞ (tangentInclusion n 1) z :=
    fun {_} => Eventually.of_forall fun _ => (tangentInclusion n 1).contMDiff.contMDiffAt
  have hGV : ∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ)
      (G i ∘ tangentInclusion n 1) V := by
    intro i y hy
    exact ((hGh i _ hy).comp_contMDiff hfat).self_of_nhds.mdifferentiableWithinAt
  have hgenV : ∀ y∈V,∀ a,
      (GermIdeal.pullback (m := n) (tangentInclusion n 1) J).mem y a ↔
        IsInSpanAt (n := n) (·∈range fun i => G i ∘ tangentInclusion n 1) y a := by
    intro y hy a
    exact FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation hfat J G
      (fun i => hGh i _ hy) (hgen _ hy) a
  have hBase := derivIdeal_mem_iff_of_generators hV hGV hgenV (complexChartAt x)
    (by simp [complexChartAt]) hxV F
  exact (pullback_span_iff (derivIdealAlong (zeroPlane n) J) x (derivFamilyAlong Φ n G) hDf hD F).trans
    ((restricted_derivative_family_iff x G (fun i => hGh i _ hxU) F).trans hBase.symm)

private theorem zeroPlane_closed_submanifold (n : ℕ) : IsClosedSubmanifold (n+1) (zeroPlane n) := by
  have he : {z : ComplexModel (n+1) | HironakaActualGraphFunctionalIdeal.graphFunction (zeroFunction n) 0 z=0}=
      zeroPlane n := by
    ext z
    constructor
    · intro hz
      change actualJointNormalProjection n 1 z=0
      ext i
      have hi : i=0 := Fin.eq_zero i
      subst i
      simpa [HironakaActualGraphFunctionalIdeal.graphFunction,zeroFunction] using hz
    · intro hz
      have h := congrArg (fun v : ComplexModel 1 => v 0) hz
      simpa [HironakaActualGraphFunctionalIdeal.graphFunction,zeroFunction] using h
  refine ⟨isClosed_eq (actualJointNormalProjection n 1).continuous continuous_const,?_⟩
  intro z hz
  refine ⟨n,?_⟩
  have hz0 : HironakaActualGraphFunctionalIdeal.graphFunction (zeroFunction n) 0 z=0 := by
    rw [←he] at hz
    exact hz
  have h := HironakaActualGraphContactCoefficient.graphNormalContact_regularAtDim
    (zeroFunction n) ⊤ contDiff_const.contDiffOn (0 : Fin 1) (z := z) (by trivial) hz0
  simpa only [Opens.coe_top,preimage_univ,inter_univ,he,Nat.add_sub_cancel] using h

/-- ALL actual iterated derivative ideals retain this same original J and
literal closed zero section; no differential comparison is an input. -/
theorem zero_section_iterDerivIdealAlong (J : GermIdeal (n+1) (ComplexModel (n+1)))
    (hJ : J.IsCoherent) (q : ℕ) :
    GermIdeal.pullback (m := n) (tangentInclusion n 1) (iterDerivIdealAlong (zeroPlane n) J q)=
      iterDerivIdeal (GermIdeal.pullback (m := n) (tangentInclusion n 1) J) q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [iterDerivIdealAlong,zero_section_derivIdealAlong _
      (isCoherent_iterDerivIdealAlong hJ (zeroPlane_closed_submanifold n) q),ih,iterDerivIdeal_succ]

end
end Hironaka.HironakaActualZeroSectionDifferentialIdeals
