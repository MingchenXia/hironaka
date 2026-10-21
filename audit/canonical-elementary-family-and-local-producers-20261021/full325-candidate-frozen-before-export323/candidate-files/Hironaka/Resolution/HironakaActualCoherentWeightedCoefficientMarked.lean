/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualWeightedCoefficientCompression
import Hironaka.Invariant.OrderMultiplicativity
import Hironaka.MarkedIdeal.MarkedIdeals

/-!
# Genuine coherent common-mark coefficient ideals on the real domain

Literal finite actual functions define a coherent ideal on their true open
subtype. At every actual point the positive common-mark cosupport is exactly
the individual weighted coefficient cosupport intersection. The original
analytic ideal internally supplies the coefficient family and the real domain.
Zero ideals are allowed: nonzero invariant-domain membership and persistent
HS tracking are not asserted. No global coefficient extension is made.
Blueprint: `hironaka-actual-coherent-weighted-coefficient-marked-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualCoherentWeightedCoefficientMarked
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HolGerm RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealOrder
  IdealOrderArithmetic OrderTaylor OrderMultiplicativity
  HironakaActualWeightedCoefficientCompression HironakaActualAnalyticVertexCoefficientData
  HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings

section Functions
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {ι : Type*}

/-- The whole genuine local span of the literal original functions. -/
def finiteFunctionIdeal (c : ι → M → ℂ) : GermIdeal n M where
  mem x g := IsInSpanAt (n := n) (· ∈ range c) x g

omit [IsComplexManifold n M] in
/-- Actual finite holomorphic generators prove global coherence, on precisely their actual manifold. -/
theorem isCoherent_finiteFunctionIdeal [Fintype ι] (c : ι → M → ℂ)
    (hc : ∀ i, MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i)) :
    (finiteFunctionIdeal (n := n) c).IsCoherent := by
  let e := Fintype.equivFin ι
  let f : Fin (Fintype.card ι) → M → ℂ := fun j => c (e.symm j)
  have hr : range f=range c := by
    ext g
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨e.symm j,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨e i,by simp [f]⟩
  intro x
  refine ⟨univ,isOpen_univ,mem_univ x,Fintype.card ι,f,
    fun j => (hc (e.symm j)).mdifferentiableOn,?_⟩
  intro y _ g
  change IsInSpanAt (n := n) (· ∈ range c) y g ↔ IsInSpanAt (n := n) (· ∈ range f) y g
  rw [hr]

/-- The entire ideal cosupport is detected on every original function, at every actual point. -/
theorem mem_cosupport_finiteFunctionIdeal_iff (c : ι → M → ℂ) (x : M) (q : ℕ)
    (hc : ∀ i, HolomorphicAt n (c i) x) :
    x ∈ cosupport n univ (finiteFunctionIdeal c) q ↔
      ∀ i, VanishesToOrderOn n univ x q (c i) := by
  constructor
  · intro hx i
    exact hx.2 _ (isInSpanAt_self (S := (· ∈ range c)) ⟨i,rfl⟩ (hc i))
  · intro h
    refine ⟨mem_univ x,fun g hg => ?_⟩
    exact IsInSpanAt.vanishesToOrderOn hg (by rintro f ⟨i,rfl⟩; exact h i)

omit [IsComplexManifold n M] in
private theorem vanishes_pow (x : M) (g : M → ℂ) (w : ℕ)
    (hg : VanishesToOrderOn n univ x w g) :
    ∀ r, VanishesToOrderOn n univ x (w*r) (fun y => g y^r)
  | 0 => by simpa only [Nat.mul_zero,pow_zero] using
      (vanishesToOrderOn_zero (n := n) (N := univ) (x := x) (holomorphicAt_const 1))
  | r+1 => by simpa only [Nat.mul_succ,pow_succ] using (vanishes_pow x g w hg r).mul hg

private theorem vanishes_pow_iff (x : M) (g : M → ℂ) (hg : HolomorphicAt n g x)
    (w r : ℕ) (hr : 0 < r) :
    VanishesToOrderOn n univ x (w*r) (fun y => g y^r) ↔ VanishesToOrderOn n univ x w g := by
  constructor
  · intro h
    have hm := mem_idealPow_of_vanishesToOrderOn_univ h
    rw [Nat.mul_comm w r] at hm
    have hroot := mem_idealPow_of_pow_mem hg (show 1 ≤ r by omega) hm
    exact ⟨g,hroot,Eventually.of_forall fun _ _ => rfl⟩
  · exact fun h => vanishes_pow x g w h r

/-- Whole actual common-mark ideal of literal powered coefficient functions. -/
def weightedFunctionIdeal [Fintype ι] (w : ι → ℕ) (c : ι → M → ℂ) : GermIdeal n M :=
  finiteFunctionIdeal (fun i y => c i y^(weightedCommonMark w/w i))

omit [IsComplexManifold n M] in
/-- Global coherence of the genuine common-mark ideal follows from its actual powered functions. -/
theorem isCoherent_weightedFunctionIdeal [Fintype ι] (w : ι → ℕ) (c : ι → M → ℂ)
    (hc : ∀ i, MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i)) :
    (weightedFunctionIdeal (n := n) w c).IsCoherent :=
  isCoherent_finiteFunctionIdeal (n := n) _ (fun i => (hc i).pow _)

/-- Equality of the ENTIRE all-point cosupport, retaining each positive original coefficient weight. -/
theorem cosupport_weightedFunctionIdeal [Fintype ι] (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (c : ι → M → ℂ) (hc : ∀ i, MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i)) :
    cosupport n univ (weightedFunctionIdeal w c) (weightedCommonMark w)=
      ⋂ i, cosupport n univ (finiteFunctionIdeal (fun _ : Unit => c i)) (w i) := by
  have hhol (i : ι) (x : M) : HolomorphicAt n (c i) x :=
    holomorphicAt_of_mdifferentiableOn isOpen_univ (hc i).mdifferentiableOn (mem_univ x)
  ext x
  rw [mem_iInter]
  change x ∈ cosupport n univ
    (finiteFunctionIdeal (fun i y => c i y^(weightedCommonMark w/w i))) _ ↔ _
  rw [mem_cosupport_finiteFunctionIdeal_iff
    (fun i y => c i y^(weightedCommonMark w/w i)) x (weightedCommonMark w)
    (fun i => holomorphicAt_of_mdifferentiableOn isOpen_univ ((hc i).pow _).mdifferentiableOn (mem_univ x))]
  constructor
  · intro h i
    apply (mem_cosupport_finiteFunctionIdeal_iff _ x _ (fun _ => hhol i x)).mpr
    intro _
    have hiff := vanishes_pow_iff x (c i) (hhol i x) (w i) _ (compressionExponent_pos w hw i)
    rw [weight_mul_compressionExponent] at hiff
    exact hiff.mp (h i)
  · intro h i
    have hi := ((mem_cosupport_finiteFunctionIdeal_iff _ x _ (fun _ => hhol i x)).mp (h i)) ()
    have hiff := vanishes_pow_iff x (c i) (hhol i x) (w i) _ (compressionExponent_pos w hw i)
    rw [weight_mul_compressionExponent] at hiff
    exact hiff.mpr hi

end Functions

local instance (t q : ℕ) : Fintype (normalExponentIndex t q) := normalExponentFintype t q

/-- The original finite coefficient functions are used only on their genuine common domain. -/
def coefficientDomain {k s t : ℕ} {I : Ideal (HolGerm (ComplexModel ((k+s)+t)))}
    (P : ActualAnalyticVertexCoefficientData k s t I) : TopologicalSpace.Opens (ComplexModel (k+s)) :=
  ⟨P.domain,P.isOpen_domain⟩

/-- No function is globally extended: this is the literal actual subtype restriction. -/
def coefficientFunction {k s t : ℕ} {I : Ideal (HolGerm (ComplexModel ((k+s)+t)))}
    (P : ActualAnalyticVertexCoefficientData k s t I) (i : weightedCoefficientIndex k s t I) :
    coefficientDomain P → ℂ := fun y => P.coefficient i.1 i.2.val y.val

/-- The actual positive-mark record on the genuine coefficient-domain manifold. -/
def coefficientMarked {k s t : ℕ} {I : Ideal (HolGerm (ComplexModel ((k+s)+t)))}
    (P : ActualAnalyticVertexCoefficientData k s t I) : MarkedIdeal (k+s) (coefficientDomain P) where
  N := univ
  E := []
  ideal := weightedFunctionIdeal coefficientWeight (coefficientFunction P)
  d := weightedCommonMark (coefficientWeight (k := k) (s := s) (t := t) (I := I))

/-- The original analytic ideal constructs a true coherent marked object and whole weighted cosupport on its real domain. -/
theorem exists_original_coherent_weighted_coefficient_marked (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t)))) :
    ∃ P : ActualAnalyticVertexCoefficientData k s t I,
      (coefficientMarked P).IsWellFormed ∧ 0 < (coefficientMarked P).d ∧
      (coefficientMarked P).cosupp=
        ⋂ i : weightedCoefficientIndex k s t I,
          cosupport (k+s) univ (finiteFunctionIdeal (fun _ : Unit => coefficientFunction P i))
            (coefficientWeight i) := by
  obtain ⟨P⟩ := nonempty_actualAnalyticVertexCoefficientData k s t I
  have hc (i : weightedCoefficientIndex k s t I) :
      MDifferentiable 𝓘(ℂ,ComplexModel (k+s)) 𝓘(ℂ,ℂ) (coefficientFunction P i) := by
    intro y
    have hf := holomorphicAt_of_mdifferentiableOn P.isOpen_domain
      (P.regular i.1 i.2.val i.2.property) y.property
    exact (hf.comp_contMDiff (Eventually.of_forall fun z : coefficientDomain P =>
      (contMDiff_subtype_val (U := coefficientDomain P)).contMDiffAt)).mdifferentiableAt
  have hN : IsClosedSubmanifold (k+s) (univ : Set (coefficientDomain P)) :=
    HomogenizedGlueingTower.isClosedSubmanifold_univ
  refine ⟨P,⟨hN,isCoherent_weightedFunctionIdeal _ _ hc,
    isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩,
    weightedCommonMark_pos _ coefficientWeight_pos,?_⟩
  exact cosupport_weightedFunctionIdeal _ coefficientWeight_pos _ hc

end
end Hironaka.HironakaActualCoherentWeightedCoefficientMarked
