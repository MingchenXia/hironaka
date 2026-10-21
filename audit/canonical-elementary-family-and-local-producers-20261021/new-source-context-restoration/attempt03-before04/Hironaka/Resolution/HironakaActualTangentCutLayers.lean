/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualTangentDisplacementZeroQuotient
import Hironaka.Resolution.HironakaActualPrincipalPartsResidueSymbols
import Hironaka.Resolution.HironakaActualJointTangentCuts

/-!
# Whole B-linear tangent-cut quotients, layers and actual symbols

The actual middle-displacement-zero trace kills precisely the tangent
displacements, retains the original tangent germ scalars, and identifies
every whole normal truncation and layer after that cut. All representatives
and multiplication symbols are those of the same actual trace. The original
joint-ideal specialization derives its whole ideal image internally.
The original-only geometric consumer composes the actual all-cut producer
with this same dictionary to obtain finite freeness of every original
centre-normal layer in one unchanged flattening. No freeness, regularity
or normal-flatness certificate is an input to that endpoint.
Blueprint: `hironaka-actual-tangent-cut-layers-extension.tex`.
-/

set_option autoImplicit false
open Set
namespace Hironaka.HironakaActualTangentCutLayers
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaHolomorphicJetMonomialSpan
  HironakaActualTangentDisplacementZeroQuotient
  HironakaRelativeNormalAssociatedGraded HironakaActualPrincipalPartsResidueSymbols

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d))
    (HolGerm (ComplexModel (d+(d+t)))) := tangentAlgebra d (d+t)
local instance : Algebra (HolGerm (ComplexModel d))
    (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t

/-- The genuine original translated ideal after all literal tangent-displacement cuts. -/
def actualTangentCutIdeal (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Ideal (HolGerm (ComplexModel (d+(d+t)))) :=
  Ideal.map (actualCentreJointPullback d t).toRingHom I ⊔ tangentDisplacementIdeal d t

/-- The entire actual cut ideal maps to the unchanged original ideal. -/
theorem map_actualTangentCutIdeal_eq_original
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom
      (actualTangentCutIdeal d t I)=I := by
  have hV : Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom
      (tangentDisplacementIdeal d t)=⊥ := by
    rw [tangentDisplacementIdeal_eq_ker]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr le_rfl
  rw [actualTangentCutIdeal,Ideal.map_sup,map_jointIdeal_eq_original,hV,sup_bot_eq]

/-- The exact image of every whole truncated joint ideal, with no generator replacement. -/
theorem map_tangentCutTruncation
    (K : Ideal (HolGerm (ComplexModel (d+(d+t))))) (s : ℕ) :
    Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom
      (K ⊔ normalIdeal d (d+t)^s)=
      Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K ⊔ normalIdeal d t^s := by
  rw [Ideal.map_sup,map_jointNormalIdeal_pow_eq_normal]

/-- Containing the actual middle kernel gives exact contraction at every finite order. -/
theorem comap_tangentCutTruncation
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K) (s : ℕ) :
    Ideal.comap (actualTangentDisplacementZeroTrace d t).toRingHom
      (Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K ⊔ normalIdeal d t^s)=
      K ⊔ normalIdeal d (d+t)^s := by
  rw [← map_tangentCutTruncation d t K s,
    Ideal.comap_map_of_surjective (actualTangentDisplacementZeroTrace d t).toRingHom
      (actualTangentDisplacementZeroTrace_surjective d t)]
  change (K ⊔ normalIdeal d (d+t)^s) ⊔
    RingHom.ker (actualTangentDisplacementZeroTrace d t).toRingHom = _
  rw [← tangentDisplacementIdeal_eq_ker]
  exact sup_eq_left.mpr (hV.trans le_sup_left)

private def truncationAlgEquivTo
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K=I) (s : ℕ) :
    (HolGerm (ComplexModel (d+(d+t))) ⧸ (K ⊔ normalIdeal d (d+t)^s)) ≃ₐ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t^s)) := by
  let D := K ⊔ normalIdeal d (d+t)^s
  let F := I ⊔ normalIdeal d t^s
  have hpre : Ideal.comap (actualTangentDisplacementZeroBaseAlgHom d t).toRingHom F=D := by
    change Ideal.comap (actualTangentDisplacementZeroTrace d t).toRingHom
      (I ⊔ normalIdeal d t^s)=K ⊔ normalIdeal d (d+t)^s
    rw [← hI]
    exact comap_tangentCutTruncation d t K hV s
  let f := Ideal.quotientMapₐ F (actualTangentDisplacementZeroBaseAlgHom d t) hpre.ge
  refine AlgEquiv.ofBijective f ⟨?_,?_⟩
  · intro a b hab
    obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨h,rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    change g-h ∈ D
    rw [← hpre]
    change actualTangentDisplacementZeroTrace d t (g-h) ∈ F
    rw [map_sub]
    change Ideal.Quotient.mk F (actualTangentDisplacementZeroTrace d t g)=
      Ideal.Quotient.mk F (actualTangentDisplacementZeroTrace d t h) at hab
    exact Ideal.Quotient.eq.mp hab
  · intro a
    obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨h,hh⟩ := actualTangentDisplacementZeroTrace_surjective d t g
    refine ⟨Ideal.Quotient.mk D h,?_⟩
    change Ideal.Quotient.mk F (actualTangentDisplacementZeroTrace d t h)=Ideal.Quotient.mk F g
    rw [hh]

private theorem truncationAlgEquivTo_mk
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K=I) (s : ℕ)
    (g : HolGerm (ComplexModel (d+(d+t)))) :
    truncationAlgEquivTo d t K hV I hI s
      (Ideal.Quotient.mk (K ⊔ normalIdeal d (d+t)^s) g)=
    Ideal.Quotient.mk (I ⊔ normalIdeal d t^s) (actualTangentDisplacementZeroTrace d t g) := rfl

/-- Every kernel-containing whole joint ideal has its actual B-algebra truncation dictionary. -/
def tangentCutTruncationAlgEquiv
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K) (s : ℕ) :
    (HolGerm (ComplexModel (d+(d+t))) ⧸ (K ⊔ normalIdeal d (d+t)^s)) ≃ₐ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸
        (Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K ⊔ normalIdeal d t^s)) :=
  truncationAlgEquivTo d t K hV _ rfl s

theorem tangentCutTruncationAlgEquiv_mk
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K) (s : ℕ)
    (g : HolGerm (ComplexModel (d+(d+t)))) :
    tangentCutTruncationAlgEquiv d t K hV s
      (Ideal.Quotient.mk (K ⊔ normalIdeal d (d+t)^s) g)=
    Ideal.Quotient.mk
      (Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K ⊔ normalIdeal d t^s)
      (actualTangentDisplacementZeroTrace d t g) := rfl

/-- The same actual original ideal, all tangent displacements cut, and unchanged B scalars. -/
def actualTangentCutTruncationAlgEquiv
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) :
    (HolGerm (ComplexModel (d+(d+t))) ⧸
      (actualTangentCutIdeal d t I ⊔ normalIdeal d (d+t)^s)) ≃ₐ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t^s)) :=
  truncationAlgEquivTo d t (actualTangentCutIdeal d t I) le_sup_right I
    (map_actualTangentCutIdeal_eq_original d t I) s

theorem actualTangentCutTruncationAlgEquiv_mk
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ)
    (g : HolGerm (ComplexModel (d+(d+t)))) :
    actualTangentCutTruncationAlgEquiv d t I s
      (Ideal.Quotient.mk (actualTangentCutIdeal d t I ⊔ normalIdeal d (d+t)^s) g)=
    Ideal.Quotient.mk (I ⊔ normalIdeal d t^s) (actualTangentDisplacementZeroTrace d t g) := rfl

/-- Actual normal-power numerators have actual original normal-power traces. -/
theorem trace_mem_normalIdeal_pow (q : ℕ)
    (g : HolGerm (ComplexModel (d+(d+t)))) (hg : g ∈ normalIdeal d (d+t)^q) :
    actualTangentDisplacementZeroTrace d t g ∈ normalIdeal d t^q := by
  rw [← map_jointNormalIdeal_pow_eq_normal d t q]
  exact Ideal.mem_map_of_mem _ hg

theorem trace_mem_normalIdeal
    (g : HolGerm (ComplexModel (d+(d+t)))) (hg : g ∈ normalIdeal d (d+t)) :
    actualTangentDisplacementZeroTrace d t g ∈ normalIdeal d t := by
  rw [← map_jointNormalIdeal_eq_normal d t]
  exact Ideal.mem_map_of_mem _ hg

section Layers
set_option maxHeartbeats 1000000

private def layerMapTo
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K=I) (q : ℕ) :
    originalNormalGradedPiece d (d+t) K q →ₗ[HolGerm (ComplexModel d)]
      originalNormalGradedPiece d t I q := by
  let e := (truncationAlgEquivTo d t K hV I hI (q+1)).toLinearMap
  refine (e.comp (originalNormalGradedPiece d (d+t) K q).subtype).codRestrict
    (originalNormalGradedPiece d t I q) ?_
  intro z
  obtain ⟨g,hg,he⟩ := z.property
  change g ∈ normalIdeal d (d+t)^q at hg
  have hv : z.val=Ideal.Quotient.mk (K ⊔ normalIdeal d (d+t)^(q+1)) g := he.symm
  change truncationAlgEquivTo d t K hV I hI (q+1) z.val ∈ _
  rw [hv,truncationAlgEquivTo_mk]
  exact ⟨actualTangentDisplacementZeroTrace d t g,trace_mem_normalIdeal_pow d t q g hg,rfl⟩

private theorem layerMapTo_mk
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K=I) (q : ℕ)
    (g : HolGerm (ComplexModel (d+(d+t)))) (hg : g ∈ normalIdeal d (d+t)^q) :
    (layerMapTo d t K hV I hI q
      ⟨Ideal.Quotient.mk (K ⊔ normalIdeal d (d+t)^(q+1)) g,⟨g,hg,rfl⟩⟩).val =
    Ideal.Quotient.mk (I ⊔ normalIdeal d t^(q+1)) (actualTangentDisplacementZeroTrace d t g) := rfl

private theorem layerMapTo_injective
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K=I) (q : ℕ) :
    Function.Injective (layerMapTo d t K hV I hI q) := by
  intro a b hab
  apply Subtype.ext
  exact (truncationAlgEquivTo d t K hV I hI (q+1)).injective (congrArg Subtype.val hab)

private theorem layerMapTo_surjective
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K=I) (q : ℕ) :
    Function.Surjective (layerMapTo d t K hV I hI q) := by
  rintro ⟨x,hx⟩
  obtain ⟨h,hh,he⟩ := hx
  change h ∈ normalIdeal d t^q at hh
  rw [← map_jointNormalIdeal_pow_eq_normal d t q] at hh
  obtain ⟨g,hg,hg'⟩ :=
    (Ideal.mem_map_iff_of_surjective (actualTangentDisplacementZeroTrace d t).toRingHom
      (actualTangentDisplacementZeroTrace_surjective d t)).mp hh
  refine ⟨⟨Ideal.Quotient.mk (K ⊔ normalIdeal d (d+t)^(q+1)) g,⟨g,hg,rfl⟩⟩,?_⟩
  apply Subtype.ext
  have hhg : actualTangentDisplacementZeroTrace d t g=h := hg'
  have hclass := congrArg (Ideal.Quotient.mk (I ⊔ normalIdeal d t^(q+1))) hhg
  exact (layerMapTo_mk d t K hV I hI q g hg).trans (hclass.trans he)

private theorem layerMapTo_symbol
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K=I)
    (a : HolGerm (ComplexModel (d+(d+t)))) (ha : a ∈ normalIdeal d (d+t))
    (q : ℕ) (z : originalNormalGradedPiece d (d+t) K q) :
    layerMapTo d t K hV I hI (q+1)
      (originalLayerSymbolMul d (d+t) K a ha q z)=
    originalLayerSymbolMul d t I (actualTangentDisplacementZeroTrace d t a)
      (trace_mem_normalIdeal d t a ha) q (layerMapTo d t K hV I hI q z) := by
  rcases z with ⟨x,hx⟩
  obtain ⟨g,hg,rfl⟩ := hx
  change g ∈ normalIdeal d (d+t)^q at hg
  apply Subtype.ext
  change truncationAlgEquivTo d t K hV I hI (q+2)
    (Ideal.Quotient.mk (K ⊔ normalIdeal d (d+t)^(q+2)) (a*g))=
    Ideal.Quotient.mk (I ⊔ normalIdeal d t^(q+2))
      (actualTangentDisplacementZeroTrace d t a * actualTangentDisplacementZeroTrace d t g)
  rw [truncationAlgEquivTo_mk,map_mul]

/-- The named whole B-linear layer map for any actual kernel-containing joint ideal. -/
def tangentCutLayerMap
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K) (q : ℕ) :
    originalNormalGradedPiece d (d+t) K q →ₗ[HolGerm (ComplexModel d)]
      originalNormalGradedPiece d t (Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K) q :=
  layerMapTo d t K hV _ rfl q

theorem tangentCutLayerMap_mk
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K) (q : ℕ)
    (g : HolGerm (ComplexModel (d+(d+t)))) (hg : g ∈ normalIdeal d (d+t)^q) :
    (tangentCutLayerMap d t K hV q
      ⟨Ideal.Quotient.mk (K ⊔ normalIdeal d (d+t)^(q+1)) g,⟨g,hg,rfl⟩⟩).val =
    Ideal.Quotient.mk
      (Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K ⊔ normalIdeal d t^(q+1))
      (actualTangentDisplacementZeroTrace d t g) := rfl

def tangentCutLayerEquiv
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K) (q : ℕ) :
    originalNormalGradedPiece d (d+t) K q ≃ₗ[HolGerm (ComplexModel d)]
      originalNormalGradedPiece d t (Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K) q :=
  LinearEquiv.ofBijective (tangentCutLayerMap d t K hV q)
    ⟨layerMapTo_injective d t K hV _ rfl q,layerMapTo_surjective d t K hV _ rfl q⟩

theorem tangentCutLayerMap_symbol
    (K : Ideal (HolGerm (ComplexModel (d+(d+t)))))
    (hV : tangentDisplacementIdeal d t ≤ K)
    (a : HolGerm (ComplexModel (d+(d+t)))) (ha : a ∈ normalIdeal d (d+t))
    (q : ℕ) (z : originalNormalGradedPiece d (d+t) K q) :
    tangentCutLayerMap d t K hV (q+1) (originalLayerSymbolMul d (d+t) K a ha q z)=
    originalLayerSymbolMul d t (Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K)
      (actualTangentDisplacementZeroTrace d t a) (trace_mem_normalIdeal d t a ha) q
      (tangentCutLayerMap d t K hV q z) :=
  layerMapTo_symbol d t K hV _ rfl a ha q z

/-- The same original joint cut gives the unchanged original normal layer, over B. -/
def actualTangentCutLayerMap
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    originalNormalGradedPiece d (d+t) (actualTangentCutIdeal d t I) q →ₗ[HolGerm (ComplexModel d)]
      originalNormalGradedPiece d t I q :=
  layerMapTo d t (actualTangentCutIdeal d t I) le_sup_right I
    (map_actualTangentCutIdeal_eq_original d t I) q

theorem actualTangentCutLayerMap_mk
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (g : HolGerm (ComplexModel (d+(d+t)))) (hg : g ∈ normalIdeal d (d+t)^q) :
    (actualTangentCutLayerMap d t I q
      ⟨Ideal.Quotient.mk (actualTangentCutIdeal d t I ⊔ normalIdeal d (d+t)^(q+1)) g,⟨g,hg,rfl⟩⟩).val =
    Ideal.Quotient.mk (I ⊔ normalIdeal d t^(q+1)) (actualTangentDisplacementZeroTrace d t g) := rfl

def actualTangentCutLayerEquiv
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    originalNormalGradedPiece d (d+t) (actualTangentCutIdeal d t I) q ≃ₗ[HolGerm (ComplexModel d)]
      originalNormalGradedPiece d t I q :=
  LinearEquiv.ofBijective (actualTangentCutLayerMap d t I q)
    ⟨layerMapTo_injective d t (actualTangentCutIdeal d t I) le_sup_right I
        (map_actualTangentCutIdeal_eq_original d t I) q,
      layerMapTo_surjective d t (actualTangentCutIdeal d t I) le_sup_right I
        (map_actualTangentCutIdeal_eq_original d t I) q⟩

theorem actualTangentCutLayerMap_symbol
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (a : HolGerm (ComplexModel (d+(d+t)))) (ha : a ∈ normalIdeal d (d+t))
    (q : ℕ) (z : originalNormalGradedPiece d (d+t) (actualTangentCutIdeal d t I) q) :
    actualTangentCutLayerMap d t I (q+1)
      (originalLayerSymbolMul d (d+t) (actualTangentCutIdeal d t I) a ha q z)=
    originalLayerSymbolMul d t I (actualTangentDisplacementZeroTrace d t a)
      (trace_mem_normalIdeal d t a ha) q (actualTangentCutLayerMap d t I q z) :=
  layerMapTo_symbol d t (actualTangentCutIdeal d t I) le_sup_right I
    (map_actualTangentCutIdeal_eq_original d t I) a ha q z

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Every actual tangent-displacement symbol is killed by the final dictionary. -/
theorem actualTangentCutLayerMap_tangentSymbol_zero
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (i : Fin d) (q : ℕ)
    (z : originalNormalGradedPiece d (d+t) (actualTangentCutIdeal d t I) q) :
    actualTangentCutLayerMap d t I (q+1)
      (originalLayerSymbolMul d (d+t) (actualTangentCutIdeal d t I)
        (normalCoordinate d (d+t) (i.castAdd t)) (Ideal.subset_span ⟨i.castAdd t,rfl⟩) q z)=0 := by
  rcases z with ⟨x,hx⟩
  obtain ⟨g,hg,rfl⟩ := hx
  change g ∈ normalIdeal d (d+t)^q at hg
  apply Subtype.ext
  change actualTangentCutTruncationAlgEquiv d t I (q+2)
    (Ideal.Quotient.mk (actualTangentCutIdeal d t I ⊔ normalIdeal d (d+t)^(q+2))
      (normalCoordinate d (d+t) (i.castAdd t)*g))=0
  rw [actualTangentCutTruncationAlgEquiv_mk,map_mul]
  change Ideal.Quotient.mk (I ⊔ normalIdeal d t^(q+2))
    (actualTangentDisplacementZeroTrace d t (coordinateGerm ((i.castAdd t).natAdd d))*
      actualTangentDisplacementZeroTrace d t g)=0
  rw [actualTangentDisplacementZeroTrace_v,zero_mul,map_zero]

/-- Every actual normal-displacement symbol becomes its original normal-coordinate symbol. -/
theorem actualTangentCutLayerMap_normalSymbol
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (i : Fin t) (q : ℕ)
    (z : originalNormalGradedPiece d (d+t) (actualTangentCutIdeal d t I) q) :
    actualTangentCutLayerMap d t I (q+1)
      (originalLayerSymbolMul d (d+t) (actualTangentCutIdeal d t I)
        (normalCoordinate d (d+t) (i.natAdd d)) (Ideal.subset_span ⟨i.natAdd d,rfl⟩) q z)=
    originalLayerSymbolMul d t I (normalCoordinate d t i) (Ideal.subset_span ⟨i,rfl⟩) q
      (actualTangentCutLayerMap d t I q z) := by
  simpa only [normalCoordinate,actualTangentDisplacementZeroTrace_x] using
    actualTangentCutLayerMap_symbol d t I (normalCoordinate d (d+t) (i.natAdd d))
      (Ideal.subset_span ⟨i.natAdd d,rfl⟩) q z

end Layers

open HironakaActualJointTangentCuts

/-- The literal list of all tangent-displacement cuts contains the entire actual trace kernel. -/
theorem tangentDisplacementIdeal_le_allTangentCuts
    (K : Ideal (HolGerm (ComplexModel (d+(d+t))))) :
    tangentDisplacementIdeal d t ≤ jointCoordinateCuts d (d+t) K
      (List.ofFn (fun i : Fin d => i.castAdd t)) := by
  apply Ideal.span_le.mpr
  rintro g ⟨i,rfl⟩
  change normalCoordinate d (d+t) (i.castAdd t) ∈ parameterCuts K (normalCoordinate d (d+t))
    (List.ofFn (fun j : Fin d => j.castAdd t))
  exact parameter_mem_parameterCuts K (normalCoordinate d (d+t)) _ (i.castAdd t)
    (List.mem_ofFn.mpr ⟨i,rfl⟩)

/-- The same actual trace kills every added tangent parameter, retaining the original whole ideal image. -/
theorem map_allTangentCuts
    (K : Ideal (HolGerm (ComplexModel (d+(d+t))))) :
    Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom
      (jointCoordinateCuts d (d+t) K (List.ofFn (fun i : Fin d => i.castAdd t)))=
    Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K := by
  apply map_parameterCuts_zero
  intro i hi
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
  exact actualTangentDisplacementZeroTrace_v d t j

section OriginalCentre
open scoped Manifold ContDiff
open OkaRelationSheaf HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualCentrePrincipalParts HironakaStrictFilteredGradedQuotient
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]
local instance : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t)))) :=
  IsScalarTower.of_algHom (tangentPullback d (d+t))
set_option maxHeartbeats 1000000

/-- Original coherent constant-HS regular-centre geometry produces all original normal layers finite free. -/
theorem exists_original_hs_constant_centre_normal_layers_finite_free
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      ∀ q : ℕ,
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I0 q) ∧
        Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I0 q) := by
  obtain ⟨Φ,hsrc,h0,hflat,hcut⟩ :=
    exists_original_hs_constant_centre_all_tangent_cut_layers_free C x hreg A hA hhs
  refine ⟨Φ,hsrc,h0,hflat,?_⟩
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) 0)
  let J := Ideal.map (actualCentreJointPullback d t).toRingHom I0
  let K := jointCoordinateCuts d (d+t) J (List.ofFn (fun i : Fin d => i.castAdd t))
  have hV : tangentDisplacementIdeal d t ≤ K := tangentDisplacementIdeal_le_allTangentCuts d t J
  have hmap : Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom K=I0 := by
    exact (map_allTangentCuts d t J).trans (map_jointIdeal_eq_original d t I0)
  change ∀ q : ℕ,
    Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I0 q) ∧
    Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I0 q)
  intro q
  let : Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d (d+t) K q) := by
    change Module.Finite (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d (d+t)) q)
    exact (hcut q).1
  let : Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d (d+t) K q) := by
    change Module.Free (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d (d+t)) q)
    exact (hcut q).2
  let E : originalNormalGradedPiece d (d+t) K q ≃ₗ[HolGerm (ComplexModel d)]
      originalNormalGradedPiece d t I0 q :=
    LinearEquiv.ofBijective (layerMapTo d t K hV I0 hmap q)
      ⟨layerMapTo_injective d t K hV I0 hmap q,layerMapTo_surjective d t K hV I0 hmap q⟩
  exact ⟨Module.Finite.of_surjective E.toLinearMap E.surjective,Module.Free.of_equiv E⟩

end OriginalCentre
end
end Hironaka.HironakaActualTangentCutLayers
