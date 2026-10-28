/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualZeroSectionCoefficientIdeals

/-!
# Closed zero-section derivatives along an arbitrary original regular carrier

The independently defined closed lift of an original closed regular A has a
true product flattening, preserving all base-normal coordinates and the added
zero coordinate. The same original finite presentation, actual inverse-section
square and derivative chain rule give equality of ENTIRE along-carrier
functional ideals and all iterates. No target differential, canonical value,
centre or comparison history is supplied. Canonical embedding independence and
proper intrinsic resolution descent remain open.
Blueprint: `hironaka-actual-zero-section-submanifold-differentials-extension.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualZeroSectionSubmanifoldDifferentials
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualIntrinsicStableAmbientIso DerivativeIdeal DerivativeIdealAlong
  DerivativeIdealAlongCoherent GiraudAlong BlowupFlatCoordinates
  RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient
variable {n : ℕ}

/-- Independently defined original closed lift, NOT the ambient cylinder. -/
def liftedCarrier (A : Set (ComplexModel n)) : Set (ComplexModel (n+1)) :=
  {z | tangentProjection n 1 z∈A ∧ actualJointNormalProjection n 1 z=0}

theorem section_mem_liftedCarrier_iff (A : Set (ComplexModel n)) (x : ComplexModel n) :
    tangentInclusion n 1 x∈liftedCarrier A ↔ x∈A := by
  simp [liftedCarrier,tangentProjection_tangentInclusion]

/-- The actual product flattening is constructed from the ORIGINAL base
flattening, and preserves the same literal added normal coordinate. -/
def productFlat (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) :
    LocalHolomorphicEquivAt (n := n+1)
      (chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x) (tangentInclusion n 1 x)) where
  source := tangentProjection n 1 ⁻¹' Φ.source
  target := tangentProjection n 1 ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source.preimage (tangentProjection n 1).continuous
  isOpen_target := Φ.isOpen_target.preimage (tangentProjection n 1).continuous
  center_mem_source := by
    change tangentProjection n 1 (tangentInclusion n 1 x)∈Φ.source
    rw [tangentProjection_tangentInclusion]
    have h := Φ.center_mem_source
    change x∈Φ.source at h
    exact h
  toFun := fun z => HironakaActualIntrinsicStableAmbientIso.join
    (Φ.toFun (tangentProjection n 1 z)) (actualJointNormalProjection n 1 z)
  invFun := fun z => HironakaActualIntrinsicStableAmbientIso.join
    (Φ.invFun (tangentProjection n 1 z)) (actualJointNormalProjection n 1 z)
  toFun_holomorphic := by
    intro z hz
    have hΦ := Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hz)
    exact (((tangentInclusion n 1).differentiableAt.comp z
      (hΦ.comp z (tangentProjection n 1).differentiableAt)).add
        ((actualJointNormalInclusion n 1).differentiableAt.comp z
          (actualJointNormalProjection n 1).differentiableAt)).differentiableWithinAt
  invFun_holomorphic := by
    intro z hz
    have hΦ := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz)
    exact (((tangentInclusion n 1).differentiableAt.comp z
      (hΦ.comp z (tangentProjection n 1).differentiableAt)).add
        ((actualJointNormalInclusion n 1).differentiableAt.comp z
          (actualJointNormalProjection n 1).differentiableAt)).differentiableWithinAt
  mapsTo_toFun := by
    intro z hz
    change tangentProjection n 1 (HironakaActualIntrinsicStableAmbientIso.join
      (Φ.toFun (tangentProjection n 1 z)) (actualJointNormalProjection n 1 z))∈Φ.target
    rw [first_join]
    exact Φ.mapsTo_toFun hz
  mapsTo_invFun := by
    intro z hz
    change tangentProjection n 1 (HironakaActualIntrinsicStableAmbientIso.join
      (Φ.invFun (tangentProjection n 1 z)) (actualJointNormalProjection n 1 z))∈Φ.source
    rw [first_join]
    exact Φ.mapsTo_invFun hz
  left_inv := by
    intro z hz
    simp only [first_join,second_join,Φ.left_inv _ hz,join_projections]
  right_inv := by
    intro z hz
    simp only [first_join,second_join,Φ.right_inv _ hz,join_projections]

theorem productFlat_section (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (u : ComplexModel n) :
    (productFlat x Φ).toFun (tangentInclusion n 1 u)=tangentInclusion n 1 (Φ.toFun u) := by
  simp [productFlat,HironakaActualIntrinsicStableAmbientIso.join,tangentProjection_tangentInclusion]

theorem productFlat_inverse_section (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (u : ComplexModel n) :
    (productFlat x Φ).invFun (tangentInclusion n 1 u)=tangentInclusion n 1 (Φ.invFun u) := by
  simp [productFlat,HironakaActualIntrinsicStableAmbientIso.join,tangentProjection_tangentInclusion]

private theorem join_plane_iff (a : ComplexModel n) (b : ComplexModel 1) {k : ℕ} (hk : k ≤ n) :
    HironakaActualIntrinsicStableAmbientIso.join a b∈complexCoordinatePlane (n+1) k ↔
      a∈complexCoordinatePlane n k ∧ b=0 := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro i hi
      simpa [HironakaActualIntrinsicStableAmbientIso.join] using h (i.castAdd 1) hi
    · ext i
      simpa [HironakaActualIntrinsicStableAmbientIso.join] using h (i.natAdd n) (by simp;omega)
  · rintro ⟨ha,hb⟩ i hi
    refine Fin.addCases (fun j hj => ?_) (fun j _hj => ?_) i hi
    · simpa [HironakaActualIntrinsicStableAmbientIso.join] using ha j hj
    · simp [HironakaActualIntrinsicStableAmbientIso.join,hb]

private theorem productFlat_carrier (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    {A : Set (ComplexModel n)} {k : ℕ} (hk : k ≤ n)
    (hflat : ∀ {y : ComplexModel n},y∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y∈Φ.source →
      (y∈A ↔ Φ.toFun (chartAt (ComplexModel n) x y)∈complexCoordinatePlane n k))
    {z : ComplexModel (n+1)} (hz : z∈(productFlat x Φ).source) :
    z∈liftedCarrier A ↔ (productFlat x Φ).toFun z∈complexCoordinatePlane (n+1) k := by
  have hy : tangentProjection n 1 z∈(chartAt (ComplexModel n) x).source := by simp
  have hΦ : chartAt (ComplexModel n) x (tangentProjection n 1 z)∈Φ.source := hz
  have h := hflat hy hΦ
  change (tangentProjection n 1 z∈A ∧ actualJointNormalProjection n 1 z=0) ↔
    HironakaActualIntrinsicStableAmbientIso.join (Φ.toFun (tangentProjection n 1 z))
      (actualJointNormalProjection n 1 z)∈complexCoordinatePlane (n+1) k
  rw [join_plane_iff _ _ hk]
  exact and_congr_left fun _ => h

/-- The lifted carrier's original closed regular geometry is produced
internally from the genuine original A, not supplied as a target certificate. -/
theorem liftedCarrier_closed_submanifold {A : Set (ComplexModel n)}
    (hA : IsClosedSubmanifold n A) : IsClosedSubmanifold (n+1) (liftedCarrier A) := by
  refine ⟨(hA.1.preimage (tangentProjection n 1).continuous).inter
    (isClosed_eq (actualJointNormalProjection n 1).continuous continuous_const),?_⟩
  intro z hz
  let x := tangentProjection n 1 z
  have hx : x∈A := hz.1
  have hsec : tangentInclusion n 1 x=z := by
    have hq : actualJointNormalProjection n 1 z=0 := hz.2
    simpa only [HironakaActualIntrinsicStableAmbientIso.join,hq,map_zero,add_zero]
      using join_projections (n := n) (m := 1) z
  obtain ⟨k,hkn,_hx,Φ,hsrc,h0,hflat⟩ := hA.2 x hx
  have hreg : RegularAtDim (n := n+1) (liftedCarrier A) (tangentInclusion n 1 x) k := by
    refine ⟨by omega,(section_mem_liftedCarrier_iff A x).mpr hx,productFlat x Φ,?_,?_,?_⟩
    · change _ ⊆ (Set.univ : Set (ComplexModel (n+1)))
      exact subset_univ _
    · change (productFlat x Φ).toFun (tangentInclusion n 1 x)=0
      rw [productFlat_section]
      have hΦ0 : Φ.toFun x=0 := h0
      rw [hΦ0,map_zero]
    · intro y _hy hyΦ
      exact productFlat_carrier x Φ hkn hflat hyΦ
  exact ⟨k,by simpa only [hsec] using hreg⟩

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

private theorem zero_mem_span {k : ℕ} (x : ComplexModel k) (S : (ComplexModel k → ℂ) → Prop) :
    IsInSpanAt (n := k) S x (fun _ => 0) := by
  refine ⟨holomorphicAt_const 0,0,Fin.elim0,Fin.elim0,(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),?_⟩
  exact Eventually.of_forall fun _ => by simp

private theorem productFlat_domain_iff (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (z : ComplexModel (n+1)) :
    z ∈ flatDomain (productFlat x Φ) ↔ tangentProjection n 1 z ∈ flatDomain Φ := by
  change (z∈Set.univ ∧ tangentProjection n 1 z∈Φ.source) ↔
    (tangentProjection n 1 z∈Set.univ ∧ tangentProjection n 1 z∈Φ.source)
  simp only [mem_univ, true_and]

private theorem productFlat_map_section (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (u : ComplexModel n) :
    flatMap (productFlat x Φ) (tangentInclusion n 1 u)=tangentInclusion n 1 (flatMap Φ u) :=
  productFlat_section x Φ u

private theorem productFlat_inv_section (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (u : ComplexModel n) :
    flatInv (productFlat x Φ) (tangentInclusion n 1 u)=tangentInclusion n 1 (flatInv Φ u) :=
  productFlat_inverse_section x Φ u

private theorem productFlat_coord_section (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (i : Fin n) :
    flatCoord (productFlat x Φ) (i.castAdd 1) ∘ tangentInclusion n 1=flatCoord Φ i := by
  funext y
  change (productFlat x Φ).toFun (tangentInclusion n 1 y) (i.castAdd 1)=Φ.toFun y i
  rw [productFlat_section]
  simp

private theorem productFlat_added_coord_section (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (i : Fin 1) :
    flatCoord (productFlat x Φ) (i.natAdd n) ∘ tangentInclusion n 1=fun _ => 0 := by
  funext y
  change (productFlat x Φ).toFun (tangentInclusion n 1 y) (i.natAdd n)=0
  rw [productFlat_section]
  simp

private theorem productFlat_partial_section (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    {y : ComplexModel n} (hy : y∈flatDomain Φ) (g : ComplexModel (n+1) → ℂ)
    (hg : HolomorphicAt (n+1) g (tangentInclusion n 1 y)) (i : Fin n) :
    flatPartial (productFlat x Φ) (i.castAdd 1) g (tangentInclusion n 1 y)=
      flatPartial Φ i (g ∘ tangentInclusion n 1) y := by
  have hsy : tangentInclusion n 1 y∈flatDomain (productFlat x Φ) := by
    apply (productFlat_domain_iff x Φ _).mpr
    rwa [tangentProjection_tangentInclusion]
  have hcomp : HolomorphicAt n (g ∘ tangentInclusion n 1) y :=
    hg.comp_contMDiff (Eventually.of_forall fun _ => (tangentInclusion n 1).contMDiff.contMDiffAt)
  rw [flatPartial_eq hsy hg,flatPartial_eq hy hcomp]
  have hΓsrc : (productFlat x Φ).source⊆
      (chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x)).target := by
    change _ ⊆ (Set.univ : Set (ComplexModel (n+1)))
    exact subset_univ _
  have hgd := differentiableAt_comp_flatInv (flatMap_mem_target hsy) hΓsrc
    (show HolomorphicAt (n+1) g (flatInv (productFlat x Φ)
      (flatMap (productFlat x Φ) (tangentInclusion n 1 y))) by
        rw [flatInv_flatMap hsy];exact hg)
  rw [productFlat_map_section] at hgd
  have heq : (g ∘ flatInv (productFlat x Φ)) ∘ tangentInclusion n 1=
      (g ∘ tangentInclusion n 1) ∘ flatInv Φ := by
    funext u
    simp only [Function.comp_apply,productFlat_inv_section]
  have hc := (hgd.hasFDerivAt.comp (flatMap Φ y) (tangentInclusion n 1).hasFDerivAt).fderiv
  rw [heq] at hc
  have h := congrArg (fun L => L (EuclideanSpace.single i 1)) hc
  simp only [ContinuousLinearMap.comp_apply,section_single] at h
  rw [productFlat_map_section]
  exact h.symm

private theorem productFlat_partial_section_eventually (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (g : ComplexModel (n+1) → ℂ) (hg : HolomorphicAt (n+1) g (tangentInclusion n 1 x)) (i : Fin n) :
    flatPartial (productFlat x Φ) (i.castAdd 1) g ∘ tangentInclusion n 1
      =ᶠ[𝓝 x] flatPartial Φ i (g ∘ tangentInclusion n 1) := by
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ),
    (tangentInclusion n 1).continuous.continuousAt.eventually hg.eventually] with y hy hgy
  exact productFlat_partial_section x Φ hy g hgy i

private def liftFamilyIndex {r : ℕ} :
    Fin r ⊕ Fin n ⊕ (Fin r × Fin n) → Fin r ⊕ Fin (n+1) ⊕ (Fin r × Fin (n+1))
  | .inl i => .inl i
  | .inr (.inl j) => .inr (.inl (j.castAdd 1))
  | .inr (.inr (i,j)) => .inr (.inr (i,j.castAdd 1))

private theorem family_holomorphic {m : ℕ} (x : ComplexModel m)
    (Φ : LocalHolomorphicEquivAt (n := m) (chartAt (ComplexModel m) x x))
    (k : ℕ) {r : ℕ} (G : Fin r → ComplexModel m → ℂ)
    (hG : ∀ i,HolomorphicAt m (G i) x) (c : Fin r ⊕ Fin m ⊕ (Fin r × Fin m)) :
    HolomorphicAt m (derivFamilyAlong Φ k G c) x := by
  rcases c with i | j | ⟨i,j⟩
  · exact hG i
  · by_cases hj : k≤j.val
    · simpa only [derivFamilyAlong,if_pos hj] using
        holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ)
    · simpa only [derivFamilyAlong,if_neg hj] using (holomorphicAt_const (n := m) (x := x) (0 : ℂ))
  · by_cases hj : j.val<k
    · simpa only [derivFamilyAlong,if_pos hj] using
        holomorphicAt_flatPartial j (mem_flatDomain_self Φ) (hG i)
    · simpa only [derivFamilyAlong,if_neg hj] using (holomorphicAt_const (n := m) (x := x) (0 : ℂ))

private theorem lifted_family_base (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (k : ℕ) {r : ℕ} (G : Fin r → ComplexModel (n+1) → ℂ)
    (hG : ∀ i,HolomorphicAt (n+1) (G i) (tangentInclusion n 1 x))
    (c : Fin r ⊕ Fin n ⊕ (Fin r × Fin n)) :
    derivFamilyAlong (productFlat x Φ) k G (liftFamilyIndex c) ∘ tangentInclusion n 1
      =ᶠ[𝓝 x] derivFamilyAlong Φ k (fun i => G i ∘ tangentInclusion n 1) c := by
  rcases c with i | j | ⟨i,j⟩
  · exact Filter.EventuallyEq.rfl
  · by_cases hj : k≤j.val
    · simp only [liftFamilyIndex,derivFamilyAlong,Fin.val_castAdd,if_pos hj]
      exact Eventually.of_forall fun y => congrFun (productFlat_coord_section x Φ j) y
    · simp only [liftFamilyIndex,derivFamilyAlong,Fin.val_castAdd,if_neg hj]
      exact Filter.EventuallyEq.rfl
  · by_cases hj : j.val<k
    · simpa only [liftFamilyIndex,derivFamilyAlong,Fin.val_castAdd,if_pos hj] using
        productFlat_partial_section_eventually x Φ (G i) (hG i) j
    · simp only [liftFamilyIndex,derivFamilyAlong,Fin.val_castAdd,if_neg hj]
      exact Filter.EventuallyEq.rfl

private theorem restricted_submanifold_derivative_family_iff (x : ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    {k : ℕ} (hk : k≤n) {r : ℕ} (G : Fin r → ComplexModel (n+1) → ℂ)
    (hG : ∀ i,HolomorphicAt (n+1) (G i) (tangentInclusion n 1 x)) (F : ComplexModel n → ℂ) :
    IsInSpanAt (n := n)
      (·∈range fun c => derivFamilyAlong (productFlat x Φ) k G c ∘ tangentInclusion n 1) x F ↔
    IsInSpanAt (n := n)
      (·∈range (derivFamilyAlong Φ k (fun i => G i ∘ tangentInclusion n 1))) x F := by
  have hcomp (i : Fin r) : HolomorphicAt n (G i ∘ tangentInclusion n 1) x :=
    (hG i).comp_contMDiff (Eventually.of_forall fun _ => (tangentInclusion n 1).contMDiff.contMDiffAt)
  have hB := family_holomorphic x Φ k (fun i => G i ∘ tangentInclusion n 1) hcomp
  have hS (c : Fin r ⊕ Fin (n+1) ⊕ (Fin r × Fin (n+1))) : HolomorphicAt n
      (derivFamilyAlong (productFlat x Φ) k G c ∘ tangentInclusion n 1) x :=
    (family_holomorphic _ (productFlat x Φ) k G hG c).comp_contMDiff
      (Eventually.of_forall fun _ => (tangentInclusion n 1).contMDiff.contMDiffAt)
  constructor
  · intro h
    refine IsInSpanAt.trans ?_ h
    rintro _ ⟨c,rfl⟩
    rcases c with i | j | ⟨i,j⟩
    · exact isInSpanAt_self ⟨.inl i,rfl⟩ (hcomp i)
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · exact isInSpanAt_congr (isInSpanAt_self ⟨.inr (.inl j),rfl⟩ (hB _))
          (lifted_family_base x Φ k G hG (.inr (.inl j))).symm
      · have hj : k≤(j.natAdd n).val := by simp;omega
        simp only [derivFamilyAlong,if_pos hj]
        rw [productFlat_added_coord_section]
        exact zero_mem_span _ _
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · exact isInSpanAt_congr (isInSpanAt_self ⟨.inr (.inr (i,j)),rfl⟩ (hB _))
          (lifted_family_base x Φ k G hG (.inr (.inr (i,j)))).symm
      · have hj : ¬(j.natAdd n).val<k := by simp;omega
        simp only [derivFamilyAlong,if_neg hj,Function.comp_def]
        exact zero_mem_span _ _
  · intro h
    refine IsInSpanAt.trans ?_ h
    rintro _ ⟨c,rfl⟩
    exact isInSpanAt_congr (isInSpanAt_self ⟨liftFamilyIndex c,rfl⟩ (hS _))
      (lifted_family_base x Φ k G hG c)

/-- The actual closed lift of ANY original closed regular carrier has the
same whole derivative ideal after the SAME closed zero section. -/
theorem zero_section_submanifold_derivIdealAlong {A : Set (ComplexModel n)}
    (hA : IsClosedSubmanifold n A) (J : GermIdeal (n+1) (ComplexModel (n+1)))
    (hJ : J.IsCoherent) :
    GermIdeal.pullback (m := n) (tangentInclusion n 1) (derivIdealAlong (liftedCarrier A) J)=
      derivIdealAlong A (GermIdeal.pullback (m := n) (tangentInclusion n 1) J) := by
  apply GermIdeal.ext
  funext x F
  apply propext
  by_cases hx : x∈A
  · obtain ⟨k,hkn,_hx,Φ,hΦsrc,_h0,hflat⟩ := hA.2 x hx
    obtain ⟨U₀,hU₀,hxU₀,r,G,hG,hgen⟩ := hJ (tangentInclusion n 1 x)
    let U := U₀ ∩ flatDomain (productFlat x Φ)
    have hU : IsOpen U := hU₀.inter (isOpen_flatDomain _)
    have hxU : tangentInclusion n 1 x∈U := ⟨hxU₀,mem_flatDomain_self _⟩
    have hGh : ∀ i z,z∈U → HolomorphicAt (n+1) (G i) z :=
      fun i z hz => holomorphicAt_of_mdifferentiableOn hU₀ (hG i) hz.1
    have hΓsrc : (productFlat x Φ).source⊆
        (chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x)).target := by
      change _ ⊆ (Set.univ : Set (ComplexModel (n+1)))
      exact subset_univ _
    have hΓflat : ∀ {z : ComplexModel (n+1)},
        z∈(chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x)).source →
        chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x) z∈(productFlat x Φ).source →
        (z∈liftedCarrier A ↔ (productFlat x Φ).toFun
          (chartAt (ComplexModel (n+1)) (tangentInclusion n 1 x) z)∈
            complexCoordinatePlane (n+1) k) := by
      intro z _ hz
      exact productFlat_carrier x Φ hkn hflat hz
    have hD : ∀ a,(derivIdealAlong (liftedCarrier A) J).mem (tangentInclusion n 1 x) a ↔
        IsInSpanAt (n := n+1) (·∈range (derivFamilyAlong (productFlat x Φ) k G))
          (tangentInclusion n 1 x) a :=
      fun a => derivIdealAlong_mem_iff_of_generators hΓsrc hΓflat hU (fun _ hz => hz.2)
        (fun i => (hG i).mono fun _ hz => hz.1) (fun y hy => hgen y hy.1) hxU a
    have hDf := family_holomorphic (tangentInclusion n 1 x) (productFlat x Φ) k G
      (fun i => hGh i _ hxU)
    let V := tangentInclusion n 1 ⁻¹' U
    have hV : IsOpen V := hU.preimage (tangentInclusion n 1).continuous
    have hxV : x∈V := hxU
    have hVΦ : V⊆flatDomain Φ := by
      intro y hy
      have h := (productFlat_domain_iff x Φ _).mp hy.2
      rwa [tangentProjection_tangentInclusion] at h
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
        (fun i => hGh i _ hy) (hgen _ hy.1) a
    have hBase := derivIdealAlong_mem_iff_of_generators hΦsrc hflat hV hVΦ hGV hgenV hxV F
    exact (pullback_span_iff (derivIdealAlong (liftedCarrier A) J) x
      (derivFamilyAlong (productFlat x Φ) k G) hDf hD F).trans
        ((restricted_submanifold_derivative_family_iff x Φ hkn G (fun i => hGh i _ hxU) F).trans
          hBase.symm)
  · constructor
    · intro h
      exact derivIdealAlong_mem_of_notMem hA.1 hx (GermIdeal.mem_pullback_iff.mp h).holomorphicAt
    · intro h
      have hF : HolomorphicAt n F x := h.holomorphicAt
      have hsx : tangentInclusion n 1 x∉liftedCarrier A := by
        rwa [section_mem_liftedCarrier_iff]
      have hunit : (derivIdealAlong (liftedCarrier A) J).mem (tangentInclusion n 1 x)
          (fun _ => 1) :=
        derivIdealAlong_mem_of_notMem (liftedCarrier_closed_submanifold hA).1 hsx (holomorphicAt_const 1)
      apply GermIdeal.mem_pullback_iff.mpr
      exact isInSpanAt_of_eq_mul ⟨fun _ => 1,hunit,rfl⟩ hF hF
        (Eventually.of_forall fun _ => (mul_one _).symm)

/-- Every iterated whole derivative ideal compares through the SAME closed
section, with the original proper carrier retained at every depth. -/
theorem zero_section_submanifold_iterDerivIdealAlong {A : Set (ComplexModel n)}
    (hA : IsClosedSubmanifold n A) (J : GermIdeal (n+1) (ComplexModel (n+1)))
    (hJ : J.IsCoherent) (q : ℕ) :
    GermIdeal.pullback (m := n) (tangentInclusion n 1) (iterDerivIdealAlong (liftedCarrier A) J q)=
      iterDerivIdealAlong A (GermIdeal.pullback (m := n) (tangentInclusion n 1) J) q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [iterDerivIdealAlong,zero_section_submanifold_derivIdealAlong hA _
      (isCoherent_iterDerivIdealAlong hJ (liftedCarrier_closed_submanifold hA) q),ih,
      iterDerivIdealAlong]

end
end Hironaka.HironakaActualZeroSectionSubmanifoldDifferentials
