/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCentreJointJets

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCentrePrincipalParts
noncomputable section
open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalTaylorCoefficients
  HironakaHolomorphicJetQuotientFrames HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetMonomialSpan HironakaActualCentreJointJets
  HironakaActualHSConstantCentreJetFrames HironakaActualCentreJetFrameCocycle
  HironakaHolomorphicPointJets HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetChartInvariance

/-- Ordinary whole-module algebra: a genuine UNIT pivot plus actual column-killing and row-kernel identities determine the full kernel. -/
private theorem kernel_eq_columns_of_unit_pivot {R a b : Type*} [CommRing R] [Fintype a] [Fintype b]
    (A : Matrix a b R) {k : ℕ} (rows : Fin k → a) (cols : Fin k → b)
    (P : (a → R) →ₗ[R] (a → R)) (hunit : IsUnit (A.submatrix rows cols).det)
    (hkill : ∀ j,P (fun i => A i j)=0)
    (hfix : ∀ v : a → R,(∀ j,v (rows j)=0) → P v=v) :
    LinearMap.ker P=Submodule.span R (range fun j => (fun i => A i j)) := by
  apply le_antisymm
  · intro v hv
    let K := A.submatrix rows cols
    let w := K⁻¹.mulVec (fun j => v (rows j))
    let u : a → R := ∑ j : Fin k,w j • (fun i => A i (cols j))
    have hKw : K.mulVec w=(fun j => v (rows j)) := by
      dsimp only [w]
      rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv K hunit,Matrix.one_mulVec]
    have hurows : ∀ i,u (rows i)=v (rows i) := by
      intro i
      have he : u (rows i)=(K.mulVec w) i := by
        simp only [u,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,K,
          Matrix.mulVec,dotProduct,Matrix.submatrix_apply,mul_comm]
      exact he.trans (congrFun hKw i)
    have hPu : P u=0 := by
      dsimp only [u]
      rw [map_sum]
      simp only [map_smul,hkill,smul_zero,Finset.sum_const_zero]
    have hrows : ∀ j,(v-u) (rows j)=0 := by
      intro j
      change v (rows j)-u (rows j)=0
      rw [hurows,sub_self]
    have he := hfix (v-u) hrows
    have hPv := LinearMap.mem_ker.mp hv
    rw [map_sub,hPv,hPu,sub_zero] at he
    have hvu : v=u := sub_eq_zero.mp he.symm
    rw [hvu]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨cols j,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro v ⟨j,rfl⟩
    exact LinearMap.mem_ker.mpr (hkill j)


/-- Evaluation of the SAME actual matrix entry germ is exactly its original entry at the original point. -/
theorem actualCentreMacaulayGerm_eval (d t q : ℕ) {ι : Type*}
    (H : ι → ComplexModel (d+t) → ℂ) {U : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (h0 : (0 : ComplexModel (d+t)) ∈ U)
    (a : monomialIndex (d+t) q) (b : monomialIndex (d+t) q × ι) :
    HolGerm.eval (actualCentreMacaulayGerm d t q H hU hH h0 a b)=originalMacaulayMatrix q H 0 a b := by
  simp only [actualCentreMacaulayGerm,HolGerm.eval_mk,map_zero]

/-- The actual pivot AT0 is a genuine UNIT over the ORIGINAL tangent germ ring, not a generic nonzero denominator. -/
theorem actualCentreMacaulayGerm_pivot_unit (d t q : ℕ) {ι : Type*}
    (H : ι → ComplexModel (d+t) → ℂ) {U : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (h0 : (0 : ComplexModel (d+t)) ∈ U)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : (pivotMatrix q H rows cols 0).det ≠ 0) :
    IsUnit ((actualCentreMacaulayGerm d t q H hU hH h0).submatrix rows cols).det := by
  apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
  have he : HolGerm.eval.mapMatrix ((actualCentreMacaulayGerm d t q H hU hH h0).submatrix rows cols)=
      pivotMatrix q H rows cols 0 := by
    ext i j
    exact actualCentreMacaulayGerm_eval d t q H hU hH h0 (rows i) (cols j)
  rw [HolGerm.eval.map_det,he]
  exact hdet

/-- The genuine original holomorphic pivot projection has true tangent entry germs on its actual domain through0. -/
theorem actualCentreProjectionEntry_holAt (d t q : ℕ) {ι : Type*}
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (a b : monomialIndex (d+t) q) :
    HolAt (fun c => pivotProjection q H rows cols (tangentInclusion d t c) (Pi.single b 1) a) 0 := by
  have hh : HolAt (fun p => pivotProjection q H rows cols p (Pi.single b 1) a) 0 := by
    filter_upwards [hD.mem_nhds h0D] with p hp
    exact ((pivotProjection_holomorphic_entries q H rows cols hU hH hDU hdet (Pi.single b 1) a) p hp).differentiableAt
      (hD.mem_nhds hp)
  exact eventually_differentiableAt_comp_clm (tangentInclusion d t) hh

/-- The SAME actual pivot projection, lifted entrywise into the ORIGINAL whole tangent germ ring. -/
def actualCentreGermProjection (d t q : ℕ) {ι : Type*}
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0) :
    (monomialIndex (d+t) q → HolGerm (ComplexModel d)) →ₗ[HolGerm (ComplexModel d)]
      (monomialIndex (d+t) q → HolGerm (ComplexModel d)) :=
  Fintype.linearCombination (HolGerm (ComplexModel d)) (fun b a =>
    HolGerm.mk (fun c => pivotProjection q H rows cols (tangentInclusion d t c) (Pi.single b 1) a)
      (actualCentreProjectionEntry_holAt d t q H hU hH hD h0D hDU rows cols hdet a b))

private theorem germ_sum_products {d : ℕ} {ι : Type*} [Fintype ι]
    (F G : ι → ComplexModel d → ℂ) (hF : ∀ i,HolAt (F i) 0) (hG : ∀ i,HolAt (G i) 0)
    (hs : HolAt (fun c => ∑ i,F i c*G i c) 0) :
    (∑ i,HolGerm.mk (F i) (hF i)*HolGerm.mk (G i) (hG i))=
      HolGerm.mk (fun c => ∑ i,F i c*G i c) hs := by
  have hp : ∀ i,HolAt (fun c => F i c*G i c) 0 := fun i => eventually_differentiableAt_mul (hF i) (hG i)
  calc
    _ = ∑ i,HolGerm.mk (fun c => F i c*G i c) (hp i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (HolGerm.mk_mul _ _ _ _).symm
    _ = _ := by
      exact (HolGerm.mk_sum Finset.univ (fun i c => F i c*G i c) hp).symm


private theorem linearMap_coordinate_sum {a : Type*} [Fintype a] [DecidableEq a]
    (L : (a → ℂ) →ₗ[ℂ] (a → ℂ)) (v : a → ℂ) (i : a) :
    (∑ j,v j*L (Pi.single j 1) i)=L v i := by
  have he : (∑ j,v j • Pi.single j (1 : ℂ))=v := by
    funext j
    simp [Pi.single_apply]
  have hh := congrArg (fun w => L w i) he
  simpa only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hh

/-- The actual B-linear projection on ANY original analytic representative tuple is its genuine pointwise projection germ. -/
theorem actualCentreGermProjection_representatives (d t q : ℕ) {ι : Type*}
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (v : monomialIndex (d+t) q → ComplexModel d → ℂ) (hv : ∀ j,HolAt (v j) 0)
    (a : monomialIndex (d+t) q) :
    ∃ hp : HolAt (fun c => pivotProjection q H rows cols (tangentInclusion d t c) (fun j => v j c) a) 0,
      actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet
          (fun j => HolGerm.mk (v j) (hv j)) a=
        HolGerm.mk (fun c => pivotProjection q H rows cols (tangentInclusion d t c) (fun j => v j c) a) hp := by
  let F : monomialIndex (d+t) q → ComplexModel d → ℂ := fun j c =>
    pivotProjection q H rows cols (tangentInclusion d t c) (Pi.single j 1) a
  have hF : ∀ j,HolAt (F j) 0 :=
    fun j => actualCentreProjectionEntry_holAt d t q H hU hH hD h0D hDU rows cols hdet a j
  have hprod : ∀ j,HolAt (fun c => v j c*F j c) 0 :=
    fun j => eventually_differentiableAt_mul (hv j) (hF j)
  have hs : HolAt (fun c => ∑ j,v j c*F j c) 0 :=
    eventually_differentiableAt_sum Finset.univ hprod
  have he : (fun c => ∑ j,v j c*F j c)=
      (fun c => pivotProjection q H rows cols (tangentInclusion d t c) (fun j => v j c) a) := by
    funext c
    exact linearMap_coordinate_sum _ _ _
  have hp : HolAt (fun c => pivotProjection q H rows cols (tangentInclusion d t c) (fun j => v j c) a) 0 := by
    rw [← he]
    exact hs
  refine ⟨hp,?_⟩
  dsimp only [actualCentreGermProjection]
  rw [Fintype.linearCombination_apply,Finset.sum_apply]
  simp only [Pi.smul_apply,smul_eq_mul]
  change (∑ j,HolGerm.mk (v j) (hv j)*HolGerm.mk (F j) (hF j))=_
  rw [germ_sum_products v F hv hF hs]
  exact HolGerm.mk_eq_mk_iff.mpr (Filter.EventuallyEq.of_eq he)


/-- The lifted genuine projection fixes the ENTIRE original tangent-germ row kernel. -/
theorem actualCentreGermProjection_fixes_row_kernel (d t q : ℕ) {ι : Type*}
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0) :
    ∀ v : monomialIndex (d+t) q → HolGerm (ComplexModel d),
      (∀ j,v (rows j)=0) → actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet v=v := by
  intro v hrows
  choose f hf he using fun j => HolGerm.exists_eq_mk (v j)
  have hv : v=(fun j => HolGerm.mk (f j) (hf j)) := funext he
  have hrow : ∀ j,f (rows j) =ᶠ[𝓝 (0 : ComplexModel d)] (fun _ => 0) := by
    intro j
    have hz : HolGerm.mk (f (rows j)) (hf (rows j))=0 := (he (rows j)).symm.trans (hrows j)
    exact HolGerm.mk_eq_mk_iff.mp (hz.trans HolGerm.mk_zero.symm)
  rw [hv]
  funext a
  obtain ⟨hp,ha⟩ := actualCentreGermProjection_representatives d t q H hU hH hD h0D hDU rows cols hdet f hf a
  rw [ha]
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards [eventually_all.mpr hrow] with c hc
  apply congrFun (pivotProjection_eq_self q H rows cols (tangentInclusion d t c) (fun j => f j c) ?_) a
  change (fun j : Fin k => f (rows j) c)=0
  funext j
  exact hc j

/-- Source centre rank constancy makes the lifted original projection kill EVERY entire original Macaulay column germ. -/
theorem actualCentreGermProjection_kills_columns (d t q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k) :
    ∀ b,actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet
      (fun a => actualCentreMacaulayGerm d t q H hU hH (hDU h0D) a b)=0 := by
  intro b
  funext a
  let v : monomialIndex (d+t) q → ComplexModel d → ℂ :=
    fun j c => originalMacaulayMatrix q H (tangentInclusion d t c) j b
  have hv : ∀ j,HolAt (v j) 0 := fun j => actualCentreMacaulayEntry_holAt d t q H hU hH (hDU h0D) j b
  obtain ⟨hp,ha⟩ := actualCentreGermProjection_representatives d t q H hU hH hD h0D hDU rows cols hdet v hv a
  change actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet
    (fun j => HolGerm.mk (v j) (hv j)) a=0
  rw [ha,← HolGerm.mk_zero]
  apply HolGerm.mk_eq_mk_iff.mpr
  have hT : Tendsto (tangentInclusion d t) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (tangentInclusion d t).continuous.tendsto (0 : ComplexModel d)
  filter_upwards [hT.eventually (hD.mem_nhds h0D)] with c hc
  have hcol : (fun j => originalMacaulayMatrix q H (tangentInclusion d t c) j b) ∈
      LinearMap.range (originalMacaulayLinearMap q H (tangentInclusion d t c)) := by
    rw [originalMacaulayLinearMap,Fintype.range_linearCombination]
    exact Submodule.subset_span ⟨b,rfl⟩
  rw [← ker_pivotProjection_eq_entire_image q H rows cols (tangentInclusion d t c)
    (hdet _ hc) (hrank _ hc (tangentInclusion_mem_plane d t c))] at hcol
  exact congrFun (LinearMap.mem_ker.mp hcol) a


/-- The ENTIRE lifted actual projection kernel is exactly the SAME original Macaulay column span over B. -/
theorem actualCentreGermProjection_kernel (d t q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k) :
    LinearMap.ker (actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet)=
      Submodule.span (HolGerm (ComplexModel d))
        (range fun b => (fun a => actualCentreMacaulayGerm d t q H hU hH (hDU h0D) a b)) := by
  exact kernel_eq_columns_of_unit_pivot (actualCentreMacaulayGerm d t q H hU hH (hDU h0D)) rows cols _
    (actualCentreMacaulayGerm_pivot_unit d t q H hU hH (hDU h0D) rows cols (hdet 0 h0D))
    (actualCentreGermProjection_kills_columns d t q H hU hH hD h0D hDU rows cols hdet hrank)
    (actualCentreGermProjection_fixes_row_kernel d t q H hU hH hD h0D hDU rows cols hdet)

/-- The SAME original finite joint ideal is literally spanned by actual whole pullbacks of original holomorphic generators. -/
def actualCentreJointIdeal (d t : ℕ) {ι : Type*}
    (H : ι → ComplexModel (d+t) → ℂ) (hH0 : ∀ i,HolAt (H i) 0) :
    Ideal (HolGerm (ComplexModel (d+(d+t)))) :=
  Ideal.span (range fun i => actualCentreJointPullback d t (HolGerm.mk (H i) (hH0 i)))

/-- Genuine whole ideal-image identification, with the SAME actual columns and no full independent word-array replacement. -/
theorem actualCentreJointIdeal_image (d t q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) {U : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (h0 : (0 : ComplexModel (d+t)) ∈ U)
    (hH0 : ∀ i,HolAt (H i) 0) :
    let := tangentAlgebra d (d+t)
    ((actualCentreJointIdeal d t H hH0).restrictScalars (HolGerm (ComplexModel d))).map
      (actualJointScalarJet d (d+t) q)=Submodule.span (HolGerm (ComplexModel d))
        (range fun b => (fun a => actualCentreMacaulayGerm d t q H hU hH h0 a b)) := by
  let := tangentAlgebra d (d+t)
  dsimp only
  calc
    _ = Submodule.span (HolGerm (ComplexModel d))
        (range fun b : monomialIndex (d+t) q × ι => actualJointScalarJet d (d+t) q
          (normalWord d (d+t) b.1*actualCentreJointPullback d t (HolGerm.mk (H b.2) (hH0 b.2)))) :=
      actualJointScalarJet_ideal_image d (d+t) q (fun i => actualCentreJointPullback d t (HolGerm.mk (H i) (hH0 i)))
    _ = _ := by
      apply congrArg (Submodule.span (HolGerm (ComplexModel d)))
      apply congrArg Set.range
      funext b
      exact actualJointScalarJet_column_dictionary d t q H hU hH h0 hH0 b


/-- True selected-row evaluation over the unchanged original tangent germ ring. -/
def actualCentreGermRowMap (d n q : ℕ) {k : ℕ} (rows : Fin k → monomialIndex n q) :
    (monomialIndex n q → HolGerm (ComplexModel d)) →ₗ[HolGerm (ComplexModel d)]
      (Fin k → HolGerm (ComplexModel d)) where
  toFun v j := v (rows j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual lifted original pivot projection has ZERO entire selected rows for EVERY original tangent-germ tuple. -/
theorem actualCentreGermProjection_row_zero (d t q : ℕ) {ι : Type*}
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (v : monomialIndex (d+t) q → HolGerm (ComplexModel d)) :
    actualCentreGermRowMap d (d+t) q rows
      (actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet v)=0 := by
  choose f hf he using fun j => HolGerm.exists_eq_mk (v j)
  have hv : v=(fun j => HolGerm.mk (f j) (hf j)) := funext he
  rw [hv]
  funext j
  change actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet
    (fun j => HolGerm.mk (f j) (hf j)) (rows j)=0
  obtain ⟨hp,ha⟩ := actualCentreGermProjection_representatives d t q H hU hH hD h0D hDU rows cols hdet f hf (rows j)
  rw [ha,← HolGerm.mk_zero]
  apply HolGerm.mk_eq_mk_iff.mpr
  have hT : Tendsto (tangentInclusion d t) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (tangentInclusion d t).continuous.tendsto (0 : ComplexModel d)
  filter_upwards [hT.eventually (hD.mem_nhds h0D)] with c hc
  exact congrFun (rowMap_pivotProjection_eq_zero q H rows cols (tangentInclusion d t c)
    (hdet _ hc) (fun a => f a c)) j

/-- The genuine model is the TRUE whole joint-word-jet image intersected with selected-row kernel; repeated word relations are retained. -/
def actualCentrePrincipalPartsModel (d t q : ℕ) {k : ℕ}
    (rows : Fin k → monomialIndex (d+t) q) :
    Submodule (HolGerm (ComplexModel d)) (monomialIndex (d+t) q → HolGerm (ComplexModel d)) :=
  letI := tangentAlgebra d (d+t)
  LinearMap.range (actualJointScalarJet d (d+t) q) ⊓ LinearMap.ker (actualCentreGermRowMap d (d+t) q rows)

/-- The actual projection preserves the TRUE original joint-jet image, by its ENTIRE ideal kernel, and lands in the genuine model. -/
theorem actualCentreGermProjection_mem_model (d t q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U) (hH0 : ∀ i,HolAt (H i) 0)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k) :
    let := tangentAlgebra d (d+t)
    ∀ v,v ∈ LinearMap.range (actualJointScalarJet d (d+t) q) →
      actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet v ∈
        actualCentrePrincipalPartsModel d t q rows := by
  let := tangentAlgebra d (d+t)
  dsimp only
  intro v hv
  let P := actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet
  let T := actualJointScalarJet d (d+t) q
  have he : ((actualCentreJointIdeal d t H hH0).restrictScalars (HolGerm (ComplexModel d))).map T=LinearMap.ker P :=
    (actualCentreJointIdeal_image d t q H hU hH (hDU h0D) hH0).trans
      (actualCentreGermProjection_kernel d t q H hU hH hD h0D hDU rows cols hdet hrank).symm
  have hker : LinearMap.ker P ≤ LinearMap.range T := by
    rw [← he]
    rintro w ⟨g,_hg,rfl⟩
    exact LinearMap.mem_range_self T g
  have hrow := actualCentreGermProjection_row_zero d t q H hU hH hD h0D hDU rows cols hdet v
  have hfix : P (P v)=P v := actualCentreGermProjection_fixes_row_kernel d t q H hU hH hD h0D hDU rows cols hdet
    (P v) (fun j => congrFun hrow j)
  have hz : P (v-P v)=0 := by rw [map_sub,hfix,sub_self]
  have hrem : v-P v ∈ LinearMap.range T := hker (LinearMap.mem_ker.mpr hz)
  have hm := Submodule.sub_mem (LinearMap.range T) hv hrem
  have hh : v-(v-P v)=P v := by abel
  rw [hh] at hm
  exact ⟨hm,LinearMap.mem_ker.mpr hrow⟩


/-- True whole original coordinates, restricted to the TRUE joint-jet image and exact selected-row kernel. -/
def actualCentrePrincipalPartsCoordinates (d t q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U) (hH0 : ∀ i,HolAt (H i) 0)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k) :
    letI := tangentAlgebra d (d+t)
    HolGerm (ComplexModel (d+(d+t))) →ₗ[HolGerm (ComplexModel d)] actualCentrePrincipalPartsModel d t q rows :=
  letI := tangentAlgebra d (d+t)
  ((actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet).comp
    (actualJointScalarJet d (d+t) q)).codRestrict _
      (fun g => actualCentreGermProjection_mem_model d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank
        _ (LinearMap.mem_range_self _ g))

/-- The ENTIRE original whole principal-parts coordinate kernel is exactly J+N_z^q. -/
theorem ker_actualCentrePrincipalPartsCoordinates (d t q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U) (hH0 : ∀ i,HolAt (H i) 0)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k) :
    let := tangentAlgebra d (d+t)
    LinearMap.ker (actualCentrePrincipalPartsCoordinates d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank)=
      (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ q).restrictScalars (HolGerm (ComplexModel d)) := by
  let := tangentAlgebra d (d+t)
  dsimp only
  have he : LinearMap.ker (actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet)=
      ((actualCentreJointIdeal d t H hH0).restrictScalars (HolGerm (ComplexModel d))).map (actualJointScalarJet d (d+t) q) :=
    (actualCentreGermProjection_kernel d t q H hU hH hD h0D hDU rows cols hdet hrank).trans
      (actualCentreJointIdeal_image d t q H hU hH (hDU h0D) hH0).symm
  rw [actualCentrePrincipalPartsCoordinates,LinearMap.ker_codRestrict,LinearMap.ker_comp,he,
    Submodule.comap_map_eq,ker_actualJointScalarJet]
  exact (Submodule.restrictScalars_sup (HolGerm (ComplexModel d))
    (actualCentreJointIdeal d t H hH0) (normalIdeal d (d+t) ^ q)).symm

/-- Surjectivity is onto the TRUE original model: use its original whole-jet preimage, not an arbitrary independent word vector. -/
theorem actualCentrePrincipalPartsCoordinates_surjective (d t q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U) (hH0 : ∀ i,HolAt (H i) 0)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k) :
    let := tangentAlgebra d (d+t)
    Function.Surjective (actualCentrePrincipalPartsCoordinates d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank) := by
  let := tangentAlgebra d (d+t)
  dsimp only
  intro v
  obtain ⟨g,hg⟩ := v.2.1
  refine ⟨g,Subtype.ext ?_⟩
  change actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet
    (actualJointScalarJet d (d+t) q g)=v.val
  rw [hg]
  exact actualCentreGermProjection_fixes_row_kernel d t q H hU hH hD h0D hDU rows cols hdet v.val
    (fun j => congrFun (LinearMap.mem_ker.mp v.2.2) j)

/-- The ENTIRE ORIGINAL joint principal-parts quotient, with its genuine B-action, has the actual whole coordinate equivalence. -/
def actualCentrePrincipalPartsFrame (d t q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U) (hH0 : ∀ i,HolAt (H i) 0)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k) :
    letI := tangentAlgebra d (d+t)
    (HolGerm (ComplexModel (d+(d+t))) ⧸ (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ q))
      ≃ₗ[HolGerm (ComplexModel d)] actualCentrePrincipalPartsModel d t q rows :=
  letI := tangentAlgebra d (d+t)
  (Submodule.quotEquivOfEq _ _
    (ker_actualCentrePrincipalPartsCoordinates d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank).symm).trans
      ((actualCentrePrincipalPartsCoordinates d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank).quotKerEquivOfSurjective
        (actualCentrePrincipalPartsCoordinates_surjective d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank))

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY original geometry, coherence and ALL intrinsic HS constancy supply SAME original generators before ALL orders and true whole B-module principal-parts frames. -/
theorem exists_original_hs_constant_centre_whole_principal_parts
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C,∀ ℓ : ℕ,hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ (O : Set M), IsOpen O ∧ x ∈ O ∧ ∃ (N : ℕ) (G : Fin N → M → ℂ),
        (∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (G i) O) ∧
        (∀ y ∈ O,∀ g,A.mem y g ↔ IsInSpanAt (n := d+t) (· ∈ range G) y g) ∧
      ∃ (U : Set (ComplexModel (d+t))), ∃ hU : IsOpen U,∃ h0U : (0 : ComplexModel (d+t)) ∈ U,∃ _hUT : U ⊆ Φ.target,
        MapsTo (actualFlatteningInverseMap x Φ) U O ∧
        let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
        ∃ hH : ∀ i,DifferentiableOn ℂ (H i) U,
        ∃ hhol : ∀ p ∈ U,∀ i,HolAt (H i) p,
          (∀ p (hp : p ∈ U),originalCoherentOriginIdeal
            (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) p)=translatedIdeal H p (hhol p hp)) ∧
          (∀ p (_hp : p ∈ U) (ℓ : ℕ),
            hilbertSamuelAt A (actualFlatteningInverseMap x Φ p) ℓ=
              Module.finrank ℂ (LinearMap.range (finiteJet (n := d+t) (ℓ+1)))-
                Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))) ∧
          (∀ p ∈ U,p ∈ complexCoordinatePlane (d+t) d → ∀ ℓ : ℕ,
            Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))=
              Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H 0))) ∧
          ∃ hH0 : ∀ i,HolAt (H i) 0,
          ∀ ℓ : ℕ,∃ (k : ℕ) (rows : Fin k → monomialIndex (d+t) (ℓ+1))
            (cols : Fin k → monomialIndex (d+t) (ℓ+1) × Fin N),
            k=Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H 0)) ∧
            ∃ D : Set (ComplexModel (d+t)),∃ hD : IsOpen D,∃ h0D : (0 : ComplexModel (d+t)) ∈ D,
            ∃ hDU : D ⊆ U,
              IsOpen ((tangentInclusion d t) ⁻¹' D) ∧ (0 : ComplexModel d) ∈ (tangentInclusion d t) ⁻¹' D ∧
            ∃ hdet : ∀ p ∈ D,(pivotMatrix (ℓ+1) H rows cols p).det ≠ 0,
            ∃ hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
              Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))=k,
              IsUnit ((actualCentreMacaulayGerm d t (ℓ+1) H hU hH h0U).submatrix rows cols).det ∧
              letI := tangentAlgebra d (d+t)
              LinearMap.ker (actualCentrePrincipalPartsCoordinates d t (ℓ+1) H hU hH hD h0D hDU hH0 rows cols hdet hrank)=
                (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ (ℓ+1)).restrictScalars (HolGerm (ComplexModel d)) ∧
              Function.Surjective (actualCentrePrincipalPartsCoordinates d t (ℓ+1) H hU hH hD h0D hDU hH0 rows cols hdet hrank) ∧
              Nonempty ((HolGerm (ComplexModel (d+(d+t))) ⧸
                  (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ (ℓ+1)))
                ≃ₗ[HolGerm (ComplexModel d)] actualCentrePrincipalPartsModel d t (ℓ+1) rows) := by
  obtain ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hHS,hR,hpiv⟩ :=
    exists_original_hs_constant_centre_origin_pivot_frames C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  let hH0 : ∀ i,HolAt (H i) 0 := hhol 0 h0U
  refine ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hHS,hR,hH0,?_⟩
  intro ℓ
  obtain ⟨k,rows,cols,hk,D,hD,h0D,hDU,hV,h0V,hdet,_hproj,_hframes⟩ := hpiv ℓ
  have hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))=k := by
    intro p hp hplane
    exact (hR p (hDU hp) hplane ℓ).trans hk.symm
  refine ⟨k,rows,cols,hk,D,hD,h0D,hDU,hV,h0V,hdet,hrank,?_,?_⟩
  · exact actualCentreMacaulayGerm_pivot_unit d t (ℓ+1) H hU hH h0U rows cols (hdet 0 h0D)
  · let := tangentAlgebra d (d+t)
    exact ⟨ker_actualCentrePrincipalPartsCoordinates d t (ℓ+1) H hU hH hD h0D hDU hH0 rows cols hdet hrank,
      actualCentrePrincipalPartsCoordinates_surjective d t (ℓ+1) H hU hH hD h0D hDU hH0 rows cols hdet hrank,
      ⟨actualCentrePrincipalPartsFrame d t (ℓ+1) H hU hH hD h0D hDU hH0 rows cols hdet hrank⟩⟩

end OriginalCentre

end
end Hironaka.HironakaActualCentrePrincipalParts
