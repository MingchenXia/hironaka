/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeGeometry
import Hironaka.Resolution.HironakaSmoothSubmersionComposition
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionRegularityReflection
noncomputable section
open Hironaka.BlowupSequences RegularAtDimTransport SimultaneousNormalCrossings
  NormalCrossings HironakaSmoothSubmersionNormalCrossings

private def linearCoordinates {r : ℕ} (L : ComplexModel r ≃L[ℂ] ComplexModel r) :
    LocalHolomorphicEquivAt (n := r) 0 where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := L
  invFun := L.symm
  toFun_holomorphic := L.differentiable.differentiableOn
  invFun_holomorphic := L.symm.differentiable.differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => L.symm_apply_apply _
  right_inv := fun _ _ => L.apply_symm_apply _

/-- Actual saturation by vertical fibres internally gives normal coordinates
whose literal vertical coordinates are retained. -/
theorem exists_vertical_preserving_normal_coordinates {n t : ℕ}
    (Ξ : LocalHolomorphicEquivAt (n := n+t) 0) (S : Finset (Fin (n+t)))
    (hvertical : ∀ u ∈ Ξ.source,
      (∀ i : Fin (n+t), i.val < n → u i = 0) → Ξ.toFun u ∈ coordSubspace S) :
    ∃ X : Finset (Fin (n+t)), ∃ Ψ : LocalHolomorphicEquivAt (n := n+t) 0,
      (∀ i ∈ X, i.val < n) ∧ X.card = S.card ∧ Ψ.source ⊆ Ξ.source ∧ Ψ.toFun 0 = 0 ∧
      (∀ u ∈ Ψ.source, Ξ.toFun u ∈ coordSubspace S ↔ Ψ.toFun u ∈ coordSubspace X) ∧
      ∀ u ∈ Ψ.source, ∀ i ∉ X, Ψ.toFun u i = u i := by
  classical
  let Y := Finset.univ.filter (fun i : Fin (n+t) => i.val < n)
  have hYS : ∀ u ∈ Ξ.source, u ∈ coordSubspace Y → Ξ.toFun u ∈ coordSubspace S := by
    intro u hu hv
    exact hvertical u hu (fun i hi => hv i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩))
  obtain ⟨X,σ,Φ,hXY,_havoid,hsrc,hσ,hcoord⟩ :=
    exists_model_coords (ι := Empty) Ξ Y S ∅ Empty.elim Empty.elim
      (by simp) (by simp) hYS
  have hΦ0 : Φ.toFun 0 = 0 := by
    ext r
    obtain ⟨i,rfl⟩ := σ.surjective r
    by_cases hi : i ∈ X
    · exact (hcoord 0 Φ.center_mem_source).2.1.mp (hYS 0 (hsrc Φ.center_mem_source) (fun _ _ => by simp)) _ ((hσ i).mpr hi)
    · simpa using (hcoord 0 Φ.center_mem_source).2.2 i hi
  let L : ComplexModel (n+t) ≃L[ℂ] ComplexModel (n+t) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ.symm).toContinuousLinearEquiv
  have happ (u : ComplexModel (n+t)) (i : Fin (n+t)) : L u i = u (σ i) := by
    simp [L,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
  let Ψ := LocalHolomorphicEquivAt.comp Φ (linearCoordinates L) hΦ0
  have hXcard : X.card = S.card := by
    have hset : X.map σ.toEmbedding = Finset.univ.filter
        (fun i : Fin (n+t) => n+t-S.card ≤ i.val) := by
      ext i
      simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact (hσ a).mpr ha
      · intro hi
        exact ⟨σ.symm i,(hσ (σ.symm i)).mp (by simpa using hi),σ.apply_symm_apply i⟩
    have hScard : S.card ≤ n+t := by simpa using Finset.card_le_univ S
    have hcount := card_filter_le_lt (n := n+t) (a := n+t-S.card) (b := n+t) le_rfl
    have he : (Finset.univ.filter (fun i : Fin (n+t) => n+t-S.card ≤ i.val)) =
        Finset.univ.filter (fun i : Fin (n+t) => n+t-S.card ≤ i.val ∧ i.val < n+t) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,i.isLt,and_true]
    rw [← Finset.card_map σ.toEmbedding, hset, he, hcount]
    omega
  refine ⟨X,Ψ,(fun i hi => (Finset.mem_filter.mp (hXY hi)).2),hXcard,
    fun u hu => hsrc hu.1,?_,?_,?_⟩
  · change L (Φ.toFun 0) = 0
    rw [hΦ0,map_zero]
  · intro u hu
    have hd := (hcoord u hu.1).2.1
    change Ξ.toFun u ∈ coordSubspace S ↔ L (Φ.toFun u) ∈ coordSubspace X
    rw [hd]
    constructor
    · intro h i hi
      rw [happ]
      exact h (σ i) ((hσ i).mpr hi)
    · intro h i hi
      obtain ⟨a,rfl⟩ := σ.surjective i
      have ha := (hσ a).mp hi
      simpa only [happ] using h a ha
  · intro u hu i hi
    change L (Φ.toFun u) i = u i
    rw [happ]
    exact (hcoord u hu.1).2.2 i hi

private def horizontalInclusion (n t : ℕ) : ComplexModel n →L[ℂ] ComplexModel (n+t) :=
  EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ (ComplexModel n) (ComplexModel t))

private def horizontalProjection (n t : ℕ) : ComplexModel (n+t) →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel t)).comp
    EuclideanSpace.finAddEquivProd.toContinuousLinearMap

private theorem projection_inclusion (n t : ℕ) (u : ComplexModel n) :
    horizontalProjection n t (horizontalInclusion n t u) = u := by
  change (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd.symm (u,0))).1 = u
  rw [EuclideanSpace.finAddEquivProd.apply_symm_apply]

private theorem horizontal_of_vertical_zero {n t : ℕ} (w : ComplexModel (n+t))
    (hw : (EuclideanSpace.finAddEquivProd (n := n) (m := t) w).2 = 0) :
    horizontalInclusion n t (horizontalProjection n t w) = w := by
  apply EuclideanSpace.finAddEquivProd.injective
  change EuclideanSpace.finAddEquivProd
    (EuclideanSpace.finAddEquivProd.symm ((EuclideanSpace.finAddEquivProd w).1,0)) = _
  rw [EuclideanSpace.finAddEquivProd.apply_symm_apply]
  exact Prod.ext rfl hw.symm

/-- A genuine vertical-preserving coordinate chart internally restricts to
actual horizontal source/target and two holomorphic inverse maps. -/
def horizontalSliceCoordinates {n t : ℕ}
    (Ψ : LocalHolomorphicEquivAt (n := n+t) 0) (_hΨ0 : Ψ.toFun 0 = 0)
    (hvertical : ∀ u ∈ Ψ.source,
      (EuclideanSpace.finAddEquivProd (n := n) (m := t) (Ψ.toFun u)).2 =
        (EuclideanSpace.finAddEquivProd u).2) :
    LocalHolomorphicEquivAt (n := n) 0 := by
  let inc := horizontalInclusion n t
  let pr := horizontalProjection n t
  have hforward (u : ComplexModel n) (hu : inc u ∈ Ψ.source) :
      inc (pr (Ψ.toFun (inc u))) = Ψ.toFun (inc u) := by
    apply horizontal_of_vertical_zero
    rw [hvertical _ hu]
    change (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd.symm (u,0))).2 = 0
    rw [EuclideanSpace.finAddEquivProd.apply_symm_apply]
  have hbackward (u : ComplexModel n) (hu : inc u ∈ Ψ.target) :
      inc (pr (Ψ.invFun (inc u))) = Ψ.invFun (inc u) := by
    apply horizontal_of_vertical_zero
    have h := hvertical (Ψ.invFun (inc u)) (Ψ.mapsTo_invFun hu)
    rw [Ψ.right_inv _ hu] at h
    change (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd.symm (u,0))).2 = _ at h
    rw [EuclideanSpace.finAddEquivProd.apply_symm_apply] at h
    exact h.symm
  refine {
    source := inc ⁻¹' Ψ.source
    target := inc ⁻¹' Ψ.target
    isOpen_source := Ψ.isOpen_source.preimage inc.continuous
    isOpen_target := Ψ.isOpen_target.preimage inc.continuous
    center_mem_source := by simpa only [mem_preimage,map_zero] using Ψ.center_mem_source
    toFun := fun u => pr (Ψ.toFun (inc u))
    invFun := fun u => pr (Ψ.invFun (inc u))
    toFun_holomorphic := pr.differentiable.comp_differentiableOn
      (Ψ.toFun_holomorphic.comp inc.differentiableOn (fun _ hu => hu))
    invFun_holomorphic := pr.differentiable.comp_differentiableOn
      (Ψ.invFun_holomorphic.comp inc.differentiableOn (fun _ hu => hu))
    mapsTo_toFun := ?_
    mapsTo_invFun := ?_
    left_inv := ?_
    right_inv := ?_ }
  · intro u hu
    change inc (pr (Ψ.toFun (inc u))) ∈ Ψ.target
    rw [hforward u hu]
    exact Ψ.mapsTo_toFun hu
  · intro u hu
    change inc (pr (Ψ.invFun (inc u))) ∈ Ψ.source
    rw [hbackward u hu]
    exact Ψ.mapsTo_invFun hu
  · intro u hu
    rw [hforward u hu,Ψ.left_inv _ hu]
    exact projection_inclusion n t u
  · intro u hu
    rw [hbackward u hu,Ψ.right_inv _ hu]
    exact projection_inclusion n t u

 theorem horizontalSliceCoordinates_zero {n t : ℕ}
    (Ψ : LocalHolomorphicEquivAt (n := n+t) 0) (hΨ0 : Ψ.toFun 0 = 0)
    (hvertical : ∀ u ∈ Ψ.source,
      (EuclideanSpace.finAddEquivProd (n := n) (m := t) (Ψ.toFun u)).2 =
        (EuclideanSpace.finAddEquivProd u).2) :
    (horizontalSliceCoordinates Ψ hΨ0 hvertical).toFun 0 = 0 := by
  change horizontalProjection n t (Ψ.toFun (horizontalInclusion n t 0)) = 0
  rw [map_zero,hΨ0,map_zero]

/-- Every actual cylinder flattening internally supplies a target flattening,
with the exact fibre-dimension subtraction. -/
theorem regularAtDim_of_cylinder_flattening {n t j : ℕ} (A : Set (ComplexModel n))
    (hj : j ≤ n+t) (Ξ : LocalHolomorphicEquivAt (n := n+t) 0)
    (hA : ∀ u ∈ Ξ.source, horizontalProjection n t u ∈ A ↔
      Ξ.toFun u ∈ complexCoordinatePlane (n+t) j) (h0A : (0 : ComplexModel n) ∈ A) :
    t ≤ j ∧ RegularAtDim (n := n) A 0 (j-t) := by
  classical
  let S := Finset.univ.filter (fun i : Fin (n+t) => j ≤ i.val)
  have hS : S.card = n+t-j := by
    have he : S = Finset.univ.filter (fun i : Fin (n+t) => j ≤ i.val ∧ i.val < n+t) := by
      ext i
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,i.isLt,and_true]
    rw [he,card_filter_le_lt le_rfl]
  have hvertical : ∀ u ∈ Ξ.source,
      (∀ i : Fin (n+t), i.val < n → u i = 0) → Ξ.toFun u ∈ coordSubspace S := by
    intro u hu hv
    have hpr : horizontalProjection n t u = 0 := by
      ext r
      change (EuclideanSpace.finAddEquivProd u).1 r = 0
      simpa [EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,
        LinearIsometryEquiv.piLpCongrLeft_apply] using hv (Fin.castAdd t r) r.isLt
    have hplane := (hA u hu).mp (hpr ▸ h0A)
    simpa only [S,coordSubspace_eq_complexCoordinatePlane] using hplane
  obtain ⟨X,Ψ,hX,hcard,hsrc,hΨ0,hnormal,hretain⟩ :=
    exists_vertical_preserving_normal_coordinates Ξ S hvertical
  have hblock : ∀ u ∈ Ψ.source,
      (EuclideanSpace.finAddEquivProd (n := n) (m := t) (Ψ.toFun u)).2 =
        (EuclideanSpace.finAddEquivProd u).2 := by
    intro u hu
    ext r
    have hnot : Fin.natAdd n r ∉ X := by
      intro hr
      have hlt := hX _ hr
      change n+r.val < n at hlt
      omega
    simpa [EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,
      LinearIsometryEquiv.piLpCongrLeft_apply] using hretain u hu (Fin.natAdd n r) hnot
  let Θ := horizontalSliceCoordinates Ψ hΨ0 hblock
  let X₀ := Finset.univ.filter (fun i : Fin n => Fin.castAdd t i ∈ X)
  have hmap : X₀.map (Fin.castAddEmb t) = X := by
    ext i
    simp only [Finset.mem_map,X₀,Finset.mem_filter,Finset.mem_univ,true_and,Fin.castAddEmb_apply]
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro hi
      exact ⟨⟨i.val,hX i hi⟩,hi,Fin.ext rfl⟩
  have hc : X₀.card = n+t-j := by
    rw [← Finset.card_map (Fin.castAddEmb t),hmap,hcard,hS]
  have hcn : X₀.card ≤ n := by simpa using Finset.card_le_univ X₀
  have htj : t ≤ j := by omega
  obtain ⟨σ,hσ⟩ := exists_perm_nested (X := X₀) (Y := X₀) subset_rfl
  let L : ComplexModel n ≃L[ℂ] ComplexModel n :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ).toContinuousLinearEquiv
  have happ (u : ComplexModel n) (i : Fin n) : L u (σ i) = u i := by
    simp [L,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
  let Ω := LocalHolomorphicEquivAt.comp Θ (linearCoordinates L)
    (horizontalSliceCoordinates_zero Ψ hΨ0 hblock)
  have hdim : n-X₀.card = j-t := by omega
  refine ⟨htj,hdim ▸ ?_⟩
  refine ⟨Nat.sub_le _ _,h0A,Ω,(fun _ _ => mem_univ _),?_,?_⟩
  · change L (Θ.toFun 0) = 0
    rw [horizontalSliceCoordinates_zero Ψ hΨ0 hblock,map_zero]
  · intro u _ hu
    have hΨu : horizontalInclusion n t u ∈ Ψ.source := hu.1
    have hΞu := hsrc hΨu
    have h := (hA (horizontalInclusion n t u) hΞu).trans
      (by simpa only [S,coordSubspace_eq_complexCoordinatePlane] using
        hnormal (horizontalInclusion n t u) hΨu)
    rw [projection_inclusion] at h
    change u ∈ A ↔ L (Θ.toFun u) ∈ complexCoordinatePlane n (n-X₀.card)
    rw [h]
    constructor
    · intro hv r hr
      obtain ⟨i,rfl⟩ := σ.surjective r
      rw [happ]
      change (EuclideanSpace.finAddEquivProd (Ψ.toFun (horizontalInclusion n t u))).1 i = 0
      have hi : Fin.castAdd t i ∈ X := (Finset.mem_filter.mp ((hσ i).1.mp hr)).2
      simpa [EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,
        LinearIsometryEquiv.piLpCongrLeft_apply] using hv (Fin.castAdd t i) hi
    · intro hv r hr
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp (hmap.symm ▸ hr)
      have h := hv (σ i) ((hσ i).1.mpr hi)
      rw [happ] at h
      change (EuclideanSpace.finAddEquivProd (Ψ.toFun (horizontalInclusion n t u))).1 i = 0 at h
      simpa [EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,
        LinearIsometryEquiv.piLpCongrLeft_apply] using h

/-- Regularity of the literal full product cylinder reflects to its original
base, with no target normal equations or reflected regularity premise. -/
theorem regularAtDim_cylinder_reflection {n t j : ℕ} (A : Set (ComplexModel n))
    (h : RegularAtDim (n := n+t) (horizontalProjection n t ⁻¹' A) 0 j) :
    t ≤ j ∧ RegularAtDim (n := n) A 0 (j-t) := by
  obtain ⟨hj,hmem,Ξ,_hsrc,_h0,hflat⟩ := h
  apply regularAtDim_of_cylinder_flattening A hj Ξ
  · intro u hu
    simpa [complexChartAt,chartAt_self_eq] using hflat (mem_univ u) hu
  · simpa only [mem_preimage,map_zero] using hmem

private def inverseCoordinates {r : ℕ} {p : ComplexModel r}
    (Φ : LocalHolomorphicEquivAt (n := r) p) (h0 : Φ.toFun p = 0) :
    LocalHolomorphicEquivAt (n := r) 0 where
  source := Φ.target
  target := Φ.source
  isOpen_source := Φ.isOpen_target
  isOpen_target := Φ.isOpen_source
  center_mem_source := h0 ▸ Φ.mapsTo_toFun Φ.center_mem_source
  toFun := Φ.invFun
  invFun := Φ.toFun
  toFun_holomorphic := Φ.invFun_holomorphic
  invFun_holomorphic := Φ.toFun_holomorphic
  mapsTo_toFun := Φ.mapsTo_invFun
  mapsTo_invFun := Φ.mapsTo_toFun
  left_inv := Φ.right_inv
  right_inv := Φ.left_inv

/-- A genuine original submersion reflects regularity of the WHOLE original
preimage, with its actual fibre dimension and no target flattening premise. -/
theorem regularAtDim_of_preimage_submersion {n m : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
    {A : Set X} {j : ℕ} (hA : RegularAtDim (n := m) (f ⁻¹' A) y j) :
    m-n ≤ j ∧ RegularAtDim (n := n) A (f y) (j-(m-n)) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le
    (HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt hf)
  have ht : n+t-n = t := by omega
  rw [ht]
  obtain ⟨hj,hymem,Φs,hΦssrc,hΦs0,hΦsflat⟩ := hA
  let e := chartAt (ComplexModel (n+t)) y
  let e' := chartAt (ComplexModel n) (f y)
  let Φ := HironakaSmoothSubmersionComposition.centeredCoordinates (n := n) (f y)
  have hΦ0 : Φ.toFun (e' (f y)) = 0 :=
    HironakaSmoothSubmersionComposition.centeredCoordinates_zero (n := n) (f y)
  let Λ := liftedCoordinatesAdd (n := n) (k := t) (f := f) (y := y) hf Φ hΦ0
  have hΛdict := liftedCoordinatesAdd_dictionary (n := n) (k := t) (f := f) (y := y) hf Φ hΦ0
  have hΛ0 : Λ.toFun (e y) = 0 := hΛdict.2.1
  have hΛinv0 : Λ.invFun 0 = e y := by
    rw [← hΛ0]
    exact Λ.left_inv _ Λ.center_mem_source
  let Ξ := LocalHolomorphicEquivAt.comp (inverseCoordinates Λ hΛ0) Φs hΛinv0
  let A₀ : Set (ComplexModel n) := {u | e'.symm (Φ.invFun u) ∈ A}
  have h0A : (0 : ComplexModel n) ∈ A₀ := by
    change e'.symm (Φ.invFun 0) ∈ A
    have hi : Φ.invFun 0 = e' (f y) := by
      rw [← hΦ0]
      exact Φ.left_inv _ Φ.center_mem_source
    rw [hi,e'.left_inv (mem_chart_source _ (f y))]
    exact hymem
  have hcylinder : ∀ u ∈ Ξ.source, horizontalProjection n t u ∈ A₀ ↔
      Ξ.toFun u ∈ complexCoordinatePlane (n+t) j := by
    intro u hu
    have huΛ : u ∈ Λ.target := hu.1
    have hvΛ : Λ.invFun u ∈ Λ.source := Λ.mapsTo_invFun huΛ
    have hv : Λ.invFun u ∈ e.target := hΛdict.1 hvΛ
    let z := e.symm (Λ.invFun u)
    have hz : z ∈ e.source := e.map_target hv
    have hez : e z = Λ.invFun u := e.right_inv hv
    have hzΛ : z ∈ BlowupFlatCoordinates.flatDomain Λ := ⟨hz,by
      change e z ∈ Λ.source
      rw [hez]
      exact hvΛ⟩
    have hd := hΛdict.2.2 z hzΛ
    have hfirst : horizontalProjection n t u = Φ.toFun (e' (f z)) := by
      ext i
      have h := hd.2 i
      change Λ.toFun (e z) (Fin.castAdd t i) = Φ.toFun (e' (f z)) i at h
      rw [hez,Λ.right_inv _ huΛ] at h
      change (EuclideanSpace.finAddEquivProd u).1 i = _
      simpa [EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,
        LinearIsometryEquiv.piLpCongrLeft_apply] using h
    have hback : e'.symm (Φ.invFun (horizontalProjection n t u)) = f z := by
      rw [hfirst,Φ.left_inv _ hd.1.2,e'.left_inv hd.1.1]
    have hflat := hΦsflat hz (hez ▸ hu.2)
    change e'.symm (Φ.invFun (horizontalProjection n t u)) ∈ A ↔
      Φs.toFun (Λ.invFun u) ∈ complexCoordinatePlane (n+t) j
    rw [hback]
    change f z ∈ A ↔ Φs.toFun (e z) ∈ complexCoordinatePlane (n+t) j at hflat
    rw [hez] at hflat
    exact hflat
  obtain ⟨htj,hreg⟩ := regularAtDim_of_cylinder_flattening A₀ hj Ξ hcylinder h0A
  obtain ⟨hjn,hmem,Θ,_hΘsrc,hΘ0,hΘflat⟩ := hreg
  have hΘzero : Θ.toFun 0 = 0 := by
    simpa [complexChartAt,chartAt_self_eq] using hΘ0
  let Ω := LocalHolomorphicEquivAt.comp Φ Θ hΦ0
  refine ⟨htj,hjn,hymem,Ω,(fun u hu => hu.1),?_,?_⟩
  · change Θ.toFun (Φ.toFun (e' (f y))) = 0
    rw [hΦ0,hΘzero]
  · intro x hx hxΩ
    change x ∈ e'.source at hx
    change e' x ∈ Ω.source at hxΩ
    have hflat := hΘflat (mem_univ (Φ.toFun (e' x))) hxΩ.2
    have hleft : e'.symm (Φ.invFun (Φ.toFun (e' x))) = x := by
      rw [Φ.left_inv _ hxΩ.1,e'.left_inv hx]
    change x ∈ A ↔ Θ.toFun (Φ.toFun (e' x)) ∈ complexCoordinatePlane n (j-t)
    simpa [complexChartAt,chartAt_self_eq,A₀,hleft] using hflat

/-- Actual regular codimension-one pairs reflect and pull back across the
same genuine submersion, including arbitrary fibre dimension. -/
theorem regular_codim_one_preimage_iff {n m : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (N S : Set X) :
    (∃ k, RegularAtDim (n := m) (f ⁻¹' N) y (k+1) ∧
      RegularAtDim (n := m) (f ⁻¹' S) y k) ↔
    ∃ k, RegularAtDim (n := n) N (f y) (k+1) ∧
      RegularAtDim (n := n) S (f y) k := by
  constructor
  · rintro ⟨k,hN,hS⟩
    obtain ⟨htk,hS'⟩ := regularAtDim_of_preimage_submersion hf hS
    obtain ⟨_,hN'⟩ := regularAtDim_of_preimage_submersion hf hN
    refine ⟨k-(m-n),?_,hS'⟩
    have he : k+1-(m-n) = (k-(m-n))+1 := by omega
    exact he ▸ hN'
  · rintro ⟨k,hN,hS⟩
    refine ⟨k+(m-n),?_,HironakaSmoothSubmersionRelativeGeometry.regularAtDim_preimage_submersion hf hS⟩
    have h := HironakaSmoothSubmersionRelativeGeometry.regularAtDim_preimage_submersion hf hN
    have he : k+1+(m-n) = (k+(m-n))+1 := by omega
    exact he ▸ h

end
end Hironaka.HironakaSmoothSubmersionRegularityReflection
