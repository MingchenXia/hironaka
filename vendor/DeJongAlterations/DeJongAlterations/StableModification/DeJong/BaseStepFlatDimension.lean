import DeJongAlterations.StableModification.DeJong.BaseStepFlatDimensionAlgebra
import DeJongAlterations.StableModification.DeJong.BaseStepInput
import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundAffine
import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberOpenDimension
import DeJongAlterations.Geometry.ReducedClosedSubscheme

/-!
# Flat families have equidimensional fibres

The dimension theory of flat families used in the base step 4.22 of de Jong
(`dejong96-alterations:page-0025`) to see that the flat strict transforms are multipointed
curves in Temkin's sense (Temkin §1.2, `semi-stable.tex` l.1671–1675): if `g : C → S` is
flat and locally of finite type over a variety `S` and every irreducible component of the
generic fibre has dimension `n`, then every irreducible component of every fibre has
dimension `n` (EGA IV 6.1.2 in the form needed here).

## Proof

* `forall_irreducibleComponents_preimage_dim` (affine case): for a finitely generated domain
  `R` over a field and a flat `R`-algebra `A` of finite type, the components of the fibre
  `Spec A ×_{Spec R} {p}` correspond to the minimal primes `Q` of `κ(p) ⊗_R A`, and the
  component of `Q` has dimension `trdeg κ(P)/κ(p)` for the prime `P ⊆ A` under `Q`
  (`exists_ringKrullDim_fiber_quotient`). The prime `P` is minimal over `p`, and the flat
  dimension formula `relTrdeg_eq_of_minimal_over` gives `trdeg κ(P)/κ(p) = n`.
* `topologicalKrullDim_inter_eq`: on a scheme locally of finite type over a field, an
  irreducible closed subset and each of its nonempty open subsets have the same dimension
  (reduced induced structure and Codex's
  `FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion`).
* `exists_homeomorph_chart`: over affine opens `U = Spec A ⊆ g⁻¹(W)`, `W = Spec R`, the part of
  the fibre `C_s` lying in `U` is homeomorphic to the fibre of `Spec A → Spec R` at the prime
  of `s`.
* `flatFamilyPureFiberDimension`: the statement `FlatFamilyPureFiberDimension`, by covering each
  fibre by such charts; the generic point of `S` corresponds to the zero ideal of each chart.

## Main results

* `flatFamilyPureFiberDimension : FlatFamilyPureFiberDimension`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModification.DeJong

universe u

namespace FlatDimension

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The dimension of a space embedded in `X` is that of its image. -/
theorem topologicalKrullDim_eq_of_isEmbedding {f : Y → X} (hf : IsEmbedding f) {T : Set X}
    (hT : Set.range f = T) : topologicalKrullDim Y = topologicalKrullDim T :=
  IsHomeomorph.topologicalKrullDim_eq _
    (hf.toHomeomorph.trans (Homeomorph.setCongr hT)).isHomeomorph

/-- The trace of `Z` on a subspace `O` has the dimension of `Z ∩ O`. -/
theorem topologicalKrullDim_preimage_val (O Z : Set X) :
    topologicalKrullDim (Subtype.val ⁻¹' Z : Set O) = topologicalKrullDim (Z ∩ O : Set X) := by
  refine topologicalKrullDim_eq_of_isEmbedding
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal) ?_
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.2, y.1.2⟩
  · rintro ⟨hxZ, hxO⟩
    exact ⟨⟨⟨x, hxO⟩, hxZ⟩, rfl⟩

/-- The closure of an irreducible component of an open subspace `O` is an irreducible
component of `X`, whose trace on `O` is the component we started with. -/
theorem closure_image_mem_irreducibleComponents {O : Set X} (hO : IsOpen O) {Z : Set O}
    (hZ : Z ∈ irreducibleComponents O) :
    closure (Subtype.val '' Z) ∈ irreducibleComponents X ∧
      Subtype.val ⁻¹' closure (Subtype.val '' Z) = Z := by
  have hirr : IsIrreducible (closure (Subtype.val '' Z)) :=
    (hZ.1.image _ continuous_subtype_val.continuousOn).closure
  have h1 : Z ⊆ Subtype.val ⁻¹' closure (Subtype.val '' Z) :=
    fun z hz ↦ subset_closure ⟨z, hz, rfl⟩
  have hpre : Subtype.val ⁻¹' closure (Subtype.val '' Z) = Z := by
    have h2 : IsIrreducible (Subtype.val ⁻¹' closure (Subtype.val '' Z) : Set O) :=
      ⟨hZ.1.1.mono h1, hirr.2.preimage hO.isOpenEmbedding_subtypeVal⟩
    exact (hZ.2 h2 h1).antisymm h1
  refine ⟨⟨hirr, fun T hT hle ↦ ?_⟩, hpre⟩
  have hZT : Z ⊆ Subtype.val ⁻¹' T := h1.trans (Set.preimage_mono hle)
  have hTpre : Subtype.val ⁻¹' T = Z :=
    (hZ.2 ⟨hZ.1.1.mono hZT, hT.2.preimage hO.isOpenEmbedding_subtypeVal⟩ hZT).antisymm hZT
  obtain ⟨z, hz⟩ := hZ.1.1
  have hne : (T ∩ O).Nonempty := ⟨z, hZT hz, z.2⟩
  calc T ⊆ closure (T ∩ O) := subset_closure_inter_of_isPreirreducible_of_isOpen hT.2 hO hne
    _ = closure (Subtype.val '' (Subtype.val ⁻¹' T : Set O)) := by
        rw [Subtype.image_preimage_coe, Set.inter_comm]
    _ = closure (Subtype.val '' Z) := by rw [hTpre]

end Topology

section Scheme

variable {K : Type u} [Field K] {F : Scheme.{u}}

/-- On a scheme locally of finite type over a field, an irreducible closed subset `Y` and a
nonempty open part `Y ∩ O` of it have the same dimension. -/
theorem topologicalKrullDim_inter_eq (pF : F ⟶ Spec (.of K)) [LocallyOfFiniteType pF]
    {Y : Set F} (hY : IsIrreducible Y) (hYc : IsClosed Y) {O : Set F} (hO : IsOpen O)
    (hne : (Y ∩ O).Nonempty) :
    topologicalKrullDim (Y ∩ O : Set F) = topologicalKrullDim Y := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨Y, hYc⟩ : Closeds F)
  let ι := I.subschemeι
  have hrange : Set.range ι = Y := I.range_subschemeι
  have hemb : IsEmbedding ι := ι.isClosedEmbedding.isEmbedding
  have : IsReduced I.subscheme :=
    Geometry.ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme _
  let e : I.subscheme ≃ₜ Y := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  obtain ⟨y, hyY, hyO⟩ := hne
  have : Nonempty I.subscheme := ⟨e.symm ⟨y, hyY⟩⟩
  have : IrreducibleSpace Y := Subtype.irreducibleSpace hY
  have : IrreducibleSpace I.subscheme := e.isOpenEmbedding.irreducibleSpace
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  let O' : I.subscheme.Opens := ι ⁻¹ᵁ ⟨O, hO⟩
  have : Nonempty O' := by
    obtain ⟨z, rfl⟩ : y ∈ Set.range ι := hrange ▸ hyY
    exact ⟨⟨z, hyO⟩⟩
  have h1 := Geometry.FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion (ι ≫ pF) O'.ι
  have h2 : topologicalKrullDim I.subscheme = topologicalKrullDim Y :=
    topologicalKrullDim_eq_of_isEmbedding hemb hrange
  have h3 : topologicalKrullDim O' = topologicalKrullDim (Y ∩ O : Set F) := by
    refine topologicalKrullDim_eq_of_isEmbedding (hemb.comp O'.ι.isOpenEmbedding.isEmbedding) ?_
    rw [Set.range_comp, Scheme.Opens.range_ι, ← hrange]
    exact Set.image_preimage_eq_range_inter
  rw [← h3, ← h2]
  exact h1

/-- If all irreducible components of a scheme locally of finite type over a field have
dimension `n`, so do those of each open subspace. -/
theorem forall_irreducibleComponents_dim_isOpen (pF : F ⟶ Spec (.of K))
    [LocallyOfFiniteType pF] {n : WithBot ℕ∞}
    (h : ∀ Z ∈ irreducibleComponents F, topologicalKrullDim Z = n) {O : Set F}
    (hO : IsOpen O) : ∀ Z ∈ irreducibleComponents O, topologicalKrullDim Z = n := by
  intro Z hZ
  obtain ⟨hc, hpre⟩ := closure_image_mem_irreducibleComponents hO hZ
  obtain ⟨z, hz⟩ := hZ.1.1
  have hne : (closure (Subtype.val '' Z) ∩ O).Nonempty := ⟨z, subset_closure ⟨z, hz, rfl⟩, z.2⟩
  calc topologicalKrullDim Z
      = topologicalKrullDim (Subtype.val ⁻¹' closure (Subtype.val '' Z) : Set O) := by
        rw [hpre]
    _ = topologicalKrullDim (closure (Subtype.val '' Z) ∩ O : Set F) :=
        topologicalKrullDim_preimage_val _ _
    _ = topologicalKrullDim (closure (Subtype.val '' Z)) :=
        topologicalKrullDim_inter_eq pF hc.1 (isClosed_of_mem_irreducibleComponents _ hc) hO hne
    _ = n := h _ hc

/-- On a scheme locally of finite type over a field, all irreducible components have
dimension `n` if every point has an open neighbourhood with this property. -/
theorem forall_irreducibleComponents_dim_of_isOpen_cover (pF : F ⟶ Spec (.of K))
    [LocallyOfFiniteType pF] {n : WithBot ℕ∞}
    (h : ∀ x : F, ∃ O : Set F, IsOpen O ∧ x ∈ O ∧
      ∀ Z ∈ irreducibleComponents O, topologicalKrullDim Z = n) :
    ∀ Z ∈ irreducibleComponents F, topologicalKrullDim Z = n := by
  intro Z hZ
  obtain ⟨z, hz⟩ := hZ.1.1
  obtain ⟨O, hO, hzO, hOn⟩ := h z
  have hc : (Subtype.val ⁻¹' Z : Set O) ∈ irreducibleComponents O :=
    preimage_mem_irreducibleComponents hZ hO.isOpenEmbedding_subtypeVal
      ⟨z, hz, by rwa [Subtype.range_coe]⟩
  rw [← topologicalKrullDim_inter_eq pF hZ.1 (isClosed_of_mem_irreducibleComponents _ hZ) hO
    ⟨z, hz, hzO⟩, ← topologicalKrullDim_preimage_val]
  exact hOn _ hc

end Scheme

section Spectrum

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- `trdeg κ(P)/κ(p)` depends only on the ideal `P`. -/
theorem relTrdeg_congr (p : Ideal R) [p.IsPrime] {P P' : Ideal A} [P.IsPrime] [P'.IsPrime]
    (e : P = P') (h : p = P.comap (algebraMap R A)) (h' : p = P'.comap (algebraMap R A)) :
    relTrdeg p P h = relTrdeg p P' h' := by
  subst e
  rfl

open Geometry.FiberDimensionComponentLowerBoundAffine in
/-- The component `V(Q)` of the fibre ring `κ(p) ⊗_R A` has dimension `trdeg κ(P)/κ(p)`, for
`P ⊆ A` the prime under `Q`. -/
theorem exists_topologicalKrullDim_zeroLocus_fiber [Algebra.FiniteType R A]
    (p : PrimeSpectrum R) (Q : PrimeSpectrum (p.asIdeal.Fiber A)) :
    ∃ (h : p.asIdeal = ((PrimeSpectrum.preimageEquivFiber R A p).symm Q).1.asIdeal.comap
        (algebraMap R A)) (d : ℕ),
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Q.asIdeal : Set (p.asIdeal.Fiber A))) = d ∧
        relTrdeg p.asIdeal ((PrimeSpectrum.preimageEquivFiber R A p).symm Q).1.asIdeal h = d := by
  obtain ⟨h, d, hd, htr⟩ := exists_ringKrullDim_fiber_quotient p Q
  refine ⟨h, d, ?_, htr⟩
  rw [topologicalKrullDim_zeroLocus_eq_ringKrullDim_quotient, hd]

/-- **Equidimensional fibres, affine case.** Let `R` be a finitely generated domain over a field
`k` and `A` a flat `R`-algebra of finite type. If every irreducible component of the generic
fibre of `Spec A → Spec R` has dimension `n`, then so does every irreducible component of every
fibre. -/
theorem forall_irreducibleComponents_preimage_dim (k : Type u) [Field k] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] [Algebra.FiniteType R A] [Module.Flat R A] (n : ℕ)
    (hgen : ∀ Y ∈ irreducibleComponents
        (PrimeSpectrum.comap (algebraMap R A) ⁻¹' ({⊥} : Set (PrimeSpectrum R))),
      topologicalKrullDim Y = n)
    (p : PrimeSpectrum R) :
    ∀ Y ∈ irreducibleComponents
        (PrimeSpectrum.comap (algebraMap R A) ⁻¹' ({p} : Set (PrimeSpectrum R))),
      topologicalKrullDim Y = n := by
  have hgen' := forall_irreducibleComponents_dim_of_homeomorph
    (PrimeSpectrum.preimageHomeomorphFiber R A ⊥).symm hgen
  -- the transcendence degrees at the minimal primes of `A`
  have hAL : ∀ (q : Ideal A) (hq : q ∈ minimalPrimes A),
      haveI := hq.1.1
      ∀ h : (⊥ : Ideal R) = q.comap (algebraMap R A), relTrdeg ⊥ q h = n := by
    intro q hq
    have : q.IsPrime := hq.1.1
    intro h
    let e := PrimeSpectrum.preimageOrderIsoFiber R A (⊥ : PrimeSpectrum R)
    let x : PrimeSpectrum.comap (algebraMap R A) ⁻¹' ({⊥} : Set (PrimeSpectrum R)) :=
      ⟨⟨q, this⟩, PrimeSpectrum.ext h.symm⟩
    have hQ : (e x).asIdeal ∈ minimalPrimes ((⊥ : PrimeSpectrum R).asIdeal.Fiber A) := by
      refine ⟨⟨(e x).2, bot_le⟩, fun Q' hQ' hle ↦ ?_⟩
      obtain ⟨y, hy⟩ := e.surjective ⟨Q', hQ'.1⟩
      have hyx : y ≤ x := by
        rw [← e.le_iff_le, hy]
        exact hle
      have hxy : x ≤ y := hq.2 ⟨y.1.2, bot_le⟩ hyx
      have := e.monotone hxy
      rw [hy] at this
      exact this
    have hcomp : PrimeSpectrum.zeroLocus ((e x).asIdeal : Set _) ∈
        irreducibleComponents (PrimeSpectrum ((⊥ : PrimeSpectrum R).asIdeal.Fiber A)) := by
      rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents, (e x).2.radical]
      exact hQ
    obtain ⟨h', d, hd, htr⟩ := exists_topologicalKrullDim_zeroLocus_fiber ⊥ (e x)
    have hdn : (d : WithBot ℕ∞) = n := hd.symm.trans (hgen' _ hcomp)
    have hdn' : d = n := by exact_mod_cast hdn
    have hP : ((PrimeSpectrum.preimageEquivFiber R A ⊥).symm (e x)).1.asIdeal = q := by
      change (e.symm (e x)).1.asIdeal = q
      rw [e.symm_apply_apply]
    rw [relTrdeg_congr _ hP h' h] at htr
    exact htr.trans (by rw [hdn'])
  apply forall_irreducibleComponents_dim_of_homeomorph (PrimeSpectrum.preimageHomeomorphFiber R A p)
  intro Y hY
  rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hY
  obtain ⟨Q, hQ, rfl⟩ := hY
  have : Q.IsPrime := hQ.1.1
  let Qpt : PrimeSpectrum (p.asIdeal.Fiber A) := ⟨Q, this⟩
  let e := PrimeSpectrum.preimageOrderIsoFiber R A p
  obtain ⟨h, d, hd, htr⟩ := exists_topologicalKrullDim_zeroLocus_fiber p Qpt
  have hmin : ∀ P' : Ideal A, P'.IsPrime → P'.comap (algebraMap R A) = p.asIdeal →
      P' ≤ ((PrimeSpectrum.preimageEquivFiber R A p).symm Qpt).1.asIdeal →
      P' = ((PrimeSpectrum.preimageEquivFiber R A p).symm Qpt).1.asIdeal := by
    intro P' hP' hc hle
    let y : PrimeSpectrum.comap (algebraMap R A) ⁻¹' ({p} : Set (PrimeSpectrum R)) :=
      ⟨⟨P', hP'⟩, PrimeSpectrum.ext hc⟩
    have hy : y ≤ e.symm Qpt := hle
    have h1 : e y ≤ Qpt := by
      have := e.monotone hy
      rwa [e.apply_symm_apply] at this
    have h2 : Qpt ≤ e y := hQ.2 ⟨(e y).2, bot_le⟩ h1
    have h3 : e y = Qpt := le_antisymm h1 h2
    have h4 : y = e.symm Qpt := by rw [← h3, e.symm_apply_apply]
    exact congrArg (fun z : PrimeSpectrum.comap (algebraMap R A) ⁻¹' ({p} : Set _) ↦
      z.1.asIdeal) h4
  have hn := relTrdeg_eq_of_minimal_over k n hAL p.asIdeal _ h hmin
  rw [htr] at hn
  have hdn : d = n := by exact_mod_cast hn
  simp only [Function.comp_apply]
  rw [hd, hdn]

end Spectrum

section Chart

variable {C S : Scheme.{u}}

/-- **Affine charts of a fibre.** For affine opens `W ⊆ S` and `U ⊆ g⁻¹(W)` and `s ∈ W`, the
part of the fibre `C_s` lying over `U` is homeomorphic to the fibre of
`Spec Γ(C, U) → Spec Γ(S, W)` at the prime of `s`. -/
theorem exists_homeomorph_chart (g : C ⟶ S) {W : S.Opens} (hW : IsAffineOpen W) {U : C.Opens}
    (hU : IsAffineOpen U) (hUW : U ≤ g ⁻¹ᵁ W) (s : S) (hs : s ∈ W) :
    Nonempty (PrimeSpectrum.comap (g.appLE W U hUW).hom ⁻¹'
        ({hW.primeIdealOf ⟨s, hs⟩} : Set (PrimeSpectrum Γ(S, W))) ≃ₜ
      ((g.fiberι s) ⁻¹' (U : Set C) : Set (g.fiber s))) := by
  have hcomm := IsAffineOpen.SpecMap_appLE_fromSpec g hW hU hUW
  have hpt : ∀ x : Spec Γ(C, U), g (hU.fromSpec x) =
      hW.fromSpec (Spec.map (g.appLE W U hUW) x) := by
    intro x
    rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]
  have hp : hW.fromSpec (hW.primeIdealOf ⟨s, hs⟩) = s := hW.fromSpec_primeIdealOf ⟨s, hs⟩
  let T := PrimeSpectrum.comap (g.appLE W U hUW).hom ⁻¹'
    ({hW.primeIdealOf ⟨s, hs⟩} : Set (PrimeSpectrum Γ(S, W)))
  have hmemT : ∀ x : T, hU.fromSpec x.1 ∈ g ⁻¹' {s} := by
    intro x
    exact (hpt x.1).trans ((congrArg hW.fromSpec x.2).trans hp)
  let f₀ : T → g ⁻¹' {s} := fun x ↦ ⟨hU.fromSpec x.1, hmemT x⟩
  have hf₀ : IsEmbedding f₀ := by
    refine (IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).mp ?_
    exact hU.fromSpec.isOpenEmbedding.isEmbedding.comp IsEmbedding.subtypeVal
  have hmem : ∀ x : T, (g.fiberHomeo s).symm (f₀ x) ∈ (g.fiberι s) ⁻¹' (U : Set C) := by
    intro x
    rw [Set.mem_preimage, Scheme.Hom.fiberι_fiberHomeo_symm, ← hU.range_fromSpec]
    exact ⟨x.1, rfl⟩
  let f : T → ((g.fiberι s) ⁻¹' (U : Set C) : Set (g.fiber s)) :=
    fun x ↦ ⟨(g.fiberHomeo s).symm (f₀ x), hmem x⟩
  have hf : IsEmbedding f := by
    refine (IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).mp ?_
    exact (g.fiberHomeo s).symm.isEmbedding.comp hf₀
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hyU : g.fiberι s y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hy
    obtain ⟨x, hx⟩ := hyU
    have hgy : g (g.fiberι s y) = s := (g.fiberHomeo s y).2
    have hxT : Spec.map (g.appLE W U hUW) x = hW.primeIdealOf ⟨s, hs⟩ :=
      hW.fromSpec.isOpenEmbedding.injective ((hpt x).symm.trans (by rw [hx, hgy, hp]))
    refine ⟨⟨x, hxT⟩, Subtype.ext ?_⟩
    change (g.fiberHomeo s).symm (f₀ ⟨x, hxT⟩) = y
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext hx
  exact ⟨hf.toHomeomorphOfSurjective hsurj⟩

/-- The generic point of an integral scheme corresponds to the zero ideal of each nonempty
affine open. -/
theorem primeIdealOf_genericPoint [IsIntegral S] {W : S.Opens} (hW : IsAffineOpen W)
    [Nonempty W] (hη : genericPoint S ∈ W) :
    hW.primeIdealOf ⟨genericPoint S, hη⟩ = (⊥ : PrimeSpectrum Γ(S, W)) := by
  refine le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ _).mpr ?_)
  refine (hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp ?_
  rw [hW.fromSpec_primeIdealOf]
  exact (genericPoint_spec S).specializes (Set.mem_univ _)

end Chart

/-- **Flat families have equidimensional fibres** (EGA IV 6.1.2 in the form used here): the
statement `FlatFamilyPureFiberDimension` holds. -/
theorem flatFamilyPureFiberDimension : FlatFamilyPureFiberDimension.{u} := by
  intro k _ S C pS _ g _ _ _ n hgen s
  have hlft : ∀ t : S, LocallyOfFiniteType (g.fiberToSpecResidueField t) := fun t ↦
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback g (S.fromSpecResidueField t)) ‹_›
  apply @forall_irreducibleComponents_dim_of_isOpen_cover _ _ _ (g.fiberToSpecResidueField s)
    (hlft s)
  intro x
  have hc : g (g.fiberι s x) = s := (g.fiberHomeo s x).2
  obtain ⟨_, ⟨W, hW, rfl⟩, hsW, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (show s ∈ (⊤ : S.Opens) from trivial) (⊤ : S.Opens).isOpen
  obtain ⟨_, ⟨U, hU, rfl⟩, hcU, hUW⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    (show g.fiberι s x ∈ g ⁻¹ᵁ W by rw [Scheme.Hom.mem_preimage, hc]; exact hsW)
    (g ⁻¹ᵁ W).isOpen
  have hUW' : U ≤ g ⁻¹ᵁ W := hUW
  refine ⟨(g.fiberι s) ⁻¹' (U : Set C), U.isOpen.preimage (g.fiberι s).continuous, hcU, ?_⟩
  let := (g.appLE W U hUW').hom.toAlgebra
  have : Nonempty W := ⟨⟨s, hsW⟩⟩
  have : IsDomain Γ(S, W) := IsIntegral.component_integral W
  let := Geometry.RationalCoordinateMap.sectionAlgebra pS ⟨W, hW⟩
  have : Algebra.FiniteType k Γ(S, W) :=
    Geometry.FunctionFieldDimension.affineSections_finiteType pS ⟨W, hW⟩
  have : Algebra.FiniteType Γ(S, W) Γ(C, U) := RingHom.finiteType_algebraMap.mp
    (HasRingHomProperty.appLE @LocallyOfFiniteType g ‹_› ⟨W, hW⟩ ⟨U, hU⟩ hUW')
  have : Module.Flat Γ(S, W) Γ(C, U) := RingHom.flat_algebraMap_iff.mp
    (HasRingHomProperty.appLE @Flat g ‹_› ⟨W, hW⟩ ⟨U, hU⟩ hUW')
  have hη : genericPoint S ∈ W := genericPoint_mem_of_nonempty W ‹_›
  have hbot := primeIdealOf_genericPoint hW hη
  obtain ⟨eη⟩ := exists_homeomorph_chart g hW hU hUW' (genericPoint S) hη
  rw [hbot] at eη
  have hgenU := @forall_irreducibleComponents_dim_isOpen _ _ _
    (g.fiberToSpecResidueField (genericPoint S)) (hlft _) _ hgen _
    (U.isOpen.preimage (g.fiberι (genericPoint S)).continuous)
  have hA := forall_irreducibleComponents_preimage_dim (R := Γ(S, W)) (A := Γ(C, U)) k n
    (forall_irreducibleComponents_dim_of_homeomorph eη hgenU) (hW.primeIdealOf ⟨s, hsW⟩)
  obtain ⟨es⟩ := exists_homeomorph_chart g hW hU hUW' s hsW
  exact forall_irreducibleComponents_dim_of_homeomorph es.symm hA

end FlatDimension

end DeJongAlterations.StableModification.DeJong
