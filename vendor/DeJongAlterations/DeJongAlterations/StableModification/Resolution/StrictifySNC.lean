import DeJongAlterations.StableModification.Resolution.StrictifyInduction
import DeJongAlterations.Geometry.SNCSubdivisorTopology
import DeJongAlterations.Geometry.SNCSubdivisorSpread
import DeJongAlterations.Geometry.SNCSubdivisorCartier
import DeJongAlterations.Geometry.SNCSubdivisorComponent
import DeJongAlterations.Geometry.SNCLocality
import DeJongAlterations.Algebra.CompletionIntersectionRegularity
import DeJongAlterations.Algebra.NodeFittingIdealSheafQuotient

/-!
# Normal crossings families of multiplicity one are strict normal crossings divisors

Let `Y` be a regular integral scheme of finite type over an algebraically closed field and `F` a
normal crossings family on `Y` all of whose members have multiplicity at most `1`
(`IsNCFamily F (fun _ ↦ 1)`): at every closed point `y` each member through `y` is cut out in
`Ô_{Y,y}` by one parameter `t_{i_l}` of a regular system of parameters, distinct members by
distinct parameters. Then the reduced divisor `⋃ F` is a strict normal crossings divisor in the
sense of Codex's `IsStrictNormalCrossings` (de Jong 1996, 2.4,
`references/dejong96-alterations/tex/page-0006.tex`).

The proof works at closed points. By principal descent along `𝒪_y → Ô_y` each member through
`y` is cut out by an element `h_l ∈ 𝒪_y` associated to `t_{i_l}` in `Ô_y`
(`exists_localEquation`); the irreducible components of `⋃ F` through `y` have the same local
ideals as the members containing them (`localIdeal_eq_of_maximal`); intersections of components
are then cut out by parts of regular systems of parameters (Codex's
`CompletionIntersectionRegularity`), and the general points are reached through the openness of
the regular locus and the Jacobson property.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Resolution.Strictify

set_option backward.isDefEq.respectTransparency false

open Algebra.NodeFittingIdealSheaf Scheme.IdealSheafData

universe u

section Algebra

/-- Associates of parts of a regular system of parameters are parts of a regular system of
parameters. -/
theorem linearIndependent_toCotangent_of_associated {R ι κ : Type*} [CommRing R] [IsLocalRing R]
    [Fintype κ] (t : ι → maximalIdeal R)
    (ht : LinearIndependent (ResidueField R) fun i ↦ (maximalIdeal R).toCotangent (t i))
    (e : κ → ι) (he : Function.Injective e) (a : κ → maximalIdeal R)
    (ha : ∀ s, Associated (a s : R) (t (e s) : R)) :
    LinearIndependent (ResidueField R) fun s ↦ (maximalIdeal R).toCotangent (a s) := by
  have ht' : LinearIndependent (ResidueField R)
      fun s ↦ (maximalIdeal R).toCotangent (t (e s)) := ht.comp e he
  rw [linearIndependent_toCotangent_iff] at ht' ⊢
  choose u hu using ha
  intro c hc s
  have h1 : ∑ s, (c s * ↑(u s)⁻¹) * (t (e s) : R) = ∑ s, c s * (a s : R) := by
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← hu s, mul_mul_mul_comm, Units.inv_mul, mul_one]
  have := ht' (fun s ↦ c s * ↑(u s)⁻¹) (h1 ▸ hc) s
  exact (Ideal.mul_unit_mem_iff_mem _ (u s)⁻¹.isUnit).mp this

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [IsRegularLocalRing (AdicCompletion (maximalIdeal O) O)]

/-- **Intersections of local equations.** If the images in `Ô` of `h_s ∈ O` are associated to
distinct members of a regular system of parameters, then `⋂ (h_s) = (∏ h_s)`. -/
theorem iInf_span_singleton_eq_span_prod {ι κ : Type*} [Fintype κ]
    (t : ι → maximalIdeal (AdicCompletion (maximalIdeal O) O))
    (ht : LinearIndependent (ResidueField (AdicCompletion (maximalIdeal O) O))
      fun i ↦ (maximalIdeal (AdicCompletion (maximalIdeal O) O)).toCotangent (t i))
    (e : κ → ι) (he : Function.Injective e) (h : κ → O)
    (hh : ∀ s, Associated (algebraMap O (AdicCompletion (maximalIdeal O) O) (h s))
      (t (e s) : AdicCompletion (maximalIdeal O) O)) :
    ⨅ s, Ideal.span {h s} = Ideal.span {∏ s, h s} := by
  classical
  have : IsDomain (AdicCompletion (maximalIdeal O) O) :=
    Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  apply le_antisymm
  · intro x hx
    rw [← Algebra.CompletionRegularityBasics.comap_map O (Ideal.span {∏ s, h s}), Ideal.mem_comap,
      Ideal.map_span, Set.image_singleton, map_prod]
    have hprod : Ideal.span {∏ s, algebraMap O (AdicCompletion (maximalIdeal O) O) (h s)} =
        Ideal.span {∏ s, (t (e s) : AdicCompletion (maximalIdeal O) O)} :=
      Ideal.span_singleton_eq_span_singleton.mpr
        (Associated.prod _ _ _ fun s _ ↦ hh s)
    rw [hprod, span_prod_param_eq_inf (fun s ↦ t (e s)) (ht.comp e he) Finset.univ]
    simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Submodule.mem_iInf]
    intro s
    rw [← Ideal.span_singleton_eq_span_singleton.mpr (hh s)]
    have hs : x ∈ Ideal.span {h s} := (Submodule.mem_iInf _).mp hx s
    simpa [Ideal.map_span] using
      Ideal.mem_map_of_mem (algebraMap O (AdicCompletion (maximalIdeal O) O)) hs
  · refine le_iInf fun s ↦ ?_
    rw [Ideal.span_singleton_le_span_singleton]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ s)

end Algebra

section Local

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **Local equations of members of multiplicity one.** If `x ∈ F l` and the chart `c` gives
`F l` at most one branch, then it has exactly one branch `t_i`, and `I(F l)_x = (h)` for some
`h ∈ 𝒪_x` associated to `t_i` in `Ô_x`. -/
theorem exists_localEquation {ι : Type*} (F : ι → Closeds X) (x : X) (c : NCChart F x)
    [IsDomain (X.completedLocalRing x)] (l : ι) (hl : (c.A l).card ≤ 1) (hx : x ∈ F l) :
    ∃ (i : Fin c.n) (h : X.presheaf.stalk x), c.A l = {i} ∧
      localIdeal (F l) x = Ideal.span {h} ∧
      Associated (algebraMap _ (X.completedLocalRing x) h) (c.t i : X.completedLocalRing x) := by
  have hne : c.A l ≠ ∅ := by
    intro h0
    apply (formalIdeal_ne_top_iff (F l) x).mpr hx
    rw [c.formalIdeal_eq l, h0, Finset.prod_empty, Ideal.span_singleton_one]
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp
    (le_antisymm hl (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)))
  have hf : formalIdeal (F l) x = Ideal.span {(c.t i : X.completedLocalRing x)} := by
    rw [c.formalIdeal_eq l, hi, Finset.prod_singleton]
  obtain ⟨h, -, hJ, hspan⟩ := exists_span_singleton_eq_of_map_eq_span_singleton
    (X.toCompletedLocalRing x)
    (fun J ↦ Algebra.CompletionRegularityBasics.comap_map (X.presheaf.stalk x) J)
    (localIdeal (F l) x) _ hf
  exact ⟨i, h, hi, hJ, Ideal.span_singleton_eq_span_singleton.mp hspan⟩

/-- The local ideal of a member through `x` with one branch is prime. -/
theorem localIdeal_isPrime_of_mem {ι : Type*} (F : ι → Closeds X) (x : X) (c : NCChart F x)
    [IsRegularLocalRing (X.completedLocalRing x)] (l : ι) (hl : (c.A l).card ≤ 1)
    (hx : x ∈ F l) : (localIdeal (F l) x).IsPrime := by
  have : IsDomain (X.completedLocalRing x) :=
    Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  obtain ⟨i, h, hi, -, -⟩ := exists_localEquation F x c l hl hx
  have hf : formalIdeal (F l) x = Ideal.span {(c.t i : X.completedLocalRing x)} := by
    rw [c.formalIdeal_eq l, hi, Finset.prod_singleton]
  rw [← Algebra.CompletionRegularityBasics.comap_map (X.presheaf.stalk x) (localIdeal (F l) x)]
  change (formalIdeal (F l) x).comap _ |>.IsPrime
  rw [hf]
  have := (Ideal.span_singleton_prime (prime_param c.t c.indep i).ne_zero).mpr
    (prime_param c.t c.indep i)
  exact Ideal.comap_isPrime _ _

end Local

section Components

variable {X : Scheme.{u}}

/-- **Local ideals of maximal irreducible subsets.** Let `C ⊆ G ⊆ B` be closed, `C` irreducible and
maximal among the irreducible subsets of `B`, and `x ∈ C`. If `I(G)_x` is prime then
`I(C)_x = I(G)_x`. -/
theorem localIdeal_eq_of_maximal (B C G : Closeds X) (hC : IsIrreducible (C : Set X))
    (hmax : ∀ T : Set X, IsIrreducible T → (C : Set X) ⊆ T → T ⊆ B → T ⊆ C)
    (hCG : C ≤ G) (hGB : G ≤ B) (x : X) (hx : x ∈ C) (hprime : (localIdeal G x).IsPrime) :
    localIdeal C x = localIdeal G x := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  let A := Γ(X, U.1)
  let : Algebra A (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x, hxU⟩
  let p := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
  let f := U.2.fromSpec
  have hrange : Set.range f = U.1 := U.2.range_fromSpec
  let IC := (vanishingIdeal C).ideal U
  let IG := (vanishingIdeal G).ideal U
  have hIC : IC = PrimeSpectrum.vanishingIdeal (f ⁻¹' C) := vanishingIdeal_ideal _ _
  have hIG : IG = PrimeSpectrum.vanishingIdeal (f ⁻¹' G) := vanishingIdeal_ideal _ _
  have hlocC : localIdeal C x = IC.map (algebraMap A (X.presheaf.stalk x)) :=
    stalkIdeal_eq_map_germ _ U hxU
  have hlocG : localIdeal G x = IG.map (algebraMap A (X.presheaf.stalk x)) :=
    stalkIdeal_eq_map_germ _ U hxU
  let P := (localIdeal G x).comap (algebraMap A (X.presheaf.stalk x))
  have hPprime : P.IsPrime := Ideal.comap_isPrime _ _
  have hGP : IG ≤ P := by
    show IG ≤ (localIdeal G x).comap _
    rw [hlocG]
    exact Ideal.le_comap_map
  have hxpt : f (U.2.primeIdealOf ⟨x, hxU⟩) = x := U.2.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hCirr : IsIrreducible (f ⁻¹' C) :=
    hC.preimage f.isOpenEmbedding ⟨x, hx, U.2.primeIdealOf ⟨x, hxU⟩, hxpt⟩
  have hICprime : IC.IsPrime := by
    rw [hIC]
    exact PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hCirr
  have hICp : IC ≤ p := by
    rw [hIC]
    intro a ha
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp ha _ (by
      change f (U.2.primeIdealOf ⟨x, hxU⟩) ∈ C
      rw [hxpt]
      exact hx)
  have hdisj : Disjoint (p.primeCompl : Set A) IC :=
    Set.disjoint_left.mpr fun a ha haI ↦ ha (hICp haI)
  have hCcomap : (IC.map (algebraMap A (X.presheaf.stalk x))).comap
      (algebraMap A (X.presheaf.stalk x)) = IC :=
    IsLocalization.under_map_of_isPrime_disjoint p.primeCompl _ hICprime hdisj
  have hGC : IG ≤ IC := (le_def.mp (vanishingIdeal_antimono hCG)) U
  have hPIC : P ≤ IC := by
    intro a ha
    rw [← hCcomap]
    have ha' : algebraMap A (X.presheaf.stalk x) a ∈ localIdeal G x := ha
    rw [hlocG] at ha'
    exact Ideal.map_mono hGC ha'
  -- the irreducible closed set `T = closure (V(P))`
  let T : Set X := closure (f '' PrimeSpectrum.zeroLocus (P : Set A))
  have hTirr : IsIrreducible T := by
    have h0 : PrimeSpectrum.zeroLocus (P : Set A) = closure {(⟨P, hPprime⟩ : PrimeSpectrum A)} :=
      (PrimeSpectrum.closure_singleton (R := A) ⟨P, hPprime⟩).symm
    show IsIrreducible (closure (f '' PrimeSpectrum.zeroLocus (P : Set A)))
    rw [h0]
    exact (isIrreducible_singleton.closure.image f f.continuous.continuousOn).closure
  have hCT : (C : Set X) ⊆ T := by
    have h1 : (C : Set X) ⊆ closure ((C : Set X) ∩ U.1) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen hC.isPreirreducible U.1.isOpen
        ⟨x, hx, hxU⟩
    refine h1.trans (closure_mono ?_)
    rintro z ⟨hzC, hzU⟩
    obtain ⟨q, rfl⟩ : z ∈ Set.range f := hrange ▸ hzU
    refine ⟨q, ?_, rfl⟩
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    refine hPIC.trans ?_
    rw [hIC]
    intro a ha
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp ha q hzC
  have hTB : T ⊆ B := by
    have hTG : T ⊆ G := by
      refine closure_minimal ?_ G.isClosed
      rintro _ ⟨q, hq, rfl⟩
      have hq' : q ∈ PrimeSpectrum.zeroLocus (IG : Set A) := by
        rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
        exact hGP.trans ((PrimeSpectrum.mem_zeroLocus _ _).mp hq)
      rw [hIG, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
        (G.isClosed.preimage f.continuous).closure_eq] at hq'
      exact hq'
    exact hTG.trans hGB
  have hTC := hmax T hTirr hCT hTB
  have hICP : IC ≤ P := by
    rw [hIC]
    have hsub : PrimeSpectrum.zeroLocus (P : Set A) ⊆ f ⁻¹' C :=
      fun q hq ↦ hTC (subset_closure ⟨q, hq, rfl⟩)
    calc PrimeSpectrum.vanishingIdeal (f ⁻¹' C)
        ≤ PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (P : Set A)) :=
          PrimeSpectrum.vanishingIdeal_anti_mono hsub
      _ = P := by rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hPprime.radical]
  rw [hlocC, le_antisymm hICP hPIC]
  exact IsLocalization.map_under p.primeCompl _ (localIdeal G x)

/-- Two irreducible closed subsets through `x` with the same local ideal at `x` coincide. -/
theorem eq_of_localIdeal_eq (C C' : Closeds X) (hC : IsIrreducible (C : Set X))
    (hC' : IsIrreducible (C' : Set X)) (x : X) (hx : x ∈ C) (hx' : x ∈ C')
    (h : localIdeal C x = localIdeal C' x) : C = C' := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  let A := Γ(X, U.1)
  let : Algebra A (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x, hxU⟩
  let p := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
  let f := U.2.fromSpec
  have hrange : Set.range f = U.1 := U.2.range_fromSpec
  have hxpt : f (U.2.primeIdealOf ⟨x, hxU⟩) = x := U.2.fromSpec_primeIdealOf ⟨x, hxU⟩
  -- the affine ideal of an irreducible closed set through `x` is recovered from its stalk
  have key : ∀ D : Closeds X, IsIrreducible (D : Set X) → x ∈ D →
      ((localIdeal D x).comap (algebraMap A (X.presheaf.stalk x))) =
        PrimeSpectrum.vanishingIdeal (f ⁻¹' D) := by
    intro D hD hxD
    have hID : (vanishingIdeal D).ideal U = PrimeSpectrum.vanishingIdeal (f ⁻¹' D) :=
      vanishingIdeal_ideal _ _
    have hirr : IsIrreducible (f ⁻¹' D) :=
      hD.preimage f.isOpenEmbedding ⟨x, hxD, U.2.primeIdealOf ⟨x, hxU⟩, hxpt⟩
    have hprime := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hirr
    have hle : PrimeSpectrum.vanishingIdeal (f ⁻¹' D) ≤ p := by
      intro a ha
      exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp ha _ (by
        change f (U.2.primeIdealOf ⟨x, hxU⟩) ∈ D
        rw [hxpt]
        exact hxD)
    rw [localIdeal, stalkIdeal_eq_map_germ _ U hxU, hID]
    exact IsLocalization.under_map_of_isPrime_disjoint p.primeCompl _ hprime
      (Set.disjoint_left.mpr fun a ha haI ↦ ha (hle haI))
  have hpre : f ⁻¹' C = f ⁻¹' C' := by
    have h1 := key C hC hx
    have h2 := key C' hC' hx'
    rw [h] at h1
    have h3 := congrArg PrimeSpectrum.zeroLocus (congrArg (fun I : Ideal A ↦ (I : Set A))
      (h1.symm.trans h2))
    simp only [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      (C.isClosed.preimage f.continuous).closure_eq,
      (C'.isClosed.preimage f.continuous).closure_eq] at h3
    exact h3
  have hU : (C : Set X) ∩ U.1 = (C' : Set X) ∩ U.1 := by
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      obtain ⟨q, rfl⟩ : z ∈ Set.range f := hrange ▸ hzU
      exact ⟨(show q ∈ f ⁻¹' C' from hpre ▸ hz), hzU⟩
    · rintro ⟨hz, hzU⟩
      obtain ⟨q, rfl⟩ : z ∈ Set.range f := hrange ▸ hzU
      exact ⟨(show q ∈ f ⁻¹' C from hpre.symm ▸ hz), hzU⟩
  have hcl : ∀ D : Closeds X, IsIrreducible (D : Set X) → x ∈ D →
      (D : Set X) = closure ((D : Set X) ∩ U.1) := fun D hD hxD ↦
    le_antisymm (subset_closure_inter_of_isPreirreducible_of_isOpen hD.isPreirreducible
      U.1.isOpen ⟨x, hxD, hxU⟩) (closure_minimal Set.inter_subset_left D.isClosed)
  apply SetLike.coe_injective
  rw [hcl C hC hx, hcl C' hC' hx', hU]

end Components

section Lattice

variable {X : Scheme.{u}}

/-- Stalks of ideal sheaves commute with suprema. -/
theorem stalkIdeal_iSup {ι : Type*} (I : ι → X.IdealSheafData) (x : X) :
    Algebra.NodeFittingIdealSheaf.stalkIdeal (⨆ i, I i) x =
      ⨆ i, Algebra.NodeFittingIdealSheaf.stalkIdeal (I i) x := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hxU, ideal_iSup, iSup_apply, Ideal.map_iSup]
  congr 1
  ext1 i
  rw [stalkIdeal_eq_map_germ _ U hxU]

/-- Stalks of ideal sheaves commute with finite infima. -/
theorem stalkIdeal_iInf {ι : Type*} [Finite ι] (I : ι → X.IdealSheafData) (x : X) :
    Algebra.NodeFittingIdealSheaf.stalkIdeal (⨅ i, I i) x =
      ⨅ i, Algebra.NodeFittingIdealSheaf.stalkIdeal (I i) x := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have hloc := U.2.isLocalization_stalk ⟨x, hxU⟩
  rw [stalkIdeal_eq_map_germ _ U hxU, ideal_iInf, iInf_apply]
  have h := Geometry.SNCSubdivisorCartier.map_finset_inf (S := X.presheaf.stalk x)
    (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl Finset.univ (fun i ↦ (I i).ideal U)
  rw [Finset.inf_eq_iInf, Finset.inf_eq_iInf] at h
  simp only [Finset.mem_univ, iInf_true] at h
  refine h.trans ?_
  congr 1
  ext1 i
  rw [stalkIdeal_eq_map_germ _ U hxU]
  rfl

end Lattice

section Family

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {r : ℕ} (F : Fin r → Closeds X)

omit [IsLocallyNoetherian X] in
/-- An irreducible closed subset of `⋃ F` lies in some member. -/
theorem exists_le_of_isIrreducible (C : Closeds X) (hC : IsIrreducible (C : Set X))
    (hCB : C ≤ ⨆ l, F l) : ∃ l, C ≤ F l := by
  classical
  have hsub : (C : Set X) ⊆ ⋃₀ ((Finset.univ.image fun l ↦ (F l : Set X) : Finset (Set X)) :
      Set (Set X)) := by
    intro z hz
    obtain ⟨l, hl⟩ := (mem_iSup_closeds F z).mp (hCB hz)
    exact ⟨F l, by simp, hl⟩
  obtain ⟨z, hz, hCz⟩ := isIrreducible_iff_sUnion_isClosed.mp hC _ (by
    intro z hz
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hz
    exact (F l).isClosed) hsub
  obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨l, hCz⟩

variable {F}

/-- At a closed point `x`, every component `C` of `⋃ F` through `x` lies in a member `F l` through
`x` with `I(C)_x = I(F l)_x`. -/
theorem exists_member_of_component (hF : IsNCFamily F (fun _ ↦ 1))
    (C : DivisorComponent (vanishingIdeal (⨆ l, F l))) (x : X) (hx : IsClosed ({x} : Set X))
    [IsRegularLocalRing (X.completedLocalRing x)] (hxC : x ∈ C.val) :
    ∃ l, x ∈ F l ∧ C.val ≤ F l ∧ localIdeal C.val x = localIdeal (F l) x := by
  obtain ⟨c, hc⟩ := hF x hx
  have hsupp : (vanishingIdeal (⨆ l, F l)).support = ⨆ l, F l :=
    Geometry.ReducedClosedSubscheme.support_vanishingIdeal _
  have hirr := Geometry.SNCLocality.divisorComponent_isIrreducible _ C
  have hCB : C.val ≤ ⨆ l, F l :=
    (Geometry.SNCSubdivisorComponent.component_le_support _ C).trans hsupp.le
  obtain ⟨l, hl⟩ := exists_le_of_isIrreducible F C.val hirr hCB
  have hxl : x ∈ F l := hl hxC
  refine ⟨l, hxl, hl, localIdeal_eq_of_maximal (⨆ l, F l) C.val (F l) hirr ?_ hl
    (le_iSup F l) x hxC (localIdeal_isPrime_of_mem F x c l (hc l) hxl)⟩
  intro T hT hCT hTB
  exact Geometry.SNCSubdivisorTopology.component_maximal _ C T hT hCT (by rw [hsupp]; exact hTB)

/-- Local equations of all members at a closed point. -/
theorem exists_localEquations (hF : IsNCFamily F (fun _ ↦ 1)) (x : X)
    (hx : IsClosed ({x} : Set X)) [IsRegularLocalRing (X.completedLocalRing x)] :
    ∃ (c : NCChart F x) (i : {l // x ∈ F l} → Fin c.n) (h : {l // x ∈ F l} → X.presheaf.stalk x),
      (∀ l, c.A l.1 = {i l} ∧ localIdeal (F l.1) x = Ideal.span {h l} ∧
        Associated (algebraMap _ (X.completedLocalRing x) (h l))
          (c.t (i l) : X.completedLocalRing x)) ∧
      Function.Injective i ∧ (∀ l, x ∉ F l → localIdeal (F l) x = ⊤) := by
  classical
  obtain ⟨c, hc⟩ := hF x hx
  have : IsDomain (X.completedLocalRing x) :=
    Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  choose i h hih using fun l : {l // x ∈ F l} ↦ exists_localEquation F x c l.1 (hc l.1) l.2
  refine ⟨c, i, h, hih, ?_, ?_⟩
  · intro l l' hii
    by_contra hne
    have hd : Disjoint (c.A l.1) (c.A l'.1) := c.disjoint fun h' ↦ hne (Subtype.ext h')
    rw [(hih l).1, (hih l').1, hii] at hd
    exact Finset.disjoint_singleton.mp hd rfl
  · intro l hl
    by_contra hne
    exact hl ((localIdeal_ne_top_iff (F l) x).mp hne)

/-- At a closed point the ideal of `⋃ F` is principal, generated by the product of the local
equations of the members through the point. -/
theorem exists_localIdeal_iSup_eq_span (hF : IsNCFamily F (fun _ ↦ 1)) (x : X)
    (hx : IsClosed ({x} : Set X)) [IsRegularLocalRing (X.completedLocalRing x)] :
    ∃ b : X.presheaf.stalk x, b ≠ 0 ∧ localIdeal (⨆ l, F l) x = Ideal.span {b} := by
  classical
  obtain ⟨c, i, h, hih, hinj, htop⟩ := exists_localEquations hF x hx
  have : IsDomain (X.completedLocalRing x) :=
    Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  have hloc : localIdeal (⨆ l, F l) x = ⨅ l, localIdeal (F l) x := by
    rw [localIdeal, Scheme.IdealSheafData.vanishingIdeal_iSup, stalkIdeal_iInf]
    rfl
  have hinf : ⨅ l, localIdeal (F l) x = ⨅ l : {l // x ∈ F l}, Ideal.span {h l} := by
    apply le_antisymm
    · exact le_iInf fun l ↦ iInf_le_of_le l.1 (hih l).2.1.le
    · refine le_iInf fun l ↦ ?_
      by_cases hl : x ∈ F l
      · exact iInf_le_of_le ⟨l, hl⟩ (hih ⟨l, hl⟩).2.1.ge
      · rw [htop l hl]
        exact le_top
  rw [hloc, hinf, iInf_span_singleton_eq_span_prod c.t c.indep i hinj h (fun l ↦ (hih l).2.2)]
  refine ⟨∏ l, h l, ?_, rfl⟩
  intro h0
  have hassoc : Associated (algebraMap _ (X.completedLocalRing x) (∏ l, h l))
      (∏ l, (c.t (i l) : X.completedLocalRing x)) := by
    rw [map_prod]
    exact Associated.prod _ _ _ fun l _ ↦ (hih l).2.2
  rw [h0, map_zero] at hassoc
  have hne : (∏ l, (c.t (i l) : X.completedLocalRing x)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun l _ ↦ (prime_param c.t c.indep (i l)).ne_zero
  exact hne (zero_dvd_iff.mp hassoc.dvd)

end Family

section Cartier

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] {r : ℕ} {F : Fin r → Closeds X}

include q in
/-- **Cartier.** On a regular integral scheme of finite type over a field, the union of a normal
crossings family of multiplicity one is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_vanishingIdeal_iSup (hX : IsRegularScheme X)
    (hF : IsNCFamily F (fun _ ↦ 1)) :
    IsEffectiveCartierDivisor (vanishingIdeal (⨆ l, F l)) := by
  intro x
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace q
  obtain ⟨x₀, hx₀x, hx₀⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set X))
    ⟨x, subset_closure (Set.mem_singleton x)⟩ isClosed_closure.isLocallyClosed
  have hsp : x ⤳ x₀ := specializes_iff_mem_closure.mpr hx₀x
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hX x₀
  have : IsRegularLocalRing (X.completedLocalRing x₀) :=
    Algebra.CompletionRegularityAscent.isRegularLocalRing_completion _
  obtain ⟨b, hb0, hb⟩ := exists_localIdeal_iSup_eq_span hF x₀ hx₀
  obtain ⟨U, hx₀U⟩ := exists_affineOpens_mem x₀
  let R := Γ(X, U.1)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  have : Nonempty U.1 := ⟨⟨x₀, hx₀U⟩⟩
  let : Algebra R (X.presheaf.stalk x₀) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x₀, hx₀U⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x₀) (U.2.primeIdealOf ⟨x₀, hx₀U⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x₀, hx₀U⟩
  let p := (U.2.primeIdealOf ⟨x₀, hx₀U⟩).asIdeal
  let I := (vanishingIdeal (⨆ l, F l)).ideal U
  have hI : I.map (algebraMap R (X.presheaf.stalk x₀)) = Ideal.span {b} := by
    rw [← hb, localIdeal, stalkIdeal_eq_map_germ _ U hx₀U]
    rfl
  let e := IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk x₀) (Localization.AtPrime p)
  have heq : I.map (algebraMap R (Localization.AtPrime p)) = Ideal.span {e b} := by
    have : algebraMap R (Localization.AtPrime p) =
        (e : X.presheaf.stalk x₀ →+* Localization.AtPrime p).comp
          (algebraMap R (X.presheaf.stalk x₀)) :=
      RingHom.ext fun z ↦ (e.commutes z).symm
    rw [this, ← Ideal.map_map, hI, Ideal.map_span, Set.image_singleton]
    rfl
  have : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  have hreg : IsRegular (e b) := IsRegular.of_ne_zero fun h ↦ hb0 (e.injective (h.trans
    (map_zero e).symm))
  obtain ⟨s, hs, a, -, hareg, hspan⟩ :=
    Geometry.SNCSubdivisorSpread.exists_away_regular_span_eq I p (e b) hreg heq
  have hx₀V : x₀ ∈ X.basicOpen s := by
    rw [Scheme.mem_basicOpen X s x₀ hx₀U]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x₀) p s).mpr hs
  have hxV : x ∈ X.basicOpen s := hsp.mem_open (X.basicOpen s).isOpen hx₀V
  let : Algebra R Γ(X, X.basicOpen s) := (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom.toAlgebra
  have : IsLocalization.Away s Γ(X, X.basicOpen s) := U.2.isLocalization_basicOpen s
  let e' := IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) Γ(X, X.basicOpen s)
  refine ⟨X.affineBasicOpen s, hxV, e' (algebraMap R (Localization.Away s) a),
    Geometry.CartierLocality.isRegular_ringEquiv e'.toRingEquiv hareg, ?_⟩
  rw [← (vanishingIdeal (⨆ l, F l)).map_ideal_basicOpen U s]
  change I.map (algebraMap R Γ(X, X.basicOpen s)) = _
  have : algebraMap R Γ(X, X.basicOpen s) =
      (e' : Localization.Away s →+* Γ(X, X.basicOpen s)).comp
        (algebraMap R (Localization.Away s)) :=
    RingHom.ext fun z ↦ (e'.commutes z).symm
  rw [this, ← Ideal.map_map, hspan, Ideal.map_span, Set.image_singleton]
  rfl

end Cartier

section Intersections

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {r : ℕ} {F : Fin r → Closeds X}

/-- **Intersections of components at a closed point.** At a closed point `x` of the intersection of
a set `J` of components of `⋃ F`, the ideal of the scheme-theoretic intersection is generated by a
part `(t_C)_{C ∈ J}` of a regular system of parameters of `𝒪_x` (tested in `Ô_x`). -/
theorem exists_stalkIdeal_componentIntersection (hF : IsNCFamily F (fun _ ↦ 1))
    (J : Finset (DivisorComponent (vanishingIdeal (⨆ l, F l)))) (x : X)
    (hx : IsClosed ({x} : Set X)) [IsRegularLocalRing (X.completedLocalRing x)]
    (hxE : x ∈ (componentIntersection (vanishingIdeal (⨆ l, F l)) J).support) :
    ∃ t : J → maximalIdeal (X.presheaf.stalk x),
      Algebra.NodeFittingIdealSheaf.stalkIdeal
          (componentIntersection (vanishingIdeal (⨆ l, F l)) J) x =
        Ideal.span (Set.range fun C ↦ (t C : X.presheaf.stalk x)) ∧
      LinearIndependent (ResidueField (X.completedLocalRing x)) (fun C ↦
        (maximalIdeal (X.completedLocalRing x)).toCotangent
          (Algebra.CompletionIntersectionRegularityCotangent.completedFamily _ t C)) := by
  classical
  have hxC : ∀ C : J, x ∈ C.1.val := by
    intro C
    rw [componentIntersection_support] at hxE
    exact Closeds.mem_iInf.mp (Closeds.mem_iInf.mp hxE C.1) C.2
  choose l hxl hCl hlocl using fun C : J ↦ exists_member_of_component hF C.1 x hx (hxC C)
  obtain ⟨c, i, h, hih, hinj, -⟩ := exists_localEquations hF x hx
  let lam : J → {l // x ∈ F l} := fun C ↦ ⟨l C, hxl C⟩
  have hlocC : ∀ C : J, localIdeal C.1.val x = Ideal.span {h (lam C)} := fun C ↦
    (hlocl C).trans (hih (lam C)).2.1
  have hlaminj : Function.Injective lam := by
    intro C C' hCC
    have h1 : localIdeal C.1.val x = localIdeal C'.1.val x := by
      rw [hlocC, hlocC, hCC]
    exact Subtype.ext (Subtype.ext (eq_of_localIdeal_eq _ _
      (Geometry.SNCLocality.divisorComponent_isIrreducible _ C.1)
      (Geometry.SNCLocality.divisorComponent_isIrreducible _ C'.1) x (hxC C) (hxC C') h1))
  have hmem : ∀ C : J, h (lam C) ∈ maximalIdeal (X.presheaf.stalk x) := by
    intro C
    have hle := (localIdeal_le_maximalIdeal_iff (F (l C)) x).mpr (hxl C)
    rw [(hih (lam C)).2.1] at hle
    exact hle (Ideal.subset_span rfl)
  refine ⟨fun C ↦ ⟨h (lam C), hmem C⟩, ?_, ?_⟩
  · rw [componentIntersection, iSup_subtype', stalkIdeal_iSup]
    change _ = Submodule.span _ _
    rw [Submodule.span_range_eq_iSup]
    congr 1
    ext1 C
    exact hlocC C
  · exact linearIndependent_toCotangent_of_associated c.t c.indep (fun C ↦ i (lam C))
      (hinj.comp hlaminj) _ fun C ↦ (hih (lam C)).2.2

variable {k : Type u} [Field k] [PerfectField k] (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q]

include q in
/-- **Regular intersections.** -/
theorem isRegularScheme_componentIntersection (hX : IsRegularScheme X)
    (hF : IsNCFamily F (fun _ ↦ 1)) (J : Finset (DivisorComponent (vanishingIdeal (⨆ l, F l)))) :
    IsRegularScheme (componentIntersection (vanishingIdeal (⨆ l, F l)) J).subscheme := by
  let E := componentIntersection (vanishingIdeal (⨆ l, F l)) J
  apply isRegularScheme_of_closedPoints (E.subschemeι ≫ q)
  intro z hz
  have hx : IsClosed ({E.subschemeι z} : Set X) := by
    have := E.subschemeι.isClosedEmbedding.isClosedMap _ hz
    rwa [Set.image_singleton] at this
  have hxE : E.subschemeι z ∈ E.support := by
    change E.subschemeι z ∈ (E.support : Set X)
    rw [← range_subschemeι]
    exact Set.mem_range_self z
  have : IsRegularLocalRing (X.presheaf.stalk (E.subschemeι z)) := hX _
  have : IsRegularLocalRing (X.completedLocalRing (E.subschemeι z)) :=
    Algebra.CompletionRegularityAscent.isRegularLocalRing_completion _
  obtain ⟨t, ht, hli⟩ := exists_stalkIdeal_componentIntersection hF J _ hx hxE
  have hreg := Algebra.CompletionIntersectionRegularity.isRegularLocalRing_original_quotient
    (X.presheaf.stalk (E.subschemeι z)) t hli
  rw [← ht] at hreg
  exact IsRegularLocalRing.of_ringEquiv (stalkQuotientEquiv E z)

end Intersections

section Codimension

variable {X : Scheme.{u}}

/-- Membership in the support of an ideal sheaf, on an affine open. -/
theorem mem_support_iff_le_primeIdealOf (E : X.IdealSheafData) (U : X.affineOpens) (z : X)
    (hz : z ∈ U.1) : z ∈ E.support ↔ E.ideal U ≤ (U.2.primeIdealOf ⟨z, hz⟩).asIdeal := by
  let : Algebra Γ(X, U.1) (X.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hz⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk z) (U.2.primeIdealOf ⟨z, hz⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨z, hz⟩
  rw [Algebra.NodeFittingGeometricNodeSupport.mem_support_iff_stalkIdeal_le_maximalIdeal,
    stalkIdeal_eq_map_germ _ U hz]
  change Ideal.map (algebraMap Γ(X, U.1) (X.presheaf.stalk z)) _ ≤ _ ↔ _
  rw [Ideal.map_le_iff_le_comap]
  rw [show (maximalIdeal (X.presheaf.stalk z)).comap (algebraMap Γ(X, U.1) (X.presheaf.stalk z)) =
    (U.2.primeIdealOf ⟨z, hz⟩).asIdeal from
    IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk z) _]

variable [IsLocallyNoetherian X] {r : ℕ} {F : Fin r → Closeds X}
  {k : Type u} [Field k] (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q]

include q in
/-- **Codimension of intersections.** The scheme-theoretic intersection of `|J|` components of
`⋃ F` has pure codimension `|J|`. -/
theorem hasPureCodimension_componentIntersection (hX : IsRegularScheme X)
    (hF : IsNCFamily F (fun _ ↦ 1)) (J : Finset (DivisorComponent (vanishingIdeal (⨆ l, F l)))) :
    HasPureCodimension (componentIntersection (vanishingIdeal (⨆ l, F l)) J).support J.card := by
  classical
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace q
  let E := componentIntersection (vanishingIdeal (⨆ l, F l)) J
  intro W hW w hw
  have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
  have hW'c : IsClosed ((Subtype.val : E.support → X) '' W) :=
    E.support.isClosed.isClosedEmbedding_subtypeVal.isClosedMap W hWc
  -- a closed point `x` of the component
  obtain ⟨x, hxW, hx⟩ := nonempty_inter_closedPoints ⟨w, hw.mem⟩ hW'c.isLocallyClosed
  have hxE : x ∈ E.support := by
    obtain ⟨x', -, rfl⟩ := hxW
    exact x'.2
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have : IsRegularLocalRing (X.completedLocalRing x) :=
    Algebra.CompletionRegularityAscent.isRegularLocalRing_completion _
  obtain ⟨t, ht, hli⟩ := exists_stalkIdeal_componentIntersection hF J x hx hxE
  have hheight := Algebra.CompletionIntersectionRegularity.original_ideal_height
    (X.presheaf.stalk x) t hli
  have hreg := Algebra.CompletionIntersectionRegularity.isRegularLocalRing_original_quotient
    (X.presheaf.stalk x) t hli
  have : IsDomain (X.presheaf.stalk x ⧸ Ideal.span (Set.range fun C ↦ (t C : X.presheaf.stalk x))) :=
    Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  have hprime : (Algebra.NodeFittingIdealSheaf.stalkIdeal E x).IsPrime := by
    rw [ht]
    exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  -- an affine neighbourhood
  have hsp : w ⤳ x := hw.specializes hxW
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  have hwU : w ∈ U.1 := hsp.mem_open U.1.isOpen hxU
  let A := Γ(X, U.1)
  let : Algebra A (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x, hxU⟩
  let px := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
  let pw := (U.2.primeIdealOf ⟨w, hwU⟩).asIdeal
  let f := U.2.fromSpec
  have hfx : f (U.2.primeIdealOf ⟨x, hxU⟩) = x := U.2.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hfw : f (U.2.primeIdealOf ⟨w, hwU⟩) = w := U.2.fromSpec_primeIdealOf ⟨w, hwU⟩
  have hpwx : pw ≤ px := by
    have h1 : f (U.2.primeIdealOf ⟨w, hwU⟩) ⤳ f (U.2.primeIdealOf ⟨x, hxU⟩) := by
      rw [hfx, hfw]
      exact hsp
    exact (PrimeSpectrum.le_iff_specializes _ _).mpr
      (f.isOpenEmbedding.isInducing.specializes_iff.mp h1)
  have hEw : E.ideal U ≤ pw :=
    (mem_support_iff_le_primeIdealOf E U w hwU).mp (by
      obtain ⟨w', -, hw'⟩ := hw.mem
      rw [← hw']
      exact w'.2)
  have hloc : Algebra.NodeFittingIdealSheaf.stalkIdeal E x =
      (E.ideal U).map (algebraMap A (X.presheaf.stalk x)) := stalkIdeal_eq_map_germ _ U hxU
  let P := (Algebra.NodeFittingIdealSheaf.stalkIdeal E x).comap (algebraMap A (X.presheaf.stalk x))
  have hPprime : P.IsPrime := Ideal.comap_isPrime _ _
  have hEP : E.ideal U ≤ P := by
    show E.ideal U ≤ (Algebra.NodeFittingIdealSheaf.stalkIdeal E x).comap _
    rw [hloc]
    exact Ideal.le_comap_map
  have hPw : P ≤ pw := by
    intro a ha
    have ha' : algebraMap A (X.presheaf.stalk x) a ∈
        Algebra.NodeFittingIdealSheaf.stalkIdeal E x := ha
    rw [hloc] at ha'
    have hdisj : Disjoint (px.primeCompl : Set A) pw :=
      Set.disjoint_left.mpr fun b hb hbw ↦ hb (hpwx hbw)
    have hcm := IsLocalization.under_map_of_isPrime_disjoint px.primeCompl (X.presheaf.stalk x)
      (U.2.primeIdealOf ⟨w, hwU⟩).isPrime hdisj
    exact hcm.le (Ideal.map_mono hEw ha')
  -- the point `ζ` of `P` is the generic point `w`
  let ζ : PrimeSpectrum A := ⟨P, hPprime⟩
  have hζU : f ζ ∈ U.1 := by
    have h : f ζ ∈ Set.range f := Set.mem_range_self ζ
    rwa [U.2.range_fromSpec] at h
  have hζpt : U.2.primeIdealOf ⟨f ζ, hζU⟩ = ζ :=
    f.isOpenEmbedding.injective (U.2.fromSpec_primeIdealOf ⟨f ζ, hζU⟩)
  have hζE : f ζ ∈ E.support := by
    rw [mem_support_iff_le_primeIdealOf E U (f ζ) hζU, hζpt]
    exact hEP
  have hζw : f ζ ⤳ w := by
    rw [← hfw]
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp hPw).map f.continuous
  -- maximality of `W`
  let ζ' : E.support := ⟨f ζ, hζE⟩
  have hS : IsIrreducible (closure ({ζ'} : Set E.support)) := isIrreducible_singleton.closure
  have hWS : W ⊆ closure ({ζ'} : Set E.support) := by
    intro v hv
    rw [closure_subtype, Set.image_singleton]
    have hvw : (v : X) ∈ closure ({w} : Set X) := by
      rw [hw.def]
      exact ⟨v, hv, rfl⟩
    exact (specializes_iff_mem_closure.mp (hζw.trans (specializes_iff_mem_closure.mpr hvw)))
  have hSW : closure ({ζ'} : Set E.support) ⊆ W := hW.2 hS hWS
  have hζW : (f ζ : X) ∈ (Subtype.val : E.support → X) '' W :=
    ⟨ζ', hSW (subset_closure rfl), rfl⟩
  have hwζ : w ⤳ f ζ := by
    rw [specializes_iff_mem_closure, hw.def]
    exact hζW
  have hζeq : f ζ = w := (hζw.antisymm hwζ).eq
  have hpwP : pw = P := by
    have : U.2.primeIdealOf ⟨w, hwU⟩ = ζ := by
      apply f.isOpenEmbedding.injective
      rw [hfw, hζeq]
    exact congrArg PrimeSpectrum.asIdeal this
  -- the dimension
  let : Algebra A (X.presheaf.stalk w) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨w, hwU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk w) pw := U.2.isLocalization_stalk ⟨w, hwU⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height pw (X.presheaf.stalk w), hpwP]
  have h1 : P.height = (Algebra.NodeFittingIdealSheaf.stalkIdeal E x).height :=
    IsLocalization.height_under px.primeCompl _
  rw [h1, ht, hheight, Fintype.card_coe]
  rfl

end Codimension

section Main

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q]

include q in
/-- **Normal crossings of multiplicity one are strict normal crossings.** On a regular integral
scheme of finite type over a perfect field, the reduced union of a normal crossings family all of
whose members have multiplicity at most `1` is a strict normal crossings divisor (Codex's
`IsStrictNormalCrossings`, de Jong 2.4). -/
theorem isStrictNormalCrossings_of_isNCFamily (hX : IsRegularScheme X) {r : ℕ}
    {F : Fin r → Closeds X} (hF : IsNCFamily F (fun _ ↦ 1)) :
    IsStrictNormalCrossings (vanishingIdeal (⨆ l, F l)) :=
  ⟨isEffectiveCartierDivisor_vanishingIdeal_iSup q hX hF,
    Geometry.ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme _,
    fun x _ ↦ hX x,
    fun J _ ↦ isRegularScheme_componentIntersection q hX hF J,
    fun J _ ↦ hasPureCodimension_componentIntersection q hX hF J⟩

end Main

end DeJongAlterations.StableModification.Resolution.Strictify
