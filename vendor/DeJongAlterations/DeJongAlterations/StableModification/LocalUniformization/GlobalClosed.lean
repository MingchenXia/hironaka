import DeJongAlterations.StableModification.LocalUniformization.GlobalCentre

/-!
# Closedness of the modification locus over a localized base

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.1 (T:2972–2975) works over the localization `R_𝔭` beneath the centre `x` and
extends the resulting blow-up "trivially" to `C`. Over `R_𝔭` the locus `T` of the transported
blow-up is closed in `C_𝔭 = C ×_R R_𝔭` (strict henselianity, `Blowups.exists_transport`), and `x`
is its only point over `𝔭`. This file shows that `T` is then closed in `C` itself
(`isClosed_of_finite_of_unique`), using that `x` is a closed point of `C`.

**Proof.** If `z ∈ T` specializes to `y ∉ C_𝔭`, choose a valuation ring `V` of `κ(z)` centred at
`y`; its coarsening `V'` at the image of `R ∖ 𝔭` (`coarsening`) is centred at a generization
`y'` of `y` lying over `𝔭` (`coarsening_valuation_lt_one_iff`), hence `y' ∈ T`, `y' = x` and
`y = x`. Blueprint `lem:sm-cofinal-closed` (`sm-local-uniformization.tex`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Topology

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

open ValCurves RiemannZariskiSpace

section Coarsening

variable {K L : Type u} [Field K] [Field L] {O : ValuationSubring K}

/-- **The coarsening of `V` at the image of `O ∖ 𝔭`**: the valuation ring
`{w ∈ L | θ(s) w ∈ V for some s ∉ 𝔭}`. -/
def coarsening (V : ValuationSubring L) (θ : O →+* L) (hθV : ∀ o, θ o ∈ V) (𝔭 : Ideal O)
    [𝔭.IsPrime] : ValuationSubring L where
  carrier := {w | ∃ s : O, s ∉ 𝔭 ∧ θ s * w ∈ V}
  mul_mem' := by
    rintro a b ⟨s₁, hs₁, ha⟩ ⟨s₂, hs₂, hb⟩
    refine ⟨s₁ * s₂, fun h ↦ (‹𝔭.IsPrime›.mem_or_mem h).elim hs₁ hs₂, ?_⟩
    have : θ (s₁ * s₂) * (a * b) = (θ s₁ * a) * (θ s₂ * b) := by rw [map_mul]; ring
    rw [this]
    exact mul_mem ha hb
  one_mem' := ⟨1, ‹𝔭.IsPrime›.one_notMem, by rw [map_one, one_mul]; exact V.one_mem⟩
  add_mem' := by
    rintro a b ⟨s₁, hs₁, ha⟩ ⟨s₂, hs₂, hb⟩
    refine ⟨s₁ * s₂, fun h ↦ (‹𝔭.IsPrime›.mem_or_mem h).elim hs₁ hs₂, ?_⟩
    have : θ (s₁ * s₂) * (a + b) = θ s₂ * (θ s₁ * a) + θ s₁ * (θ s₂ * b) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (hθV _) ha) (mul_mem (hθV _) hb)
  zero_mem' := ⟨1, ‹𝔭.IsPrime›.one_notMem, by rw [mul_zero]; exact V.zero_mem⟩
  neg_mem' := by
    rintro a ⟨s, hs, ha⟩
    exact ⟨s, hs, by rw [mul_neg]; exact neg_mem ha⟩
  mem_or_inv_mem' x := by
    rcases V.mem_or_inv_mem x with h | h
    · exact Or.inl ⟨1, ‹𝔭.IsPrime›.one_notMem, by rw [map_one, one_mul]; exact h⟩
    · exact Or.inr ⟨1, ‹𝔭.IsPrime›.one_notMem, by rw [map_one, one_mul]; exact h⟩

/-- The coarsening contains `V`. -/
theorem le_coarsening (V : ValuationSubring L) (θ : O →+* L) (hθV : ∀ o, θ o ∈ V) (𝔭 : Ideal O)
    [𝔭.IsPrime] : V ≤ coarsening V θ hθV 𝔭 :=
  fun w hw ↦ ⟨1, ‹𝔭.IsPrime›.one_notMem, by rw [map_one, one_mul]; exact hw⟩

/-- **The centre of the coarsening on `Spec O` is `𝔭`**, provided `θ(O ∖ 𝔭) ∌ 0` and `θ(𝔭)` lies
in the maximal ideal of `V`. -/
theorem coarsening_valuation_lt_one_iff (V : ValuationSubring L) (θ : O →+* L)
    (hθV : ∀ o, θ o ∈ V) (𝔭 : Ideal O) [𝔭.IsPrime] (hθ0 : ∀ s, s ∉ 𝔭 → θ s ≠ 0)
    (h𝔭 : ∀ p ∈ 𝔭, V.valuation (θ p) < 1) (o : O) :
    (coarsening V θ hθV 𝔭).valuation (θ o) < 1 ↔ o ∈ 𝔭 := by
  set V' := coarsening V θ hθV 𝔭
  have hmem : ∀ o, θ o ∈ V' := fun o ↦ le_coarsening V θ hθV 𝔭 (hθV o)
  constructor
  · intro hlt
    by_contra ho
    have hinv : (θ o)⁻¹ ∈ V' :=
      ⟨o, ho, by rw [mul_inv_cancel₀ (hθ0 o ho)]; exact V.one_mem⟩
    have h1 : V'.valuation (θ o)⁻¹ ≤ 1 := (V'.valuation_le_one_iff _).mpr hinv
    rw [map_inv₀] at h1
    have h0 : V'.valuation (θ o) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]
      exact hθ0 o ho
    have : 1 ≤ V'.valuation (θ o) := by
      rw [← inv_le_one₀ (pos_iff_ne_zero.mpr h0)]
      exact h1
    exact absurd hlt (not_lt.mpr this)
  · intro ho
    by_cases hz : θ o = 0
    · rw [hz, map_zero]
      exact zero_lt_one
    refine lt_of_le_of_ne ((V'.valuation_le_one_iff _).mpr (hmem o)) fun heq ↦ ?_
    -- `θ o` is a unit of `V'`, so `θ(s) / θ(o) ∈ V` for some `s ∉ 𝔭`
    have hinv : (θ o)⁻¹ ∈ V' := by
      rw [← V'.valuation_le_one_iff, map_inv₀, heq, inv_one]
    obtain ⟨s, hs, hsV⟩ := hinv
    -- in `O`, `s ∣ o`
    obtain ⟨r, hr⟩ : s ∣ o := by
      rcases ValuationRing.dvd_total s o with h | ⟨c, hc⟩
      · exact h
      · exact absurd (hc ▸ Ideal.mul_mem_right c 𝔭 ho) hs
    have hr𝔭 : r ∈ 𝔭 := by
      rw [hr] at ho
      exact (‹𝔭.IsPrime›.mem_or_mem ho).resolve_left hs
    have hθr : θ r ≠ 0 := by
      intro h0
      apply hz
      rw [hr, map_mul, h0, mul_zero]
    have hrinv : (θ r)⁻¹ ∈ V := by
      have : θ s * (θ o)⁻¹ = (θ r)⁻¹ := by
        rw [hr, map_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (hθ0 s hs), one_mul]
      rwa [this] at hsV
    have h1 : V.valuation (θ r)⁻¹ ≤ 1 := (V.valuation_le_one_iff _).mpr hrinv
    have h2 := h𝔭 r hr𝔭
    rw [map_inv₀] at h1
    have h0 : V.valuation (θ r) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]
      exact hθr
    have : 1 ≤ V.valuation (θ r) := by
      rw [← inv_le_one₀ (pos_iff_ne_zero.mpr h0)]
      exact h1
    exact absurd h2 (not_lt.mpr this)

end Coarsening

variable {K : Type u} [Field K] {O : ValuationSubring K}

/-- **Closedness of the modification locus in the whole curve** (`lem:sm-cofinal-closed`). Let
`g : X → Spec O`, `𝔭 ∈ Spec O`, and `T ⊆ X` a finite set of points over generizations of `𝔭`,
closed in `g⁻¹{𝔮 ⊆ 𝔭}` (`hTcl`), whose only point over `𝔭` is a closed point `x` of `X`. Then
`T` is closed in `X`. -/
theorem isClosed_of_finite_of_unique {X : Scheme.{u}} (g : X ⟶ Spec (.of O))
    (𝔭 : PrimeSpectrum O) {T : Set X} (hTfin : T.Finite)
    (hTsub : ∀ z ∈ T, (g z).asIdeal ≤ 𝔭.asIdeal)
    (hTcl : ∀ y ∈ closure T, (g y).asIdeal ≤ 𝔭.asIdeal → y ∈ T) {x : X}
    (hx : IsClosed ({x} : Set X)) (huniq : ∀ y ∈ T, g y = 𝔭 → y = x) : IsClosed T := by
  refine closure_subset_iff_isClosed.mp fun y hy ↦ ?_
  by_cases hyp : (g y).asIdeal ≤ 𝔭.asIdeal
  · exact hTcl y hy hyp
  exfalso
  have htot := (PreValuationRing.iff_ideal_total (R := O)).mp inferInstance
  have h𝔭y : 𝔭.asIdeal ≤ (g y).asIdeal := (htot.total _ _).resolve_left hyp
  -- a point `z ∈ T` specializing to `y`
  have hcl : closure T = ⋃ z ∈ T, closure {z} := by
    conv_lhs => rw [← Set.biUnion_of_singleton T]
    exact hTfin.closure_biUnion _
  rw [hcl, Set.mem_iUnion₂] at hy
  obtain ⟨z, hzT, hzy⟩ := hy
  have hzy' : z ⤳ y := specializes_iff_mem_closure.mpr hzy
  -- the residue field of `z` and a valuation ring of it centred at `y`
  let η : Spec (.of (X.residueField z)) ⟶ X := X.fromSpecResidueField z
  obtain ⟨pt⟩ : Nonempty (Spec (.of (X.residueField z))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  have hηpt : η pt = z := Scheme.fromSpecResidueField_apply z pt
  obtain ⟨V, hV⟩ := exists_isCentre_of_specializes (η := η) (z := pt) (hηpt ▸ hzy')
  let θ : O →+* X.residueField z := (Spec.preimage (η ≫ g)).hom
  have hθ : η ≫ g = Spec.map (CommRingCat.ofHom θ) := (Spec.map_preimage _).symm
  have hVy := hV.ringHom g θ hθ
  -- the kernel of `θ` is `g z ⊆ 𝔭`
  have hker := (isCentre_top (η := η) pt).ringHom g θ hθ
  rw [hηpt] at hker
  have hθ0 : ∀ s, s ∉ 𝔭.asIdeal → θ s ≠ 0 := by
    intro s hs h0
    apply hs
    refine hTsub z hzT ((hker s).2.mpr ?_)
    rw [h0, map_zero]
    exact zero_lt_one
  have h𝔭V : ∀ p ∈ 𝔭.asIdeal, V.valuationSubring.valuation (θ p) < 1 :=
    fun p hp ↦ ((hVy p).2).mp (h𝔭y hp)
  -- the coarsening is centred at a generization `y'` of `y` over `𝔭`
  have hθV : ∀ o, θ o ∈ V.valuationSubring :=
    fun o ↦ (V.valuationSubring.valuation_le_one_iff _).mp (hVy o).1
  let V' : RiemannZariskiSpace (X.residueField z) :=
    ⟨coarsening V.valuationSubring θ hθV 𝔭.asIdeal⟩
  obtain ⟨y', hV', hy'y⟩ :=
    hV.exists_of_le (V' := V') (le_coarsening V.valuationSubring θ hθV 𝔭.asIdeal)
  have hgy' : g y' = 𝔭 := by
    refine PrimeSpectrum.ext (Ideal.ext fun r ↦ ?_)
    rw [((hV'.ringHom g θ hθ) r).2]
    exact coarsening_valuation_lt_one_iff V.valuationSubring θ hθV 𝔭.asIdeal hθ0 h𝔭V r
  have hzy'' : z ⤳ y' := hηpt ▸ hV'.specializes pt
  have hy'T : y' ∈ T := by
    refine hTcl y' ?_ (hgy' ▸ le_rfl)
    exact closure_mono (Set.singleton_subset_iff.mpr hzT)
      (specializes_iff_mem_closure.mp hzy'')
  have hxy : x ⤳ y := huniq y' hy'T hgy' ▸ hy'y
  have hyx : y = x := by
    have := specializes_iff_mem_closure.mp hxy
    rwa [hx.closure_eq, Set.mem_singleton_iff] at this
  apply hyp
  rw [hyx, ← huniq y' hy'T hgy', hgy']

end DeJongAlterations.StableModification.LocalUniformization
