import DeJongAlterations.Algebra.AffinePrimeDimension
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Fibre dimension of flat algebras

The algebra behind the dimension theory of flat families used in the base step 4.22 of de
Jong (`dejong96-alterations:page-0025`): Temkin's multipointed curves have pure relative
dimension one and zero (Temkin §1.2, `semi-stable.tex` l.1671–1675), which for the flat strict
transforms of de Jong's construction is the classical statement that flat families have
equidimensional fibres (EGA IV 6.1.2).

Let `k` be a field, `R` a finitely generated `k`-domain and `A` a flat `R`-algebra of finite
type. For a prime `P` of `A` over `p ⊆ R` write `trdeg κ(P)/κ(p)` (`relTrdeg`).

* `height_eq_of_minimal_over`: if `P` is minimal among the primes over `p`, then
  `ht P = ht p` (going down for `≥`, Mathlib
  `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`; `P/pA` is a minimal prime for `≤`).
* `exists_minimalPrime_le_height_quotient`: some minimal prime `q ⊆ P` has
  `ht (P/q) ≥ ht P` (the bottom of a maximal chain below `P`).
* `relTrdeg_eq_of_minimal_over` (**the flat dimension formula**): if every minimal prime `q`
  of `A` (which lies over `0`, by going down for flat algebras) has `trdeg κ(q)/Frac R = n`, then every prime `P`
  minimal over its contraction `p` has `trdeg κ(P)/κ(p) = n`. Proof: with `q` as above,
  Codex's dimension formula for finitely generated domains
  (`Algebra.AffinePrimeDimension.height_add_quotient_dimension`) applied to `R` at `p` and to
  `A/q` at `P/q` gives `ht p + dim R/p = dim R` and `ht p + dim A/P = dim A/q = dim R + n`;
  dimensions of quotients are transcendence degrees of residue fields.
* `exists_ringKrullDim_fiber_quotient`: for a prime `Q` of the fibre ring `κ(p) ⊗_R A` over the
  prime `P` of `A`, `dim (κ(p) ⊗_R A)/Q = trdeg κ(P)/κ(p)`, since `(κ(p) ⊗_R A)/Q` is a finitely
  generated `κ(p)`-domain with fraction field `κ(P)`.
-/

noncomputable section

open scoped TensorProduct

namespace DeJongAlterations.StableModification.DeJong.FlatDimension

universe u

section Residue

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The residue field extension `κ(p) → κ(P)` for a prime `P` of `A` over a prime `p` of `R`. -/
abbrev residueAlgebra (p : Ideal R) [p.IsPrime] (P : Ideal A) [P.IsPrime]
    (h : p = P.comap (algebraMap R A)) : Algebra p.ResidueField P.ResidueField :=
  (Ideal.ResidueField.map p P (algebraMap R A) h).toAlgebra

/-- The relative transcendence degree `trdeg κ(P)/κ(p)`. -/
def relTrdeg (p : Ideal R) [p.IsPrime] (P : Ideal A) [P.IsPrime]
    (h : p = P.comap (algebraMap R A)) : Cardinal.{u} :=
  let := residueAlgebra p P h
  Algebra.trdeg p.ResidueField P.ResidueField

/-- Transcendence degrees of residue fields are additive in towers. -/
theorem trdeg_residueField_eq_add (k : Type u) [Field k] [Algebra k R] [Algebra k A]
    [IsScalarTower k R A] (p : Ideal R) [p.IsPrime] (P : Ideal A) [P.IsPrime]
    (h : p = P.comap (algebraMap R A)) :
    Algebra.trdeg k P.ResidueField = Algebra.trdeg k p.ResidueField + relTrdeg p P h := by
  let := residueAlgebra p P h
  have : IsScalarTower k p.ResidueField P.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
    change algebraMap k P.ResidueField c =
      Ideal.ResidueField.map p P (algebraMap R A) h (algebraMap k p.ResidueField c)
    rw [IsScalarTower.algebraMap_apply k R p.ResidueField, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have : FaithfulSMul k p.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k p.ResidueField).injective
  have : FaithfulSMul p.ResidueField P.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap p.ResidueField P.ResidueField).injective
  exact (trdeg_add_eq k p.ResidueField (A := P.ResidueField)).symm

/-- The dimension of a quotient of a finitely generated algebra over a field by a prime is the
transcendence degree of the residue field. -/
theorem exists_ringKrullDim_quotient_eq_trdeg (k B : Type u) [Field k] [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] (P : Ideal B) [P.IsPrime] :
    ∃ d : ℕ, ringKrullDim (B ⧸ P) = d ∧ Algebra.trdeg k P.ResidueField = d :=
  Algebra.FunctionFieldDimension.exists_dimension_and_trdeg k (B ⧸ P) P.ResidueField

end Residue

section Heights

variable {A : Type u} [CommRing A]

/-- The image of a prime containing `q` in `A ⧸ q` is prime. -/
theorem isPrime_map_quotient (q P : Ideal A) [P.IsPrime] (h : q ≤ P) :
    (P.map (Ideal.Quotient.mk q)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

theorem comap_map_quotient (q P : Ideal A) (h : q ≤ P) :
    (P.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = P := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr h]

/-- Heights do not increase when passing to a quotient. -/
theorem height_map_quotient_le (q P : Ideal A) [P.IsPrime] (h : q ≤ P) :
    have := isPrime_map_quotient q P h
    (P.map (Ideal.Quotient.mk q)).height ≤ P.height := by
  have := isPrime_map_quotient q P h
  let f : PrimeSpectrum (A ⧸ q) → PrimeSpectrum A := PrimeSpectrum.comap (Ideal.Quotient.mk q)
  have hf : StrictMono f := by
    refine Monotone.strictMono_of_injective (fun a b hab ↦ Ideal.comap_mono hab) ?_
    intro a b hab
    ext1
    have := congrArg PrimeSpectrum.asIdeal hab
    simpa [f, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] using
      congrArg (Ideal.map (Ideal.Quotient.mk q)) this
  have H := Order.height_le_height_apply_of_strictMono f hf
    ⟨P.map (Ideal.Quotient.mk q), inferInstance⟩
  rw [← PrimeSpectrum.height_eq_orderHeight] at H
  convert H using 1
  rw [← PrimeSpectrum.height_eq_orderHeight]
  congr 1
  exact (comap_map_quotient q P h).symm

/-- Some minimal prime `q ⊆ P` satisfies `ht (P/q) ≥ ht P`. -/
theorem exists_minimalPrime_le_height_quotient [IsNoetherianRing A] (P : Ideal A) [P.IsPrime] :
    ∃ q ∈ minimalPrimes A, ∃ h : q ≤ P,
      have := isPrime_map_quotient q P h
      P.height ≤ (P.map (Ideal.Quotient.mk q)).height := by
  obtain ⟨l, hlast, hlen⟩ := P.exists_ltSeries_length_eq_height
  obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ l.head.asIdeal)
  have hmem : ∀ i, q ≤ (l i).asIdeal := fun i ↦
    hqle.trans (l.monotone (Fin.zero_le i))
  have hqP : q ≤ P := by
    have := hmem (Fin.last _)
    rwa [show l (Fin.last _) = l.last from rfl, hlast] at this
  refine ⟨q, hq, hqP, ?_⟩
  have := isPrime_map_quotient q P hqP
  let l' : LTSeries (PrimeSpectrum (A ⧸ q)) :=
    { length := l.length
      toFun := fun i ↦ ⟨(l i).asIdeal.map (Ideal.Quotient.mk q),
        isPrime_map_quotient q _ (hmem i)⟩
      step := fun i ↦ by
        have hlt := l.step i
        change (l i.castSucc) < (l i.succ) at hlt
        change (l i.castSucc).asIdeal.map (Ideal.Quotient.mk q) <
          (l i.succ).asIdeal.map (Ideal.Quotient.mk q)
        refine lt_of_le_of_ne (Ideal.map_mono hlt.le) fun heq ↦ hlt.ne ?_
        ext1
        rw [← comap_map_quotient q _ (hmem i.castSucc), heq, comap_map_quotient q _ (hmem i.succ)] }
  have H := Order.length_le_height_last (p := l')
  have hlast' : l'.last = ⟨P.map (Ideal.Quotient.mk q), inferInstance⟩ := by
    ext1
    change (l (Fin.last _)).asIdeal.map _ = _
    rw [show l (Fin.last _) = l.last from rfl, hlast]
  rw [hlast', ← PrimeSpectrum.height_eq_orderHeight] at H
  rw [← hlen]
  exact H

end Heights

section Flat

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Over a domain, every minimal prime of a flat algebra lies over `0` (going down). -/
theorem comap_eq_bot_of_mem_minimalPrimes [IsDomain R] [Module.Flat R A] (q : Ideal A)
    (hq : q ∈ minimalPrimes A) : q.comap (algebraMap R A) = ⊥ := by
  have : q.IsPrime := hq.1.1
  by_contra hne
  have hlt : (⊥ : Ideal R) < q.comap (algebraMap R A) := bot_lt_iff_ne_bot.mpr hne
  have : q.LiesOver (q.comap (algebraMap R A)) := ⟨rfl⟩
  obtain ⟨P', hP'lt, hP', -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt q hlt
  exact hP'lt.not_ge (hq.2 ⟨hP', bot_le⟩ hP'lt.le)

/-- **Heights over a prime.** If `A` is flat over `R` and `P` is minimal among the primes of
`A` over `p`, then `ht P = ht p`. -/
theorem height_eq_of_minimal_over [IsNoetherianRing R] [IsNoetherianRing A] [Module.Flat R A]
    (p : Ideal R) [p.IsPrime] (P : Ideal A) [P.IsPrime]
    (hPp : P.comap (algebraMap R A) = p)
    (hmin : ∀ P' : Ideal A, P'.IsPrime → P'.comap (algebraMap R A) = p → P' ≤ P → P' = P) :
    P.height = p.height := by
  have : P.LiesOver p := ⟨hPp.symm⟩
  apply le_antisymm
  · have H := Ideal.height_le_height_add_of_liesOver p P
    let I := p.map (algebraMap R A)
    have hIP : I ≤ P := Ideal.map_le_iff_le_comap.mpr hPp.ge
    have hPI : P ∈ I.minimalPrimes := by
      refine ⟨⟨inferInstance, hIP⟩, fun J hJ hJP ↦ ?_⟩
      have : J.IsPrime := hJ.1
      have hJp : J.comap (algebraMap R A) = p :=
        le_antisymm ((Ideal.comap_mono hJP).trans hPp.le)
          (Ideal.map_le_iff_le_comap.mp hJ.2)
      exact (hmin J hJ.1 hJp hJP).ge
    rw [Ideal.minimalPrimes_eq_comap] at hPI
    obtain ⟨Q, hQ, hQP⟩ := hPI
    have : Q.IsPrime := hQ.1.1
    have hmap : P.map (Ideal.Quotient.mk I) = Q := by
      rw [← hQP, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have h0 : (P.map (Ideal.Quotient.mk I)).height = 0 := by
      rw [hmap]
      exact Ideal.height_eq_zero_iff.mpr hQ
    rw [h0, add_zero] at H
    exact H
  · rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P]
    exact le_self_add

/-- **The flat dimension formula.** Let `R` be a finitely generated domain over a field `k` and
`A` a flat `R`-algebra of finite type. If every minimal prime `q` of `A` has
`trdeg κ(q)/Frac R = n`, then every prime `P` of `A` which is minimal among the primes over
its contraction `p` has `trdeg κ(P)/κ(p) = n`. -/
theorem relTrdeg_eq_of_minimal_over (k : Type u) [Field k] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [Algebra.FiniteType R A] [Module.Flat R A] (n : ℕ)
    (hgen : ∀ (q : Ideal A) (hq : q ∈ minimalPrimes A),
      haveI := hq.1.1
      ∀ h : (⊥ : Ideal R) = q.comap (algebraMap R A), relTrdeg ⊥ q h = n)
    (p : Ideal R) [p.IsPrime] (P : Ideal A) [P.IsPrime] (hPp : p = P.comap (algebraMap R A))
    (hmin : ∀ P' : Ideal A, P'.IsPrime → P'.comap (algebraMap R A) = p → P' ≤ P → P' = P) :
    relTrdeg p P hPp = n := by
  let : Algebra k A := ((algebraMap R A).comp (algebraMap k R)).toAlgebra
  have : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  -- heights
  have hht : P.height = p.height := height_eq_of_minimal_over p P hPp.symm hmin
  obtain ⟨q, hq, hqP, hqht⟩ := exists_minimalPrime_le_height_quotient P
  have : q.IsPrime := hq.1.1
  have := isPrime_map_quotient q P hqP
  have hqht' : (P.map (Ideal.Quotient.mk q)).height = p.height :=
    le_antisymm ((height_map_quotient_le q P hqP).trans hht.le) (hht ▸ hqht)
  have hq0 : (⊥ : Ideal R) = q.comap (algebraMap R A) :=
    (comap_eq_bot_of_mem_minimalPrimes q hq).symm
  -- dimensions of quotients
  obtain ⟨tR, hR, htR⟩ := exists_ringKrullDim_quotient_eq_trdeg k R (⊥ : Ideal R)
  obtain ⟨tp, hp, htp⟩ := exists_ringKrullDim_quotient_eq_trdeg k R p
  obtain ⟨tP, hP, htP⟩ := exists_ringKrullDim_quotient_eq_trdeg k A P
  obtain ⟨tq, hqd, htq⟩ := exists_ringKrullDim_quotient_eq_trdeg k A q
  have hRdim : ringKrullDim R = tR := by
    rw [← hR]; exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)).symm
  -- the dimension formula for `R` at `p` and for `A ⧸ q` at `P ⧸ q`
  have hfR := Algebra.AffinePrimeDimension.height_add_quotient_dimension k R p
  have hfB := Algebra.AffinePrimeDimension.height_add_quotient_dimension k (A ⧸ q)
    (P.map (Ideal.Quotient.mk q))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hqP), hP, hqd,
    hqht'] at hfB
  rw [hp, hRdim] at hfR
  -- transcendence degrees
  have htowP := trdeg_residueField_eq_add k p P hPp
  have htowq := trdeg_residueField_eq_add k (⊥ : Ideal R) q hq0
  rw [hgen q hq hq0, htR, htq] at htowq
  rw [htp, htP] at htowP
  -- arithmetic
  obtain ⟨h, hh⟩ : ∃ h : ℕ, p.height = h :=
    ENat.ne_top_iff_exists.mp (Ideal.height_ne_top (Ideal.IsPrime.ne_top ‹_›)) |>.imp
      fun _ h ↦ h.symm
  rw [hh] at hfR hfB
  have e1 : h + tp = tR := by exact_mod_cast hfR
  have e2 : h + tP = tq := by exact_mod_cast hfB
  have e3 : tq = tR + n := by exact_mod_cast htowq
  have hle : relTrdeg p P hPp ≤ tP := by
    rw [htowP]; exact le_add_self
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp (hle.trans_lt (Cardinal.natCast_lt_aleph0 (n := tP)))
  rw [hm] at htowP ⊢
  have e4 : tP = tp + m := by exact_mod_cast htowP
  have : m = n := by omega
  rw [this]

end Flat

section FiberRing

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The evaluation `κ(p) ⊗_R A → κ(P)` of the fibre ring at a prime `P` over `p`. -/
def fiberEval (p : PrimeSpectrum R) (P : Ideal A) [P.IsPrime]
    (hP : p.asIdeal = P.comap (algebraMap R A)) : p.asIdeal.Fiber A →ₐ[R] P.ResidueField :=
  Algebra.TensorProduct.lift (Ideal.ResidueField.mapₐ p.asIdeal P (Algebra.ofId R A) hP)
    (IsScalarTower.toAlgHom R A P.ResidueField) (fun _ _ ↦ .all _ _)

theorem fiberEval_tmul (p : PrimeSpectrum R) (P : Ideal A) [P.IsPrime]
    (hP : p.asIdeal = P.comap (algebraMap R A)) (x : p.asIdeal.ResidueField) (a : A) :
    fiberEval p P hP (x ⊗ₜ a) =
      Ideal.ResidueField.map p.asIdeal P (algebraMap R A) hP x * algebraMap A P.ResidueField a := by
  simp only [fiberEval, Algebra.TensorProduct.lift_tmul]
  rfl

/-- **Components of a fibre ring.** For a prime `Q` of the fibre ring `κ(p) ⊗_R A`, with
`P ⊆ A` the corresponding prime over `p`, the dimension of `(κ(p) ⊗_R A)/Q` is
`trdeg κ(P)/κ(p)`. -/
theorem exists_ringKrullDim_fiber_quotient [Algebra.FiniteType R A] (p : PrimeSpectrum R)
    (Q : PrimeSpectrum (p.asIdeal.Fiber A)) :
    ∃ (h : p.asIdeal = ((PrimeSpectrum.preimageEquivFiber R A p).symm Q).1.asIdeal.comap
        (algebraMap R A)) (d : ℕ),
      ringKrullDim (p.asIdeal.Fiber A ⧸ Q.asIdeal) = d ∧
        relTrdeg p.asIdeal ((PrimeSpectrum.preimageEquivFiber R A p).symm Q).1.asIdeal h = d := by
  let Pt := (PrimeSpectrum.preimageEquivFiber R A p).symm Q
  let P := Pt.1.asIdeal
  have hP : p.asIdeal = P.comap (algebraMap R A) := by
    have := Pt.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
    exact (congrArg PrimeSpectrum.asIdeal this).symm
  refine ⟨hP, ?_⟩
  let ev := fiberEval p P hP
  have hker : RingHom.ker ev.toRingHom = Q.asIdeal := by
    have := (PrimeSpectrum.preimageEquivFiber R A p).apply_symm_apply Q
    have h2 := congrArg PrimeSpectrum.asIdeal this
    rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal] at h2
    exact h2
  let ι : p.asIdeal.Fiber A ⧸ Q.asIdeal →+* P.ResidueField :=
    Ideal.Quotient.lift Q.asIdeal ev.toRingHom fun a ha ↦ (RingHom.mem_ker).mp (hker ▸ ha)
  have hι : ∀ x, ι (Ideal.Quotient.mk _ x) = ev x := fun _ ↦ rfl
  have hinj : Function.Injective ι := RingHom.lift_injective_of_ker_le_ideal _ _ hker.le
  let algQ : Algebra (p.asIdeal.Fiber A ⧸ Q.asIdeal) P.ResidueField := ι.toAlgebra
  have halg : @algebraMap _ _ _ _ algQ = ι := rfl
  let := residueAlgebra p.asIdeal P hP
  have : IsScalarTower p.asIdeal.ResidueField (p.asIdeal.Fiber A ⧸ Q.asIdeal) P.ResidueField := by
    set_option backward.isDefEq.respectTransparency false in
    refine IsScalarTower.of_algebraMap_eq (R := p.asIdeal.ResidueField)
      (S := p.asIdeal.Fiber A ⧸ Q.asIdeal) (A := P.ResidueField) fun x ↦ ?_
    change Ideal.ResidueField.map p.asIdeal P (algebraMap R A) hP x =
      ι (Ideal.Quotient.mk _ (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber A) x))
    rw [hι, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      fiberEval_tmul, map_one, mul_one]
  have : FaithfulSMul (p.asIdeal.Fiber A ⧸ Q.asIdeal) P.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hA : ∀ a : A, algebraMap A P.ResidueField a =
      ι (Ideal.Quotient.mk Q.asIdeal ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] a)) := by
    intro a
    rw [hι, fiberEval_tmul, map_one, one_mul]
  have : IsFractionRing (p.asIdeal.Fiber A ⧸ Q.asIdeal) P.ResidueField := by
    refine IsFractionRing.of_field (p.asIdeal.Fiber A ⧸ Q.asIdeal) P.ResidueField fun z ↦ ?_
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A ⧸ P) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Ideal.Quotient.mk Q.asIdeal ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] a),
      Ideal.Quotient.mk Q.asIdeal ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] b), ?_⟩
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk,
      hA, hA]
    rw [halg]
  exact Algebra.FunctionFieldDimension.exists_dimension_and_trdeg p.asIdeal.ResidueField
    (p.asIdeal.Fiber A ⧸ Q.asIdeal) P.ResidueField

end FiberRing

end DeJongAlterations.StableModification.DeJong.FlatDimension
