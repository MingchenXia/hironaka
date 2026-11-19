import Hironaka.Resolution.HironakaActualOriginalTaylorPolynomial
import Hironaka.Analytic.HolomorphicGermPointTruncationClosure
import Hironaka.Resolution.HironakaHolomorphicJetChartInvariance

/-! Ordinary local complex algebra maps of whole nonreduced analytic germ
quotients have actual pointed holomorphic lifts. Finite genuine Taylor
polynomials and native Noetherian LOCAL Krull give the ALL-function formula.
BP FIRST: hironaka-nonreduced-quotient-germ-lifting.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology
namespace Hironaka.HironakaNonreducedQuotientGermLifting
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetChartInvariance HironakaActualOriginalTaylorPolynomial

private theorem finite_polynomial_remainder (m k : ℕ) (g : HolGerm (ComplexModel m)) :
    ∃ P : MvPolynomial (Fin m) ℂ,
      g - MvPolynomial.aeval (coordinateGerm : Fin m → HolGerm (ComplexModel m)) P ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel m)) ^ (k+1) := by
  have h : ∀ g : HolGerm (ComplexModel (0+m)),
      ∃ P : MvPolynomial (Fin m) ℂ,
        g-MvPolynomial.aeval (fun i : Fin m => coordinateGerm (i.natAdd 0)) P ∈
          IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+m))) ^ (k+1) := by
    intro g
    refine ⟨originalTaylorPolynomial m k g,?_⟩
    exact originalTaylorPolynomial_remainder m k g
  have transport (l : ℕ) (he : l=m) (σ : Fin m → Fin l)
      (hσ : ∀ i,Fin.cast he (σ i)=i)
      (hh : ∀ g : HolGerm (ComplexModel l),
        ∃ P : MvPolynomial (Fin m) ℂ,
          g-MvPolynomial.aeval (fun i => coordinateGerm (σ i)) P ∈
            IsLocalRing.maximalIdeal (HolGerm (ComplexModel l)) ^ (k+1)) :
      ∀ g : HolGerm (ComplexModel m),
        ∃ P : MvPolynomial (Fin m) ℂ,
          g-MvPolynomial.aeval (coordinateGerm : Fin m → HolGerm (ComplexModel m)) P ∈
            IsLocalRing.maximalIdeal (HolGerm (ComplexModel m)) ^ (k+1) := by
    subst l
    have hs : σ=id := funext fun i => by
      apply Fin.ext
      exact congrArg Fin.val (hσ i)
    rw [hs] at hh
    exact hh
  exact transport (0+m) (Nat.zero_add m) (Fin.natAdd 0)
    (fun i => by
      apply Fin.ext
      change 0+i.val=i.val
      exact Nat.zero_add _) h g

private theorem local_map_power {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f]
    (q : ℕ) {g : R} (hg : g ∈ IsLocalRing.maximalIdeal R ^ q) :
    f g ∈ IsLocalRing.maximalIdeal S ^ q := by
  have h := Ideal.mem_map_of_mem f hg
  rw [Ideal.map_pow] at h
  exact (pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le f) q) h

/-- Ordinary LOCAL maps into a genuine Noetherian local algebra are determined
by original coordinates; finite Taylor remainders and local Krull derive ALL functions. -/
theorem local_algHom_ext_coordinates (m : ℕ) {T : Type*} [CommRing T] [Algebra ℂ T]
    [IsNoetherianRing T] [IsLocalRing T]
    (a b : HolGerm (ComplexModel m) →ₐ[ℂ] T)
    [IsLocalHom a.toRingHom] [IsLocalHom b.toRingHom]
    (hcoord : ∀ i : Fin m, a (coordinateGerm i)=b (coordinateGerm i)) : a=b := by
  have hPoly : a.comp (MvPolynomial.aeval (coordinateGerm : Fin m → HolGerm (ComplexModel m))) =
      b.comp (MvPolynomial.aeval (coordinateGerm : Fin m → HolGerm (ComplexModel m))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply,MvPolynomial.aeval_X] using hcoord i
  apply AlgHom.ext
  intro g
  apply sub_eq_zero.mp
  have hAll : a g-b g ∈ (⨅ q : ℕ,IsLocalRing.maximalIdeal T ^ q : Ideal T) := by
    rw [Submodule.mem_iInf]
    intro q
    obtain ⟨P,hP⟩ := finite_polynomial_remainder m q g
    have hA := local_map_power a.toRingHom (q+1) hP
    have hB := local_map_power b.toRingHom (q+1) hP
    have he : a (MvPolynomial.aeval (coordinateGerm : Fin m → HolGerm (ComplexModel m)) P) =
        b (MvPolynomial.aeval (coordinateGerm : Fin m → HolGerm (ComplexModel m)) P) :=
      congrArg (fun f : MvPolynomial (Fin m) ℂ →ₐ[ℂ] T => f P) hPoly
    have hd : a g-b g ∈ IsLocalRing.maximalIdeal T ^ (q+1) := by
      have h := (IsLocalRing.maximalIdeal T ^ (q+1)).sub_mem hA hB
      change a (g-MvPolynomial.aeval (coordinateGerm : Fin m → HolGerm (ComplexModel m)) P) -
        b (g-MvPolynomial.aeval (coordinateGerm : Fin m → HolGerm (ComplexModel m)) P) ∈ _ at h
      rw [map_sub,map_sub,he] at h
      convert h using 1
      ring
    exact Ideal.pow_le_pow_right (Nat.le_succ q) hd
  rw [(IsLocalRing.maximalIdeal T).iInf_pow_eq_bot_of_isLocalRing
    (IsLocalRing.maximalIdeal.isMaximal T).ne_top] at hAll
  exact Ideal.mem_bot.mp hAll

private theorem composition_eval {m n : ℕ} (F : ComplexModel n → ComplexModel m)
    (hF : ∀ᶠ z in nhds (0 : ComplexModel n),DifferentiableAt ℂ F z) (hF0 : F 0=0)
    (g : HolGerm (ComplexModel m)) : eval (compAlgHom F hF hF0 g)=eval g := by
  induction g using HolGerm.induction_on with
  | h G hG =>
    rw [compAlgHom_mk]
    change G (F 0)=G 0
    rw [hF0]

private theorem composition_local {m n : ℕ} (F : ComplexModel n → ComplexModel m)
    (hF : ∀ᶠ z in nhds (0 : ComplexModel n),DifferentiableAt ℂ F z) (hF0 : F 0=0) :
    IsLocalHom (compAlgHom F hF hF0).toRingHom := by
  refine ⟨fun g hg => ?_⟩
  apply (HolGerm.isUnit_iff_eval_ne_zero g).mpr
  have h := (HolGerm.isUnit_iff_eval_ne_zero (compAlgHom F hF hF0 g)).mp hg
  rwa [composition_eval F hF hF0] at h

/-- An ORDINARY local complex algebra map of arbitrary proper whole germ
quotients internally yields pointed analytic F and the EXACT formula for ALL original germs. -/
theorem exists_pointed_holomorphic_lift (m n : ℕ)
    (I : Ideal (HolGerm (ComplexModel m))) (hI : I ≠ ⊤)
    (J : Ideal (HolGerm (ComplexModel n))) (hJ : J ≠ ⊤)
    (ψ : (HolGerm (ComplexModel m) ⧸ I) →ₐ[ℂ] (HolGerm (ComplexModel n) ⧸ J))
    [IsLocalHom ψ.toRingHom] :
    ∃ (F : ComplexModel n → ComplexModel m)
      (hF : ∀ᶠ z in nhds (0 : ComplexModel n),DifferentiableAt ℂ F z) (hF0 : F 0=0),
      Ideal.map (compAlgHom F hF hF0).toRingHom I ≤ J ∧
      ∀ g : HolGerm (ComplexModel m),
        ψ (Ideal.Quotient.mk I g)=Ideal.Quotient.mk J (compAlgHom F hF hF0 g) := by
  let R := HolGerm (ComplexModel m)
  let S := HolGerm (ComplexModel n)
  let T := S ⧸ J
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : Nontrivial T := Ideal.Quotient.nontrivial_iff.mpr hJ
  let : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalRing T := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S := isNoetherianRing_holGerm_euclidean n
  let : IsNoetherianRing T := inferInstance
  let : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let a : R →ₐ[ℂ] T := ψ.comp (Ideal.Quotient.mkₐ ℂ I)
  let : IsLocalHom a.toRingHom := by
    change IsLocalHom (ψ.toRingHom.comp (Ideal.Quotient.mk I))
    infer_instance
  choose v hv using fun i : Fin m =>
    Ideal.Quotient.mk_surjective (a (coordinateGerm i))
  have hv0 (i : Fin m) : eval (v i)=0 := by
    have hc : coordinateGerm i ∈ IsLocalRing.maximalIdeal R :=
      (HolGerm.mem_maximalIdeal_iff _).mpr rfl
    have hm : a (coordinateGerm i) ∈ IsLocalRing.maximalIdeal T :=
      (IsLocalRing.map_maximalIdeal_le a.toRingHom) (Ideal.mem_map_of_mem _ hc)
    have hn : ¬ IsUnit (a (coordinateGerm i)) := by
      simpa only [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff] using hm
    by_contra he
    have hu := (Ideal.Quotient.mk J).isUnit_map ((HolGerm.isUnit_iff_eval_ne_zero (v i)).mpr he)
    rw [hv i] at hu
    exact hn hu
  choose G hG hrep using fun i : Fin m => HolGerm.exists_eq_mk (v i)
  let F : ComplexModel n → ComplexModel m := fun z =>
    (EuclideanSpace.equiv (Fin m) ℂ).symm (fun i => G i z)
  have hF : ∀ᶠ z in nhds (0 : ComplexModel n),DifferentiableAt ℂ F z := by
    filter_upwards [eventually_all.mpr hG] with z hz
    exact (differentiableAt_piLp 2).mpr hz
  have hF0 : F 0=0 := by
    ext i
    change G i 0=0
    have he : eval (v i)=G i 0 := by rw [hrep i];rfl
    exact he.symm.trans (hv0 i)
  have hCoord (i : Fin m) : compAlgHom F hF hF0 (coordinateGerm i)=v i := by
    rw [hrep i,coordinateGerm,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun _ => rfl
  let b : R →ₐ[ℂ] T := (Ideal.Quotient.mkₐ ℂ J).comp (compAlgHom F hF hF0)
  let : IsLocalHom (compAlgHom F hF hF0).toRingHom := composition_local F hF hF0
  let : IsLocalHom b.toRingHom := by
    change IsLocalHom ((Ideal.Quotient.mk J).comp (compAlgHom F hF hF0).toRingHom)
    infer_instance
  have hEqual : a=b := local_algHom_ext_coordinates m a b (fun i => by
    change a (coordinateGerm i)=Ideal.Quotient.mk J (compAlgHom F hF hF0 (coordinateGerm i))
    rw [hCoord i,hv i])
  have hFormula (g : R) : ψ (Ideal.Quotient.mk I g)=
      Ideal.Quotient.mk J (compAlgHom F hF hF0 g) :=
    congrArg (fun f : R →ₐ[ℂ] T => f g) hEqual
  refine ⟨F,hF,hF0,?_,hFormula⟩
  apply Ideal.map_le_iff_le_comap.mpr
  intro g hg
  change compAlgHom F hF hF0 g ∈ J
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [←hFormula,Ideal.Quotient.eq_zero_iff_mem.mpr hg,map_zero]

end
end Hironaka.HironakaNonreducedQuotientGermLifting
