import TranscendentalNakamaye.Pending.HironakaActualNormalAxisDehomogenization
import TranscendentalNakamaye.Pending.HironakaActualFormalBlowupAllDirections
import TranscendentalNakamaye.Pending.HironakaActualAnalyticFormalNormalPowers
import TranscendentalNakamaye.Pending.HironakaActualRelativeTaylorCoefficients

/-!
# Whole relative polynomial rehomogenization over the original analytic tangent ring

Literal finite normal-polynomial formulas retain every entire tangent coefficient.
Genuine analytic blowup factorization and the actual injective Taylor/formal
blowup dictionary prove fixed-degree dehomogenization injectivity, then lift
all finite pivot-free whole relations. No desired homogeneous lift, analytic
relation or exceptional regularity is supplied as a certificate.
Blueprint: `hironaka-actual-relative-polynomial-rehomogenization-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace TranscendentalNakamaye.Pending.HironakaActualRelativePolynomialRehomogenization
noncomputable section
open FirstPass HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualNormalAxisDehomogenization HironakaActualFormalBlowupAllDirections
  HironakaActualNormalQuotientExceptionalRestriction HironakaActualAnalyticBlowupTaylor
  HironakaActualRelativeTaylorCoefficients
  HironakaActualAnalyticFormalNormalPowers HironakaActualFormalCoordinatePowerDivision
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalBlowupMemberGeneration
variable {d t : ℕ}
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t

def relativePolynomialDehomogenization (e : Fin t) (b : Fin (d+t) → ℂ) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) →ₐ[HolGerm (ComplexModel d)]
      MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  MvPolynomial.aeval (fun i => if i=e then 1 else MvPolynomial.C (HolGerm.constHom (b (i.natAdd d)))+MvPolynomial.X i)

/-- A literal finite sum using the actual pivot and direction parameters. -/
def relativePolynomialRehomogenization (e : Fin t) (b : Fin (d+t) → ℂ)
    (m : ℕ) (q : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) : MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  ∑ α ∈ q.support, MvPolynomial.X e ^ (m-α.degree) *
    MvPolynomial.aeval (fun i => MvPolynomial.X i-MvPolynomial.C (HolGerm.constHom (b (i.natAdd d)))*MvPolynomial.X e)
      (MvPolynomial.monomial α (MvPolynomial.coeff α q))

/-- Whole finite-degree rehomogenization is genuinely homogeneous. -/
theorem relativePolynomialRehomogenization_homogeneous (e : Fin t) (b : Fin (d+t) → ℂ)
    (m : ℕ) (q : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (hq : q.totalDegree ≤ m) :
    (relativePolynomialRehomogenization e b m q).IsHomogeneous m := by
  apply MvPolynomial.IsHomogeneous.sum
  intro α hα
  have hdeg : α.degree ≤ m := (MvPolynomial.le_totalDegree hα).trans hq
  have hlin (i : Fin t) :
      (MvPolynomial.X i-MvPolynomial.C (HolGerm.constHom (b (i.natAdd d)))*MvPolynomial.X e : MvPolynomial (Fin t) (HolGerm (ComplexModel d))).IsHomogeneous 1 :=
    (MvPolynomial.isHomogeneous_X (HolGerm (ComplexModel d)) i).sub (MvPolynomial.isHomogeneous_C_mul_X (HolGerm.constHom (b (i.natAdd d))) e)
  have hmon := (MvPolynomial.isHomogeneous_monomial (d := α) (MvPolynomial.coeff α q) rfl).aeval _ hlin
  have hprod := (MvPolynomial.isHomogeneous_X_pow e (m-α.degree)).mul hmon
  simpa only [one_mul,Nat.sub_add_cancel hdeg] using hprod

/-- The same actual dehomogenization recovers EVERY original finite coefficient. -/
theorem relativePolynomialDehomogenization_rehomogenization (e : Fin t) (b : Fin (d+t) → ℂ)
    (m : ℕ) (q : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hpivot : ∀ α ∈ q.support, α e = 0) :
    relativePolynomialDehomogenization e b (relativePolynomialRehomogenization e b m q) = q := by
  rw [relativePolynomialRehomogenization,map_sum]
  conv_rhs => rw [← q.support_sum_monomial_coeff]
  apply Finset.sum_congr rfl
  intro α hα
  rw [map_mul,map_pow]
  have he : relativePolynomialDehomogenization e b (MvPolynomial.X e) = 1 := by
    simp [relativePolynomialDehomogenization]
  rw [he,one_pow,one_mul,MvPolynomial.aeval_monomial,MvPolynomial.monomial_eq]
  simp only [Finsupp.prod,map_mul,map_prod,map_pow,AlgHom.commutes]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hie : i ≠ e := by
    intro h
    subst i
    exact (Finsupp.mem_support_iff.mp hi) (hpivot α hα)
  simp [relativePolynomialDehomogenization,hie]


/-- Whole relative evaluation retains each actual tangent coefficient. -/
theorem relativePolynomialDehomogenization_eval (e : Fin t) (b : Fin (d+t) → ℂ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    normalPolynomialEval d t (relativePolynomialDehomogenization e b P)=
      actualDehomogenizedNormalPolynomialEval d t e b P := by
  have ht (c : HolGerm (ComplexModel d)) : algebraMap (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) c=tangentPullback d t c := rfl
  have hc (c : ℂ) : tangentPullback d t (HolGerm.constHom c)=algebraMap ℂ (HolGerm (ComplexModel (d+t))) c :=
    (tangentPullback d t).commutes c
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp only [relativePolynomialDehomogenization,MvPolynomial.aeval_C]
    rw [(normalPolynomialEval d t).commutes c]
    unfold actualDehomogenizedNormalPolynomialEval
    rw [MvPolynomial.eval₂Hom_C]
    exact ht c
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP =>
    rw [map_mul,map_mul,hP]
    by_cases hi : i=e <;>
      simp [relativePolynomialDehomogenization,normalPolynomialEval,actualDehomogenizedNormalPolynomialEval,hi,ht,hc]

private theorem normalPolynomialEval_injective (d t : ℕ) : Function.Injective (normalPolynomialEval d t) := by
  intro P Q h
  apply MvPolynomial.ext
  intro γ
  apply actualUnshiftedTaylorAlgHom_injective d
  simpa only [actualFormalNormalCoefficient_normalPolynomialEval] using
    congrArg (fun g => actualFormalNormalCoefficient (actualUnshiftedTaylorAlgHom (d+t) g) γ) h

/-- Genuine analytic blowup and Taylor injectivity prove whole homogeneous polynomial injection. -/
theorem relativePolynomialDehomogenization_homogeneous_injective (e : Fin t) (b : Fin (d+t) → ℂ)
    (D : ℕ) (P Q : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hP : P.IsHomogeneous D) (hQ : Q.IsHomogeneous D)
    (h : relativePolynomialDehomogenization e b P=relativePolynomialDehomogenization e b Q) : P=Q := by
  apply normalPolynomialEval_injective d t
  apply actualUnshiftedTaylorAlgHom_injective (d+t)
  apply actualFormalBlowup_injective (actualTangentCentreVariables d t) (e.natAdd d) ⟨e,rfl⟩ b
  have hn (g : HolGerm (ComplexModel (d+t))) :=
    DFunLike.congr_fun (actualTaylor_analyticBlowupPullback (actualTangentCentreVariables d t) (e.natAdd d) b) g
  change actualFormalBlowup (actualTangentCentreVariables d t) (e.natAdd d) b
      (actualUnshiftedTaylorAlgHom (d+t) (normalPolynomialEval d t P))=
    actualFormalBlowup (actualTangentCentreVariables d t) (e.natAdd d) b
      (actualUnshiftedTaylorAlgHom (d+t) (normalPolynomialEval d t Q))
  simp only [AlgHom.comp_apply] at hn
  rw [←hn (normalPolynomialEval d t P),←hn (normalPolynomialEval d t Q)]
  apply congrArg (actualUnshiftedTaylorAlgHom (d+t))
  rw [actualAnalyticBlowupPullback_normalPolynomial_homogeneous d t e b P D hP,
    actualAnalyticBlowupPullback_normalPolynomial_homogeneous d t e b Q D hQ]
  change _ * actualDehomogenizedNormalPolynomialEval d t e b P=
    _ * actualDehomogenizedNormalPolynomialEval d t e b Q
  rw [←relativePolynomialDehomogenization_eval,←relativePolynomialDehomogenization_eval,h]

/-- A natural finite degree bound and a literal pivot-independent polynomial
chart relation produce a true homogeneous original relation at that degree. -/
theorem relative_homogeneous_polynomial_relation_lift_at_degree {ι : Type*} [Fintype ι]
    (e : Fin t) (b : Fin (d+t) → ℂ) (f q : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (w : ι → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (w i))
    (hq : ∀ i α, α ∈ (q i).support → α e = 0)
    (hrel : (∑ i, q i * relativePolynomialDehomogenization e b (f i)) = 0)
    (D : ℕ) (hD : ∀ i, w i + (q i).totalDegree ≤ D) :
    ∃ P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d)),
      (∀ i, (P i).IsHomogeneous (D-w i)) ∧
      (∀ i, relativePolynomialDehomogenization e b (P i) = q i) ∧
      (∑ i, P i * f i) = 0 := by
  let P := fun i => relativePolynomialRehomogenization e b (D-w i) (q i)
  have hhom (i : ι) : (P i).IsHomogeneous (D-w i) := by
    apply relativePolynomialRehomogenization_homogeneous
    have := hD i
    omega
  have heval (i : ι) : relativePolynomialDehomogenization e b (P i) = q i :=
    relativePolynomialDehomogenization_rehomogenization e b (D-w i) (q i) (hq i)
  refine ⟨P,hhom,heval,?_⟩
  have hsum : (∑ i, P i * f i).IsHomogeneous D := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    have hw : w i ≤ D := (Nat.le_add_right _ _).trans (hD i)
    simpa only [Nat.sub_add_cancel hw] using (hhom i).mul (hf i)
  apply relativePolynomialDehomogenization_homogeneous_injective e b D _ 0 hsum
    (MvPolynomial.isHomogeneous_zero (Fin t) (HolGerm (ComplexModel d)) D)
  simpa only [map_sum,map_mul,heval,map_zero] using hrel

/-- One internally chosen common degree lifts EVERY given finite original
pivot-independent chart relation; no homogeneous output is a premise. -/
theorem exists_relative_homogeneous_polynomial_relation_lift {ι : Type*} [Fintype ι]
    (e : Fin t) (b : Fin (d+t) → ℂ) (f q : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (w : ι → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (w i))
    (hq : ∀ i α, α ∈ (q i).support → α e = 0)
    (hrel : (∑ i, q i * relativePolynomialDehomogenization e b (f i)) = 0) :
    ∃ (D : ℕ) (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))),
      (∀ i, w i ≤ D) ∧ (∀ i, (P i).IsHomogeneous (D-w i)) ∧
      (∀ i, relativePolynomialDehomogenization e b (P i) = q i) ∧ (∑ i, P i * f i) = 0 := by
  let D := ∑ i, (w i + (q i).totalDegree)
  have hD (i : ι) : w i + (q i).totalDegree ≤ D := by
    change w i + (q i).totalDegree ≤ ∑ j, (w j + (q j).totalDegree)
    exact Finset.single_le_sum (f := fun j : ι => w j + (q j).totalDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  obtain ⟨P,hP,heval,hwhole⟩ := relative_homogeneous_polynomial_relation_lift_at_degree e b f q w hf hq hrel D hD
  exact ⟨D,P,fun i => (Nat.le_add_right _ _).trans (hD i),hP,heval,hwhole⟩

end
end TranscendentalNakamaye.Pending.HironakaActualRelativePolynomialRehomogenization
