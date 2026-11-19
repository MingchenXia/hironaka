import Mathlib.RingTheory.Derivation.Basic
import Hironaka.Resolution.HironakaActualHomogenizedTangentStability

/-! Finite actual Euler recovery for contact-coordinate powers, before its
genuine native coordinate/derivation and canonical-history consumers.
Blueprint: hironaka-actual-euler-contact-power-recovery-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualEulerContactPowerRecovery
noncomputable section
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  GermIdealPullbackCalculus IdealWeightPowers IdealOrderArithmetic DerivativeIdeal
  HironakaActualHomogenizedTangentStability

section Manifold
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem mul_mono {A A' B B' : GermIdeal n X} (hA : A.Le A') (hB : B.Le B') :
    (A.mul B).Le (A'.mul B'):=by
  intro x g hg
  exact IdealOrderArithmetic.mem_mul_iff.mpr ((IdealOrderArithmetic.mem_mul_iff.mp hg).mono
    (fun _ ⟨a,b,ha,hb,he⟩=>⟨a,b,hA x a ha,hB x b hb,he⟩))

/-- SAME-tangent stability absorbs ALL actual derivative powers, including0. -/
theorem iterDeriv_tangent_absorption {A T : GermIdeal n X}
    (hA : A.IsCoherent) (hT : T.IsCoherent) (hStable : ((derivIdeal A).mul T).Le A) :
    ∀j,((iterDerivIdeal A j).mul (idealPow T j)).Le A
  | 0=>by
    rw [iterDerivIdeal_zero,idealPow_zero,RestrictLeCalculus.mul_unitIdeal hA]
    exact fun _ _ h=>h
  | j+1=>by
    rw [idealPow_succ,RestrictLeCalculus.mul_comm' (idealPow T j) T,
      ←GermIdealTotalTransform.mul_assoc (isCoherent_iterDerivIdeal hA (j+1)) hT
        (isCoherent_idealPow hT j)]
    have hLe:=mul_mono (B:=idealPow T j) (B':=idealPow T j)
      (iterDeriv_tangent_stability hA hT hStable j) (fun _ _ h=>h)
    exact fun x g hg=>iterDeriv_tangent_absorption hA hT hStable j x g (hLe x g hg)
end Manifold

section Algebra
variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Literal finite iterates of the ACTUAL supplied derivation. -/
def iteratedDerivation (δ : Derivation ℂ R R) : ℕ→R→R
  | 0=>id
  | k+1=>fun f=>δ (iteratedDerivation δ k f)

/-- The true coordinate-power Euler identity, in the actual complex algebra. -/
theorem euler_coordinate_power (δ : Derivation ℂ R R) {t : R} (ht : δ t=1)
    (k : ℕ) (f : R) : t*δ (t^k*f)=(k : R)*t^k*f+t^(k+1)*δ f:=by
  induction k with
  | zero=>simp
  | succ k ih=>
    calc
      t*δ (t^(k+1)*f)=t*(t*δ (t^k*f)+t^k*f):=by
        rw [show t^(k+1)*f=t*(t^k*f) by ring,δ.leibniz,ht]
        simp only [smul_eq_mul,mul_one]
      _=(k+1 : ℕ)*t^(k+1)*f+t^(k+1+1)*δ f:=by
        rw [mul_add,ih]
        simp only [Nat.cast_succ,pow_succ]
        ring

/-- True finite Leibniz identity for an ACTUAL coordinate with δt=1. -/
theorem iteratedDerivation_coordinate_mul (δ : Derivation ℂ R R) {t : R} (ht : δ t=1) :
    ∀k f,iteratedDerivation δ (k+1) (t*f)=
      t*iteratedDerivation δ (k+1) f+(k+1 : ℕ)*iteratedDerivation δ k f
  | 0,f=>by simp [iteratedDerivation,δ.leibniz,ht,smul_eq_mul,add_comm]
  | k+1,f=>by
    change δ (iteratedDerivation δ (k+1) (t*f))=_
    rw [iteratedDerivation_coordinate_mul δ ht k f,δ.map_add,δ.leibniz,ht,
      δ.leibniz,δ.map_natCast]
    simp only [smul_eq_mul,mul_one,mul_zero,add_zero,iteratedDerivation,Nat.cast_succ]
    ring

/-- A positive ACTUAL Euler shift is injective modulo an Euler-stable ideal
with a nilpotent coordinate. The proof raises the genuine finite t-adic order. -/
theorem euler_positive_recovery (δ : Derivation ℂ R R) {t : R} (ht : δ t=1)
    (B : Ideal R) (hEuler : ∀g∈B,t*δ g∈B) {D : ℕ} (hTD : t^D∈B)
    (r : ℕ) (hr : 0<r) (f : R) (hGiven : t*δ f+(r : R)*f∈B) : f∈B:=by
  have hAll : ∀k,∃g,f-t^k*g∈B:=by
    intro k
    induction k with
    | zero=>exact ⟨f,by simp⟩
    | succ k ih=>
      obtain ⟨g,hfg⟩:=ih
      let m:=k+r
      have hm : 0<m:=by dsimp only [m];omega
      have hmC : (m : ℂ)≠0:=by exact_mod_cast (Nat.ne_of_gt hm)
      let s:=algebraMap ℂ R ((m : ℂ)⁻¹)
      have hScalar : s*(m : R)=1:=by
        have hMap:=congrArg (algebraMap ℂ R) (inv_mul_cancel₀ hmC)
        simpa only [s,map_mul,map_natCast,map_one] using hMap
      have hE:=hEuler (f-t^k*g) hfg
      have hR:=B.mul_mem_left (r : R) hfg
      have hSub:=B.sub_mem (B.sub_mem hGiven hE) hR
      have hStep : (m : R)*(t^k*g)+t^(k+1)*δ g∈B:=by
        have hEq : (m : R)*(t^k*g)+t^(k+1)*δ g=
            (t*δ f+(r : R)*f)-t*δ (f-t^k*g)-(r : R)*(f-t^k*g):=by
          rw [δ.map_sub,mul_sub,euler_coordinate_power δ ht k g]
          dsimp only [m]
          push_cast
          ring
        rw [hEq]
        exact hSub
      refine ⟨-s*δ g,?_⟩
      have hSum:=B.add_mem hfg (B.mul_mem_left s hStep)
      have hEq : f-t^(k+1)*(-s*δ g)=
          (f-t^k*g)+s*((m : R)*(t^k*g)+t^(k+1)*δ g):=by
        rw [mul_add,←mul_assoc s (m : R),hScalar]
        ring
      rw [hEq]
      exact hSum
  obtain ⟨g,hfg⟩:=hAll D
  have hSum:=B.add_mem hfg (B.mul_mem_right g hTD)
  convert hSum using 1
  ring

/-- Recover the ACTUAL original member from a finite derivative of its
contact-coordinate power. No desired colon inclusion is a premise. -/
theorem euler_contact_power_recovery (δ : Derivation ℂ R R) {t : R} (ht : δ t=1)
    (B : Ideal R) (hEuler : ∀g∈B,t*δ g∈B) {D : ℕ} (hTD : t^D∈B) :
    ∀j f,iteratedDerivation δ j (t^j*f)∈B → f∈B
  | 0,f,h=>by simpa [iteratedDerivation] using h
  | j+1,f,h=>by
    have hPow : t^(j+1)*f=t*(t^j*f):=by ring
    rw [hPow,iteratedDerivation_coordinate_mul δ ht j (t^j*f)] at h
    have hDown:=euler_positive_recovery δ ht B hEuler hTD (j+1) (by omega)
      (iteratedDerivation δ j (t^j*f)) h
    exact euler_contact_power_recovery δ ht B hEuler hTD j f hDown

end Algebra

end
end Hironaka.HironakaActualEulerContactPowerRecovery
