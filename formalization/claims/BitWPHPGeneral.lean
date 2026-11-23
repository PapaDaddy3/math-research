/-
Claim: cor:bit-WPHP-general-pigeons (Stage 17 extension, not part of the upstream preprint)
Source: https://github.com/PapaDaddy3/math-research/tree/wphp#bit-wphp-general
Scope: Weak bit-PHP with any number m > n = 2^ℓ of pigeons: if x = n²/(8192 ℓ² m) satisfies 2 ln m + 4 ≤ x, every refutation in the finite affine DAG calculus has more than exp(x) nodes. Uses only Theorems 6.9 and 7.8 of the upstream development, which are stated for arbitrary m.
Declarations: MathResearch.bitWPHP_general
-/
import claims.BitPHPExponential

namespace MathResearch
noncomputable section
open PolynomialCalculus

theorem bitWPHP_general : ∀ (ℓ : ℕ), 32 ≤ ℓ → ∀ (m : ℕ), 2^ℓ < m →
    2*Real.log (m:ℝ) + 4 ≤ ((2^ℓ:ℕ):ℝ)^2/(8192*(ℓ:ℝ)^2*(m:ℝ)) → ∀ {S : ℕ}
    (C : Fin S → FiniteParityClause (BitVar m ℓ))
    (_dag : AffineDAG (usualBitPHPInitials m ℓ) C)
    (finish : Fin S), C finish = ∅ →
    Real.exp (((2^ℓ:ℕ):ℝ)^2/(8192*(ℓ:ℝ)^2*(m:ℝ))) < (S:ℝ) := by
  intro ℓ hℓ m hm1 hxroom S C dag finish hempty
  classical
  by_contra hnot
  let n : ℕ := 2^ℓ
  let x : ℝ := ((n:ℕ):ℝ)^2/(8192*(ℓ:ℝ)^2*(m:ℝ))
  have hS : (S:ℝ) ≤ Real.exp x := le_of_not_gt hnot
  have hxr : 2*Real.log (m:ℝ) + 4 ≤ x := hxroom
  have hn1 : 1 ≤ n := Nat.one_le_two_pow
  have hmn : n < m := hm1
  have hm2 : 2 ≤ m := by omega
  have hroom : 32768*((2*ℓ+4)*ℓ^2) ≤ n := bitPHP_exponential_room ℓ hℓ
  have hℓℓ : 32*ℓ ≤ ℓ*ℓ := Nat.mul_le_mul_right _ hℓ
  have h64 : 64*ℓ ≤ n := by nlinarith
  have hℓR : (32:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hℓ
  have hmR : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  -- exp x ≥ 16 m² and exp x ≥ 16
  have he2 : (2:ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1:ℝ)
    linarith
  have he4 : (16:ℝ) ≤ Real.exp 4 := by
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    have : (2:ℝ)^4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he2 4
    norm_num at this ⊢
    linarith
  have hexpm : Real.exp (2*Real.log (m:ℝ) + 4) = (m:ℝ)^2 * Real.exp 4 := by
    rw [Real.exp_add, mul_comm 2 (Real.log _), Real.exp_mul, Real.exp_log hmpos]
    norm_num
  have hbig : 16*(m:ℝ)^2 ≤ Real.exp x := by
    have := Real.exp_le_exp.mpr hxr
    rw [hexpm] at this
    nlinarith [sq_nonneg (m:ℝ)]
  have hbig16 : (16:ℝ) ≤ Real.exp x := by nlinarith
  -- Inventory.
  let M : ℕ := 3*S + m.choose 2
  have hchoose : m.choose 2 ≤ m^2 := by
    have h := Nat.choose_le_pow m 2
    omega
  have hM : 1 ≤ M := by
    have h : 0 < m.choose 2 := Nat.choose_pos (by omega)
    omega
  have hMR : (M:ℝ) ≤ 3*Real.exp x + (m:ℝ)^2 := by
    have hc : ((m.choose 2:ℕ):ℝ) ≤ (m:ℝ)^2 := by exact_mod_cast hchoose
    simp only [M]
    push_cast
    linarith
  have hMpos : (0:ℝ) < 4*(M:ℝ) := by
    have : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    linarith
  have h4M : 4*(M:ℝ) ≤ Real.exp (2*x) := by
    rw [two_mul, Real.exp_add]
    nlinarith
  have hlog : Real.log (4*(M:ℝ)) ≤ 2*x := (Real.log_le_iff_le_exp hMpos).mpr h4M
  -- The kernel degree k = ⌊n/(32ℓ)⌋.
  let k : ℕ := n/(32*ℓ)
  have hqpos : 0 < 32*ℓ := by omega
  have hkmul : k*(32*ℓ) ≤ n := Nat.div_mul_le_self n (32*ℓ)
  have hkpos : 1 ≤ k := Nat.div_pos (by omega) hqpos
  have hkn : k ≤ n := Nat.div_le_self n (32*ℓ)
  have hklt : n < (k+1)*(32*ℓ) := by
    have h1 := Nat.div_add_mod n (32*ℓ)
    have h2 := Nat.mod_lt n hqpos
    have h3 : (32*ℓ)*(n/(32*ℓ)) = k*(32*ℓ) := Nat.mul_comm _ _
    nlinarith
  have hnk : n ≤ 64*ℓ*k := by nlinarith
  have hnkR : (n:ℝ) ≤ 64*(ℓ:ℝ)*(k:ℝ) := by exact_mod_cast hnk
  have hden : (0:ℝ) < 8192*(ℓ:ℝ)^2*(m:ℝ) := by positivity
  have hmx : (m:ℝ)*x = (n:ℝ)^2/(8192*(ℓ:ℝ)^2) := by
    simp only [x]
    field_simp
  have hsq : ((m:ℕ):ℝ)*Real.log (4*(M:ℝ)) ≤ (k:ℝ)^2 := by
    have hstep1 : (m:ℝ)*Real.log (4*(M:ℝ)) ≤ (m:ℝ)*(2*x) :=
      mul_le_mul_of_nonneg_left hlog hmpos.le
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
    have hsqr : (n:ℝ)^2 ≤ (64*(ℓ:ℝ)*(k:ℝ))^2 := pow_le_pow_left₀ hn0 hnkR 2
    have hℓ2 : (0:ℝ) < 8192*(ℓ:ℝ)^2 := by positivity
    have hfin : (m:ℝ)*(2*x) ≤ (k:ℝ)^2 := by
      have e : (m:ℝ)*(2*x) = 2*((n:ℝ)^2/(8192*(ℓ:ℝ)^2)) := by rw [← hmx]; ring
      rw [e, ← mul_div_assoc, div_le_iff₀ hℓ2]
      nlinarith
    exact hstep1.trans hfin
  have hℓk : k ≤ ℓ*k := Nat.le_mul_of_pos_left _ (by omega)
  have hpack : 4*(k-1) < n := by
    have : 32*k ≤ n := by nlinarith
    omega
  have hB : 2*(k*((12*ℓ+1)+1))-1 ≤ n := by
    have : 2*(k*((12*ℓ+1)+1)) ≤ n := by nlinarith
    omega
  -- Transfer and exclusion.
  obtain ⟨N,R,hN,_,_,_,hpc⟩ := usual_bitPHP_PC_transfer C dag finish hempty (3*ℓ) (by omega)
  let g : ∀ b : Fin N, {f // f ∈ R b} → AffineInputMap (BitVar m ℓ) :=
    fun _ i => i.val
  have hcount : Nat.card (ProperHighIndex g k) ≤ M := by
    apply le_trans ((proper_high_count_le_proper_count g k).trans ?_) hN
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (ProperBlockIndex g) ≤ Fintype.card (Fin N) := Fintype.card_subtype_le _
      _ = N := Fintype.card_fin _
  have hdegree : max (2*(3*ℓ)+ℓ) (4*(3*ℓ)+1) = 12*ℓ+1 := by omega
  rw [hdegree,registry_system_eq_ensFamily] at hpc
  exact affine_family_exclusion_of_square m ℓ M k (12*ℓ+1) (by omega) (by omega) hM
    hkpos (by omega) hsq (by omega) hpack hB g hcount hpc

end
end MathResearch
