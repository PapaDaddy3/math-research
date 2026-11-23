/-
Claim: demo:tan-ninety-degrees
Source: https://github.com/PapaDaddy3/math-research/tree/wphp-dev#tan90
Scope: Demonstration only. In Mathlib, x / 0 = 0, so Real.tan (π/2) = sin(π/2)/cos(π/2) = 1/0 = 0 is a kernel-checked theorem, although tan 90° is undefined in ordinary mathematics; also tan is unbounded near π/2.
Declarations: MathResearch.tan_ninety_is_zero_in_lean MathResearch.tan_unbounded_near_ninety
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace MathResearch
open Real

/-- 「tan 90° = 0」 — Lean/Mathlib의 0으로 나누기 규약(x/0 = 0) 때문에 참인 정리 -/
theorem tan_ninety_is_zero_in_lean : Real.tan (π / 2) = 0 := by
  rw [Real.tan_eq_sin_div_cos, Real.cos_pi_div_two, div_zero]

/-- 그런데 90° 바로 앞에서는 tan이 어떤 수보다도 커진다(발산) -/
theorem tan_unbounded_near_ninety (M : ℝ) : ∃ x : ℝ, 0 < x ∧ x < π / 2 ∧ M < Real.tan x := by
  refine ⟨Real.arctan (|M| + 1), ?_, Real.arctan_lt_pi_div_two _, ?_⟩
  · exact Real.arctan_pos.mpr (by positivity)
  · rw [Real.tan_arctan]; linarith [le_abs_self M]

end MathResearch
