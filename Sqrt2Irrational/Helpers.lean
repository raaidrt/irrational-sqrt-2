import Mathlib

open Real
open Classical
open Int

theorem exists_reduced_rational_for_rational (a b : ℤ) (hb_non_zero : b ≠ 0)
  : ∃a' b' : ℤ, IsCoprime a' b' ∧ ((a : ℚ) / b = a' / b') ∧ b' ≠ 0 := by
  let d : ℕ := a.gcd b
  use a / d
  use b / d
  have h₁: Int.cast (a / d) = (a : ℚ) / (d : ℚ) := by
    refine Int.cast_div ?_ ?_
    · apply Int.gcd_dvd_left a b
    · norm_cast
      push_neg
      exact gcd_ne_zero_right hb_non_zero
  have h₂: Int.cast (b / d) = (b : ℚ) / (d : ℚ) := by
    refine Int.cast_div ?_ ?_
    · apply Int.gcd_dvd_right a b
    · norm_cast
      push_neg
      exact gcd_ne_zero_right hb_non_zero
  have gcd_pos : 0 < d := by
    apply Int.gcd_pos_of_ne_zero_right a hb_non_zero
  constructor
  · exact isCoprime_div_gcd_div_gcd (hb_non_zero)
  · constructor
    · show (a : ℚ) / b = ↑(a / ↑d) / ↑(b / ↑d)
      calc
        (a : ℚ) / (b : ℚ) = ((a : ℚ) / (d : ℚ)) * ((d : ℚ) / (b : ℚ)) := by field_simp
                  _ = ((a : ℚ) / d) / (b / d) := by field_simp
                  _ = ↑(a / ↑d) / ↑(b / ↑d) := by simp [h₁, h₂]
    · exact ediv_gcd_ne_zero_if_ne_zero_right a hb_non_zero

theorem not_two_dvd_implies_odd (a : ℕ) (ha_odd : ¬2 ∣ a) : Odd a := by
  rcases Int.even_or_odd a with h | h
  · -- Case: a is even
    -- If a is even, then 2 ∣ a, which contradicts ha_odd
    apply absurd (even_iff_two_dvd.mp h)
    norm_cast
  · -- Case: a is odd
    -- We already have what we want
    exact_mod_cast h

/-- lemma prime_two' : Prime 2 := by
  constructor
  · -- Prove 2 ≠ 1
    norm_num
  · constructor
    · norm_num -- 2 is non-unit
    · -- Prove that for all a b, if a * b = 2, then a = 1 or b = 1
      intro a b hab_dvd_prod
      apply byContradiction
      intro h_contra
      push_neg at h_contra
      obtain ⟨ha_odd, hb_odd⟩ := h_contra
      have ha_odd : Odd a := by apply not_two_dvd_implies_odd a ha_odd
      have hb_odd : Odd b := by apply not_two_dvd_implies_odd b hb_odd
      obtain ha_mul_b_odd := Nat.odd_mul.mpr ⟨ha_odd, hb_odd⟩
      obtain ha_mul_b_even := even_iff_two_dvd.mpr hab_dvd_prod
      have ha_mul_b_not_odd : ¬Odd (a * b) := Nat.not_odd_iff_even.mpr ha_mul_b_even
      exact ha_mul_b_not_odd ha_mul_b_odd -/

theorem prime_pow_dvd (b : ℤ) (h : (2 : ℤ) ∣ b ^ 2) : (2 : ℤ) ∣ b := by
  rw [sq] at h
  -- b^2 = b * b, so 2 | b * b
  -- Since 2 is prime, 2 | b or 2 | b
  have := Int.prime_two.dvd_mul.mp h
  cases this <;> assumption

lemma transform_sq_eq_rational (a b : ℤ) (hb : b ≠ 0) (h : √2 = a / b) : 2 * b^2 = a^2 := by
  -- Square both sides of the equation
  have h_sq : (√2)^2 = (a / b)^2 := by rw [h]
  -- Simplify left side using sqrt_sq
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h_sq
  -- Simplify right side using div_pow
  rw [div_pow] at h_sq
  -- Now we have 2 = a^2 / b^2
  -- Multiply both sides by b^2
  have : 2 * b^2 = a^2 := by
    field_simp at h_sq
    norm_cast
    rify [h_sq]
  exact this

lemma not_coprime_if_both_even (a b : ℤ) (ha : Even a) (hb : Even b) : ¬IsCoprime a b := by
  intro h_coprime
  let ha := even_iff_two_dvd.mp ha
  let hb := even_iff_two_dvd.mp hb
  rw [isCoprime_iff_gcd_eq_one] at h_coprime
  have : 2 ∣ Int.gcd a b := Int.dvd_gcd ha hb
  rw [h_coprime] at this
  have : 2 ∣ 1 := this
  norm_num at this
