/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Indicator sequence for 5 Fibonacci numbers with n digits

$a(n) = 1$ if exactly 5 Fibonacci numbers exist with exactly $n$ digits, otherwise $0$.
For the partial sums $S(n) = \sum_{k=1}^n a(k)$, it is conjectured that
$\beta-2 < S(n)-\alpha n < \beta-1$, where $\alpha = \log(10)/\log(\phi) - 4$
and $\beta = \log(5)/(2\log(\phi)) - 1$.

*References:*
- [A105565](https://oeis.org/A105565)
-/

namespace OeisA105565

open Nat Finset Real
open scoped goldenRatio

/--
The primary defining sequence `a`.
$a(n) = 1$ if exactly 5 Fibonacci numbers exist with exactly $n$ digits, otherwise $0$.
That is, $a(n) = 1$ if the number of indices $k \in \mathbb{N}$ such that
$10^{n-1} \le \mathrm{fib}(k) < 10^n$ is 5.
-/
def a (n : ℕ) : ℕ :=
  if n > 0 then
    -- $n$ is the number of digits, so $n \ge 1$.
    let lowerBound : ℕ := 10 ^ (n - 1)
    let upperBound : ℕ := 10 ^ n

    -- A safe upper bound for the index $k$.
    let maxK : ℕ := 5 * n + 10

    -- Count indices $k$ in range $[0, maxK)$ such that $\mathrm{fib}(k)$ has $n$ digits.
    let count : ℕ :=
      (filter (fun k => lowerBound ≤ Nat.fib k ∧ Nat.fib k < upperBound) (range maxK)).card

    if count = 5 then 1 else 0
  else
    0

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

/-- The golden ratio $\phi = (1 + \sqrt{5})/2$. -/
noncomputable def phi : Real := goldenRatio

/-- The constant $\alpha = \log(10)/\log(\phi) - 4$. -/
noncomputable def alphaConst : Real := Real.log 10 / Real.log phi - 4

/-- The constant $\beta = \log(5)/(2\log(\phi)) - 1$. -/
noncomputable def betaConst : Real := Real.log 5 / (2 * Real.log phi) - 1

/-- The partial sum $S(n) = \sum_{k=1}^n a(k)$. -/
noncomputable def s (n : ℕ) : Real :=
  (Finset.Icc 1 n).sum (fun k => (a k : Real))

private noncomputable def boundary (n : ℕ) : ℝ :=
  Real.logb phi (((10 : ℝ) ^ n) * √5)

@[category API, AMS 11]
private lemma phi_eq_goldenRatio : phi = Real.goldenRatio := rfl

@[category API, AMS 11]
private lemma phi_pos : 0 < phi := by
  rw [phi_eq_goldenRatio]
  exact Real.goldenRatio_pos

@[category API, AMS 11]
private lemma one_lt_phi : 1 < phi := by
  rw [phi_eq_goldenRatio]
  exact Real.one_lt_goldenRatio

@[category API, AMS 11]
private lemma log_phi_pos : 0 < Real.log phi := by
  rw [phi_eq_goldenRatio]
  exact Real.log_pos Real.one_lt_goldenRatio

@[category API, AMS 11]
private lemma phi_pow_four_lt_ten : phi ^ 4 < (10 : ℝ) := by
  rw [phi_eq_goldenRatio]
  calc
    Real.goldenRatio ^ 4 = (Real.goldenRatio ^ 2) ^ 2 := by ring
    _ = (Real.goldenRatio + 1) ^ 2 := by rw [Real.goldenRatio_sq]
    _ < 10 := by nlinarith [Real.one_lt_goldenRatio, Real.goldenRatio_lt_two]

@[category API, AMS 11]
private lemma ten_lt_phi_pow_five : (10 : ℝ) < phi ^ 5 := by
  rw [phi_eq_goldenRatio]
  have hphi : (8 / 5 : ℝ) < Real.goldenRatio := by
    rw [Real.goldenRatio]
    have hs : (11 / 5 : ℝ) < √5 := by
      rw [lt_sqrt (by norm_num)]
      norm_num
    linarith
  calc
    (10 : ℝ) < (8 / 5 : ℝ) ^ 5 := by norm_num
    _ < Real.goldenRatio ^ 5 :=
      pow_lt_pow_left₀ hphi (by norm_num) (by norm_num)

@[category API, AMS 11]
private lemma alphaConst_pos : 0 < alphaConst := by
  rw [alphaConst]
  rw [sub_pos]
  rw [lt_div_iff₀ log_phi_pos]
  have h := Real.log_lt_log (pow_pos phi_pos 4) phi_pow_four_lt_ten
  rw [Real.log_pow] at h
  norm_num at h ⊢
  exact h

@[category API, AMS 11]
private lemma alphaConst_lt_one : alphaConst < 1 := by
  rw [alphaConst]
  rw [sub_lt_iff_lt_add]
  norm_num
  rw [div_lt_iff₀ log_phi_pos]
  have h := Real.log_lt_log (by norm_num) ten_lt_phi_pow_five
  rw [Real.log_pow] at h
  norm_num at h ⊢
  exact h

@[category API, AMS 11]
private lemma boundary_eq (n : ℕ) :
    boundary n = (n : ℝ) * Real.log 10 / Real.log phi +
      Real.log 5 / (2 * Real.log phi) := by
  rw [boundary, Real.logb, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_sqrt (by norm_num)]
  ring

@[category API, AMS 11]
private lemma boundary_eq_affine (n : ℕ) :
    boundary n = 4 * (n : ℝ) + 1 + ((n : ℝ) * alphaConst + betaConst) := by
  rw [boundary_eq, alphaConst, betaConst]
  ring

@[category API, AMS 11]
private lemma phi_pow_six_lt_ten_mul_sqrt_five : phi ^ 6 < (10 : ℝ) * √5 := by
  have hphi : phi < (13 / 8 : ℝ) := by
    rw [phi_eq_goldenRatio, Real.goldenRatio]
    have hs : √5 < (9 / 4 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    linarith
  have hs : (2 : ℝ) < √5 := by
    rw [lt_sqrt (by norm_num)]
    norm_num
  calc
    phi ^ 6 < (13 / 8 : ℝ) ^ 6 :=
      pow_lt_pow_left₀ hphi phi_pos.le (by norm_num)
    _ < 20 := by norm_num
    _ < 10 * √5 := by nlinarith

@[category API, AMS 11]
private lemma ten_mul_sqrt_five_lt_phi_pow_seven : (10 : ℝ) * √5 < phi ^ 7 := by
  have hphi : (8 / 5 : ℝ) < phi := by
    rw [phi_eq_goldenRatio, Real.goldenRatio]
    have hs : (11 / 5 : ℝ) < √5 := by
      rw [lt_sqrt (by norm_num)]
      norm_num
    linarith
  have hs : √5 < (9 / 4 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  calc
    (10 : ℝ) * √5 < 45 / 2 := by nlinarith
    _ < (8 / 5 : ℝ) ^ 7 := by norm_num
    _ < phi ^ 7 := pow_lt_pow_left₀ hphi (by norm_num) (by norm_num)

@[category API, AMS 11]
private lemma boundary_one_bounds : 6 < boundary 1 ∧ boundary 1 < 7 := by
  constructor
  · rw [boundary, Real.lt_logb_iff_rpow_lt one_lt_phi (by positivity)]
    norm_num [Real.rpow_natCast]
    exact phi_pow_six_lt_ten_mul_sqrt_five
  · rw [boundary, Real.logb_lt_iff_lt_rpow one_lt_phi (by positivity)]
    norm_num [Real.rpow_natCast]
    exact ten_mul_sqrt_five_lt_phi_pow_seven

@[category API, AMS 11]
private lemma alpha_add_beta_bounds :
    1 < alphaConst + betaConst ∧ alphaConst + betaConst < 2 := by
  have h := boundary_one_bounds
  rw [boundary_eq_affine] at h
  norm_num at h
  constructor <;> linarith

@[category API, AMS 11]
private lemma fib_approx_error (k : ℕ) :
    |(Nat.fib k : ℝ) - phi ^ k / √5| < 1 / 2 := by
  have hspos : (0 : ℝ) < √5 := Real.sqrt_pos.2 (by norm_num)
  have hconj : |Real.goldenConj| < (1 : ℝ) := by
    rw [abs_lt]
    exact ⟨Real.neg_one_lt_goldenConj, Real.goldenConj_neg.trans zero_lt_one⟩
  calc
    |(Nat.fib k : ℝ) - phi ^ k / √5| = |Real.goldenConj| ^ k / √5 := by
      rw [phi_eq_goldenRatio, Real.coe_fib_eq]
      have hinner :
          (Real.goldenRatio ^ k - Real.goldenConj ^ k) / √5 -
              Real.goldenRatio ^ k / √5 = -Real.goldenConj ^ k / √5 := by
        ring
      rw [hinner, abs_div, abs_neg, abs_pow, abs_of_pos hspos]
    _ ≤ 1 / √5 := by
      gcongr
      exact pow_le_one₀ (abs_nonneg _) hconj.le
    _ < 1 / 2 := by
      rw [div_lt_div_iff₀ hspos (by norm_num)]
      have hs : (2 : ℝ) < √5 := by
        rw [lt_sqrt (by norm_num)]
        norm_num
      nlinarith

@[category API, AMS 11]
private lemma sqrt_five_eq_two_mul_phi_sub_one : √5 = 2 * phi - 1 := by
  rw [phi_eq_goldenRatio, Real.goldenRatio]
  ring

@[category API, AMS 11]
private lemma boundary_pos {n : ℕ} (hn : 1 ≤ n) : 0 < boundary n := by
  rw [boundary]
  apply Real.logb_pos one_lt_phi
  have hp : (1 : ℝ) < 10 ^ n := one_lt_pow₀ (by norm_num) (by omega)
  have hs : (1 : ℝ) < √5 := by
    rw [lt_sqrt (by norm_num)]
    norm_num
  nlinarith [mul_pos (show (0 : ℝ) < 10 ^ n by positivity)
    (show (0 : ℝ) < √5 by positivity)]

@[category API, AMS 11]
private lemma boundary_ne_natCast {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    boundary n ≠ (k : ℝ) := by
  intro hk
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := by
      rw [← hk]
      exact boundary_pos hn
    exact_mod_cast this
  have htargetpos : (0 : ℝ) < (10 : ℝ) ^ n * √5 := by positivity
  have hpow : phi ^ k = (10 : ℝ) ^ n * √5 := by
    calc
      phi ^ k = phi ^ (k : ℝ) := (Real.rpow_natCast phi k).symm
      _ = phi ^ boundary n := by rw [hk]
      _ = (10 : ℝ) ^ n * √5 := by
        rw [boundary]
        exact Real.rpow_logb phi_pos one_lt_phi.ne' htargetpos
  have hgold :
      phi * (Nat.fib k : ℝ) + (Nat.fib (k - 1) : ℝ) = phi ^ k := by
    have h := Real.goldenRatio_mul_fib_succ_add_fib (k - 1)
    rw [← phi_eq_goldenRatio] at h
    simpa [Nat.sub_add_cancel hkpos] using h
  have hlinear :
      ((2 : ℝ) * 10 ^ n - Nat.fib k) * phi =
        10 ^ n + Nat.fib (k - 1) := by
    rw [hpow, sqrt_five_eq_two_mul_phi_sub_one] at hgold
    nlinarith
  let den : ℤ := 2 * (10 : ℤ) ^ n - Nat.fib k
  let num : ℤ := (10 : ℤ) ^ n + Nat.fib (k - 1)
  have hden : den ≠ 0 := by
    intro hd
    have hdR : ((den : ℤ) : ℝ) = 0 := by rw [hd]; norm_num
    simp only [den, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_pow,
      Int.cast_natCast] at hdR
    have hnumpos : (0 : ℝ) < 10 ^ n + Nat.fib (k - 1) := by positivity
    rw [hdR, zero_mul] at hlinear
    nlinarith
  have hrat : phi = (num : ℝ) / (den : ℝ) := by
    rw [eq_div_iff (by exact_mod_cast hden)]
    calc
      phi * (den : ℝ) = (den : ℝ) * phi := by ring
      _ = 10 ^ n + Nat.fib (k - 1) := by
        simpa only [den, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_pow,
          Int.cast_natCast] using hlinear
      _ = (num : ℝ) := by
        simp only [num, Int.cast_add, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]
  rw [phi_eq_goldenRatio] at hrat
  exact Real.goldenRatio_irrational.ne_rational num den hrat

@[category API, AMS 11]
private lemma three_dvd_of_two_dvd_fib {k : ℕ} (h : 2 ∣ Nat.fib k) : 3 ∣ k := by
  have hg : Nat.gcd (Nat.fib 3) (Nat.fib k) = 2 := by
    norm_num
    exact Nat.gcd_eq_left_iff_dvd.mpr h
  have hf : Nat.fib (Nat.gcd 3 k) = 2 := by
    rw [Nat.fib_gcd]
    exact hg
  have hle : Nat.gcd 3 k ≤ 3 := Nat.gcd_le_left k (by norm_num)
  have heq : Nat.gcd 3 k = 3 := by
    have hne0 : Nat.gcd 3 k ≠ 0 := by intro hzero; simp [hzero] at hf
    have hne1 : Nat.gcd 3 k ≠ 1 := by intro hone; simp [hone] at hf
    have hne2 : Nat.gcd 3 k ≠ 2 := by intro htwo; simp [htwo] at hf
    omega
  exact Nat.gcd_eq_left_iff_dvd.mp heq

@[category API, AMS 11]
private lemma five_dvd_of_five_dvd_fib {k : ℕ} (h : 5 ∣ Nat.fib k) : 5 ∣ k := by
  have hg : Nat.gcd (Nat.fib 5) (Nat.fib k) = 5 := by
    norm_num
    exact Nat.gcd_eq_left_iff_dvd.mpr h
  have hf : Nat.fib (Nat.gcd 5 k) = 5 := by
    rw [Nat.fib_gcd]
    exact hg
  have hle : Nat.gcd 5 k ≤ 5 := Nat.gcd_le_left k (by norm_num)
  have heq : Nat.gcd 5 k = 5 := by
    have hne0 : Nat.gcd 5 k ≠ 0 := by intro hzero; simp [hzero] at hf
    have hne1 : Nat.gcd 5 k ≠ 1 := by intro hone; simp [hone] at hf
    have hne2 : Nat.gcd 5 k ≠ 2 := by intro htwo; simp [htwo] at hf
    have hne3 : Nat.gcd 5 k ≠ 3 := by intro hthree; norm_num [hthree] at hf
    have hne4 : Nat.gcd 5 k ≠ 4 := by intro hfour; norm_num [hfour] at hf
    omega
  exact Nat.gcd_eq_left_iff_dvd.mp heq

@[category API, AMS 11]
private lemma fib_ne_ten_pow {n k : ℕ} (hn : 1 ≤ n) : Nat.fib k ≠ 10 ^ n := by
  intro hpow
  have hten : 10 ∣ 10 ^ n := dvd_pow_self 10 (by omega)
  have h2fib : 2 ∣ Nat.fib k := hpow ▸ dvd_trans (by norm_num) hten
  have h5fib : 5 ∣ Nat.fib k := hpow ▸ dvd_trans (by norm_num) hten
  have h15 : 15 ∣ k := by
    exact (by norm_num : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd
      (three_dvd_of_two_dvd_fib h2fib) (five_dvd_of_five_dvd_fib h5fib)
  have h610 : 610 ∣ Nat.fib k := by
    have h := Nat.fib_dvd 15 k h15
    norm_num at h
    exact h
  have h61fib : 61 ∣ Nat.fib k := dvd_trans (by norm_num) h610
  have h61pow : 61 ∣ 10 ^ n := hpow ▸ h61fib
  have h61ten : 61 ∣ 10 := (by norm_num : Nat.Prime 61).dvd_of_dvd_pow h61pow
  norm_num at h61ten

@[category API, AMS 11]
private lemma approx_lt_ten_pow_iff {n : ℕ} (_hn : 1 ≤ n) (k : ℕ) :
    phi ^ k / √5 < (10 : ℝ) ^ n ↔ (k : ℝ) < boundary n := by
  rw [boundary, Real.lt_logb_iff_rpow_lt one_lt_phi (by positivity),
    Real.rpow_natCast, div_lt_iff₀ (by positivity)]

@[category API, AMS 11]
private lemma ten_pow_lt_approx_iff {n : ℕ} (_hn : 1 ≤ n) (k : ℕ) :
    (10 : ℝ) ^ n < phi ^ k / √5 ↔ boundary n < (k : ℝ) := by
  rw [boundary, Real.logb_lt_iff_lt_rpow one_lt_phi (by positivity),
    Real.rpow_natCast, lt_div_iff₀ (by positivity)]

@[category API, AMS 11]
private lemma fib_lt_ten_pow_iff {n k : ℕ} (hn : 1 ≤ n) :
    Nat.fib k < 10 ^ n ↔ (k : ℝ) < boundary n := by
  constructor
  · intro h
    by_contra hnot
    have hge : boundary n ≤ (k : ℝ) := le_of_not_gt hnot
    have hgt : boundary n < (k : ℝ) :=
      hge.lt_of_ne (fun heq ↦ boundary_ne_natCast hn k heq)
    have happ : (10 : ℝ) ^ n < phi ^ k / √5 :=
      (ten_pow_lt_approx_iff hn k).2 hgt
    have herr := (abs_lt.mp (fib_approx_error k)).1
    have hsucc : Nat.fib k + 1 ≤ 10 ^ n := Nat.add_one_le_iff.mpr h
    have hsuccR : (Nat.fib k : ℝ) + 1 ≤ (10 : ℝ) ^ n := by
      exact_mod_cast hsucc
    nlinarith
  · intro h
    have happ : phi ^ k / √5 < (10 : ℝ) ^ n :=
      (approx_lt_ten_pow_iff hn k).2 h
    have herr := (abs_lt.mp (fib_approx_error k)).2
    have hleR : (Nat.fib k : ℝ) < (10 : ℝ) ^ n + 1 := by nlinarith
    have hle' : Nat.fib k < 10 ^ n + 1 := by exact_mod_cast hleR
    have hle : Nat.fib k ≤ 10 ^ n := by omega
    exact hle.lt_of_ne (fib_ne_ten_pow hn)

private noncomputable def cutoff (n : ℕ) : ℕ := ⌊boundary n⌋₊

private noncomputable def beat (n : ℕ) : ℕ :=
  ⌊(n : ℝ) * alphaConst + betaConst⌋₊

@[category API, AMS 11]
private lemma index_le_cutoff_iff {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    k ≤ cutoff n ↔ (k : ℝ) < boundary n := by
  have hbpos := boundary_pos hn
  have hfloorlt : (cutoff n : ℝ) < boundary n := by
    have hle : (cutoff n : ℝ) ≤ boundary n := Nat.floor_le hbpos.le
    exact hle.lt_of_ne fun heq ↦ boundary_ne_natCast hn (cutoff n) heq.symm
  constructor
  · intro h
    exact (Nat.cast_le.2 h).trans_lt hfloorlt
  · intro h
    exact (Nat.le_floor_iff hbpos.le).2 h.le

@[category API, AMS 11]
private lemma fib_lt_ten_pow_iff_cutoff {n k : ℕ} (hn : 1 ≤ n) :
    Nat.fib k < 10 ^ n ↔ k ≤ cutoff n := by
  rw [fib_lt_ten_pow_iff hn, index_le_cutoff_iff hn]

@[category API, AMS 11]
private lemma beat_pos_arg {n : ℕ} (hn : 1 ≤ n) :
    0 < (n : ℝ) * alphaConst + betaConst := by
  have hab := alpha_add_beta_bounds.1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [mul_le_mul_of_nonneg_right hnR alphaConst_pos.le]

@[category API, AMS 11]
private lemma cutoff_eq (n : ℕ) (hn : 1 ≤ n) :
    cutoff n = 4 * n + 1 + beat n := by
  rw [cutoff, beat, boundary_eq_affine]
  have hq := (beat_pos_arg hn).le
  have heq :
      4 * (n : ℝ) + 1 + ((n : ℝ) * alphaConst + betaConst) =
        ((n : ℝ) * alphaConst + betaConst) + (4 * n + 1 : ℕ) := by
    norm_num
    ring
  rw [heq, Nat.floor_add_natCast hq]
  omega

@[category API, AMS 11]
private lemma beat_arg_lt (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * alphaConst + betaConst < ((n + 2 : ℕ) : ℝ) := by
  have ha := alphaConst_lt_one
  have hab := alpha_add_beta_bounds.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmul := mul_lt_mul_of_pos_left ha hnR
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  nlinarith [alphaConst_pos]

@[category API, AMS 11]
private lemma cutoff_lt_maxK (n : ℕ) (hn : 1 ≤ n) : cutoff n < 5 * n + 10 := by
  rw [cutoff_eq n hn]
  have hargpos := (beat_pos_arg hn).le
  have hbeat : beat n < n + 2 := by
    rw [beat]
    exact (Nat.floor_lt hargpos).2 (beat_arg_lt n hn)
  omega

@[category API, AMS 11]
private lemma digit_filter_eq_Ioc {n : ℕ} (hn : 2 ≤ n) :
    filter
        (fun k ↦ 10 ^ (n - 1) ≤ Nat.fib k ∧ Nat.fib k < 10 ^ n)
        (range (5 * n + 10)) =
      Ioc (cutoff (n - 1)) (cutoff n) := by
  have hn1 : 1 ≤ n := by omega
  have hpred : 1 ≤ n - 1 := by omega
  ext k
  simp only [mem_filter, mem_range, mem_Ioc]
  rw [← not_lt, fib_lt_ten_pow_iff_cutoff hpred,
    fib_lt_ten_pow_iff_cutoff hn1, not_le]
  constructor
  · rintro ⟨_, hlow, hupp⟩
    exact ⟨hlow, hupp⟩
  · rintro ⟨hlow, hupp⟩
    exact ⟨lt_of_le_of_lt hupp (cutoff_lt_maxK n hn1), hlow, hupp⟩

@[category API, AMS 11]
private lemma digit_count_eq {n : ℕ} (hn : 2 ≤ n) :
    (filter
        (fun k ↦ 10 ^ (n - 1) ≤ Nat.fib k ∧ Nat.fib k < 10 ^ n)
        (range (5 * n + 10))).card =
      cutoff n - cutoff (n - 1) := by
  rw [digit_filter_eq_Ioc hn, Nat.card_Ioc]

@[category API, AMS 11]
private lemma beat_mono_step {n : ℕ} (hn : 2 ≤ n) : beat (n - 1) ≤ beat n := by
  apply Nat.floor_mono
  have hncast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm
  rw [hncast]
  nlinarith [alphaConst_pos]

@[category API, AMS 11]
private lemma beat_step_le {n : ℕ} (hn : 2 ≤ n) : beat n ≤ beat (n - 1) + 1 := by
  have hn1 : 1 ≤ n := by omega
  have hpred : 1 ≤ n - 1 := by omega
  have hqprev :
      (n - 1 : ℕ) * alphaConst + betaConst < (beat (n - 1) : ℝ) + 1 := by
    simpa [beat] using
      (Nat.lt_floor_add_one ((n - 1 : ℕ) * alphaConst + betaConst))
  have hq :
      (n : ℝ) * alphaConst + betaConst < (beat (n - 1) : ℝ) + 2 := by
    have hncast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm
    rw [hncast]
    nlinarith [alphaConst_lt_one]
  have hfloor : beat n < beat (n - 1) + 2 := by
    rw [beat]
    apply (Nat.floor_lt (beat_pos_arg hn1).le).2
    exact_mod_cast hq
  omega

@[category API, AMS 11]
private lemma digit_count_formula {n : ℕ} (hn : 2 ≤ n) :
    (filter
        (fun k ↦ 10 ^ (n - 1) ≤ Nat.fib k ∧ Nat.fib k < 10 ^ n)
        (range (5 * n + 10))).card =
      4 + (beat n - beat (n - 1)) := by
  rw [digit_count_eq hn, cutoff_eq n (by omega), cutoff_eq (n - 1) (by omega)]
  have hmono := beat_mono_step hn
  omega

@[category API, AMS 11]
private lemma a_eq_beat_sub {n : ℕ} (hn : 2 ≤ n) :
    a n = beat n - beat (n - 1) := by
  rw [a, if_pos (by omega)]
  dsimp only
  rw [digit_count_formula hn]
  have hmono := beat_mono_step hn
  have hstep := beat_step_le hn
  by_cases h : beat n - beat (n - 1) = 1
  · simp [h]
  · have hz : beat n - beat (n - 1) = 0 := by omega
    simp [hz]

@[category API, AMS 11]
private lemma beat_one : beat 1 = 1 := by
  rw [beat]
  norm_num only [Nat.cast_one, one_mul]
  apply (Nat.floor_eq_iff (by linarith [alpha_add_beta_bounds.1])).2
  constructor
  · norm_num
    exact alpha_add_beta_bounds.1.le
  · norm_num
    exact alpha_add_beta_bounds.2

@[category API, AMS 11]
private lemma s_eq_beat_sub_one {n : ℕ} (hn : 1 ≤ n) :
    s n = (beat n : ℝ) - 1 := by
  induction n using Nat.case_strong_induction_on with
  | hz => omega
  | hi n ih =>
      by_cases hn0 : n = 0
      · subst n
        rw [s, beat_one]
        norm_num [a_1]
      · have hnpos : 1 ≤ n := by omega
        have hrec := ih n (by omega) hnpos
        rw [s] at hrec ⊢
        have hset : insert (n + 1) (Icc 1 n) = Icc 1 (n + 1) :=
          Finset.insert_Icc_right_eq_Icc_succ (by omega : (1 : ℕ) ≤ n + 1)
        rw [← hset, sum_insert (by simp)]
        rw [hrec, a_eq_beat_sub (n := n + 1) (by omega)]
        have hmono := beat_mono_step (n := n + 1) (by omega)
        have hmono' : beat n ≤ beat (n + 1) := by simpa using hmono
        have hidx : n + 1 - 1 = n := by omega
        rw [hidx]
        rw [Nat.cast_sub hmono']
        ring

@[category API, AMS 11]
private lemma beat_cast_lt_arg {n : ℕ} (hn : 1 ≤ n) :
    (beat n : ℝ) < (n : ℝ) * alphaConst + betaConst := by
  have hqpos := beat_pos_arg hn
  have hle : (beat n : ℝ) ≤ (n : ℝ) * alphaConst + betaConst :=
    Nat.floor_le hqpos.le
  apply hle.lt_of_ne
  intro heq
  apply boundary_ne_natCast hn (4 * n + 1 + beat n)
  rw [boundary_eq_affine, ← heq]
  norm_num

@[category API, AMS 11]
private lemma beat_arg_lt_cast_add_one {n : ℕ} :
    (n : ℝ) * alphaConst + betaConst < (beat n : ℝ) + 1 := by
  simpa [beat] using Nat.lt_floor_add_one ((n : ℝ) * alphaConst + betaConst)

/--
Conjecture: $\beta-2 < S(n)-\alpha n < \beta-1$.
The constants $\alpha$ and $\beta$ are as defined in the formula section.

Solved by OpenAI Codex, prompted by Adam Haig. The proof was developed and kernel-checked in
Lean 4 on August 15, 2026.
-/
@[category research solved, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 ≤ n) :
    betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1 := by
  rw [s_eq_beat_sub_one hn]
  have hlow := beat_arg_lt_cast_add_one (n := n)
  have hupp := beat_cast_lt_arg hn
  constructor <;> nlinarith

end OeisA105565
