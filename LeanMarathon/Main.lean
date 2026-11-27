
import Mathlib
import Architect

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:erdos-weight"
  (statement := /-- For a natural number $n$, the Erd\H{o}s weight is
  $\nu_0(n)=(n\log n)^{-1}$, with Lean's real logarithm convention used outside
  the range $n\geq 2$. -/)
  (title := /-- Erd\H{o}s weight -/)
  (latexEnv := "definition")]
noncomputable def erdos_weight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log (n : ℝ))

@[blueprint "def:erdos-sum"
  (statement := /-- For a set $A\subseteq\mathbb{N}$, the Erd\H{o}s sum is
  $f(A)=\sum_{n\in A}\nu_0(n)$, represented as an unconditional sum over
  $\mathbb{N}$ by the indicator of $A$. -/)
  (title := /-- Erd\H{o}s sum -/)
  (latexEnv := "definition")]
noncomputable def erdos_sum (A : Set ℕ) : ℝ :=
  ∑' n : ℕ, A.indicator erdos_weight n

@[blueprint "def:primitive-set"
  (statement := /-- A set $A\subseteq\mathbb{N}$ is primitive if it is an
  antichain for divisibility: whenever $a,b\in A$ are distinct, $a\nmid b$. Since
  the quantification is ordered, this is equivalent to saying that no two
  distinct elements of $A$ divide one another. -/)
  (title := /-- Primitive sets -/)
  (latexEnv := "definition")]
def primitive_set (A : Set ℕ) : Prop :=
  IsAntichain (fun a b : ℕ => a ∣ b) A

@[blueprint "def:supported-above"
  (statement := /-- A set $A\subseteq\mathbb{N}$ is supported above the real
  threshold $x$ if every member $n\in A$ satisfies $x\leq n$. -/)
  (title := /-- Support above a threshold -/)
  (latexEnv := "definition")]
def supported_above (A : Set ℕ) (x : ℝ) : Prop :=
  ∀ n : ℕ, n ∈ A -> x ≤ (n : ℝ)

@[blueprint "def:supported-in-interval"
  (statement := /-- A set $A\subseteq\mathbb{N}$ is supported in the real
  interval $[x,X]$ if every member $n\in A$ satisfies $x\leq n\leq X$. -/)
  (title := /-- Finite interval support -/)
  (latexEnv := "definition")]
def supported_in_interval (A : Set ℕ) (x X : ℝ) : Prop :=
  ∀ n : ℕ, n ∈ A -> x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X

@[blueprint "def:mangoldt-reciprocal-partial-sum"
  (statement := /-- This is the partial reciprocal von Mangoldt sum
  $\sum_{1\leq q\leq t}\Lambda(q)/q$, expressed as an unconditional sum over
  $\mathbb{N}$. -/)
  (title := /-- Reciprocal von Mangoldt partial sum -/)
  (latexEnv := "definition")]
noncomputable def mangoldt_reciprocal_partial_sum (t : ℝ) : ℝ :=
  ∑' q : ℕ,
    if 1 ≤ q ∧ (q : ℝ) ≤ t then ArithmeticFunction.vonMangoldt q / (q : ℝ) else 0

@[blueprint "def:mangoldt-tail-term"
  (statement := /-- For natural numbers $m$ and $q$, this is the summand
  $\Lambda(q)/(q\log^2(mq))$ appearing in the von Mangoldt tail estimates. -/)
  (title := /-- Von Mangoldt tail summand -/)
  (latexEnv := "definition")]
noncomputable def mangoldt_tail_term (m q : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt q /
    ((q : ℝ) * (Real.log (((m * q : ℕ) : ℝ))) ^ 2)

@[blueprint "def:mangoldt-tail-sum"
  (statement := /-- For a natural number $m$ and a real threshold $y$, this is
  the tail $\sum_{q\geq y}\Lambda(q)/(q\log^2(mq))$. -/)
  (title := /-- Von Mangoldt tail sum -/)
  (latexEnv := "definition")]
noncomputable def mangoldt_tail_sum (m : ℕ) (y : ℝ) : ℝ :=
  ∑' q : ℕ, if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0

@[blueprint "def:tail-majorant"
  (statement := /-- For $x\geq 2$, this is the reindexed upper bound
  $\sum_{1\leq n<x} n^{-1}\sum_{q\geq\max(2,x/n)}
  \Lambda(q)/(q\log^2(nq))$ obtained after discarding the upper cutoff in the
  finite proof. -/)
  (title := /-- Reindexed tail majorant -/)
  (latexEnv := "definition")]
noncomputable def tail_majorant (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 1 ≤ n ∧ (n : ℝ) < x then
      (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
    else 0

@[blueprint "def:cut-capacity"
  (statement := /-- For real cut parameters $x\leq X$, this is the finite cut
  capacity
  $\sum_{x\leq r\leq X}(r\log^2 r)^{-1}
  \sum_{q\mid r,\ r/q<x}\Lambda(q)$ arising from the downward von Mangoldt
  chain. -/)
  (title := /-- Finite von Mangoldt cut capacity -/)
  (latexEnv := "definition")]
noncomputable def cut_capacity (x X : ℝ) : ℝ :=
  ∑' r : ℕ,
    if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
      (1 / ((r : ℝ) * (Real.log (r : ℝ)) ^ 2)) *
        (∑ q ∈ r.divisors,
          if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
    else 0

@[blueprint "def:erdos1196-bound"
  (statement := /-- The explicit formal version of the asymptotic conclusion in
  Erd\H{o}s--S\'ark\"ozy--Szemer\'edi problem \#1196 with constant $C$: for every
  real $x\geq 2$ and every primitive set $A\subseteq\mathbb{N}$ supported in
  $[x,\infty)$, one has $f(A)\leq 1+C/\log x$. -/)
  (title := /-- Quantitative infinite-support bound -/)
  (latexEnv := "definition")]
def erdos1196_bound (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ x : ℝ, 2 ≤ x -> ∀ A : Set ℕ,
      primitive_set A -> supported_above A x -> erdos_sum A ≤ 1 + C / Real.log x

@[blueprint "def:erdos1196-finite-bound"
  (statement := /-- The finite-support version of \cref{def:erdos1196-bound}:
  for every real $2\leq x\leq X$ and every primitive set $A\subseteq\mathbb{N}$
  supported in $[x,X]$, one has $f(A)\leq 1+C/\log x$. -/)
  (title := /-- Quantitative finite-support bound -/)
  (latexEnv := "definition")]
def erdos1196_finite_bound (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ x X : ℝ, 2 ≤ x -> x ≤ X -> ∀ A : Set ℕ,
      primitive_set A -> supported_in_interval A x X ->
        erdos_sum A ≤ 1 + C / Real.log x

@[blueprint "lem:von-mangoldt-divisor-sum"
  (statement := /-- For every $n\in\mathbb{N}$, the sum of the von Mangoldt
  function over the finite divisor set $\operatorname{divisors}(n)$ satisfies
  $\sum_{q\in\operatorname{divisors}(n)}\Lambda(q)=\log n$; in particular,
  the case $n=0$ uses the empty finite divisor set convention. -/)
  (proof := /-- Apply the standard divisor-sum identity for the von Mangoldt
  function in Mathlib, which states exactly that the finite sum over
  $\operatorname{divisors}(n)$ is $\log n$ for every $n\in\mathbb{N}$. -/)
  (title := /-- Divisor sum of the von Mangoldt function -/)
  (latexEnv := "lemma")]
lemma von_mangoldt_divisor_sum (n : ℕ) :
    (∑ q ∈ n.divisors, ArithmeticFunction.vonMangoldt q) = Real.log (n : ℝ) := by
  simpa using (ArithmeticFunction.vonMangoldt_sum (n := n))

@[blueprint "lem:mertens-von-mangoldt-reciprocal"
  (statement := /-- There is a real constant $C\geq 0$ such that, for every
  real number $t\geq 1$, the reciprocal von Mangoldt partial sum satisfies
  $|\sum_{1\leq q\leq t}\Lambda(q)/q-\log t|\leq C$. -/)
  (proof := /-- By \cref{def:mangoldt-reciprocal-partial-sum}, the
  unconditional sum is first reduced to the finite sum over
  $1\leq q\leq\lfloor t\rfloor$. For a natural number $n\geq 1$, the
  arithmetic-function convolution identity $\Lambda*\zeta=\log$ gives
  $\sum_{m\leq n}\log m=\sum_{q\leq n}\Lambda(q)\lfloor n/q\rfloor$.
  The inequalities $\lfloor n/q\rfloor\leq n/q$ and
  $n/q-1\leq\lfloor n/q\rfloor$, together with nonnegativity of
  $\Lambda(q)$, compare this weighted divisor sum with
  $n\sum_{q\leq n}\Lambda(q)/q$ up to the Chebyshev sum
  $\sum_{q\leq n}\Lambda(q)$. Mathlib's Chebyshev bound
  $\sum_{q\leq n}\Lambda(q)\leq (\log 4+4)n$, the elementary inequality
  $\log(n!)\leq n\log n$, and the logarithmic Stirling lower bound for
  $\log(n!)$ show that
  $|\sum_{q\leq n}\Lambda(q)/q-\log n|$ is bounded uniformly in
  $n\geq 1$. Finally, for real $t\geq 1$, put
  $n=\lfloor t\rfloor$. Since $n\leq t<n+1\leq 2n$, the difference between
  $\log t$ and $\log n$ is at most $\log 2$, so enlarging the constant gives
  the stated real-variable bound. -/)
  (title := /-- Mertens estimate for reciprocal von Mangoldt sums -/)
  (latexEnv := "lemma")]
lemma mertens_von_mangoldt_reciprocal :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t ->
      |mangoldt_reciprocal_partial_sum t - Real.log t| ≤ C := by
  classical
  let c0 : ℝ := Real.log (2 * Real.pi) / 2
  have htsum : ∀ t : ℝ, 0 ≤ t ->
      mangoldt_reciprocal_partial_sum t =
        ∑ q ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
    intro t ht
    rw [mangoldt_reciprocal_partial_sum]
    calc
      (∑' q : ℕ,
          if 1 ≤ q ∧ (q : ℝ) ≤ t then ArithmeticFunction.vonMangoldt q / (q : ℝ) else 0)
          = ∑ q ∈ Finset.Icc 1 ⌊t⌋₊,
              if 1 ≤ q ∧ (q : ℝ) ≤ t then ArithmeticFunction.vonMangoldt q / (q : ℝ) else 0 := by
            refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
              (s := Finset.Icc 1 ⌊t⌋₊)
              (f := fun q : ℕ =>
                if 1 ≤ q ∧ (q : ℝ) ≤ t then ArithmeticFunction.vonMangoldt q / (q : ℝ) else 0) ?_
            intro q hq
            by_cases hcond : 1 ≤ q ∧ (q : ℝ) ≤ t
            · exfalso
              exact hq (Finset.mem_Icc.mpr ⟨hcond.1, Nat.le_floor hcond.2⟩)
            · simp [hcond]
      _ = ∑ q ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            rcases Finset.mem_Icc.mp hq with ⟨hq1, hqfloor⟩
            have hqt : (q : ℝ) ≤ t := by
              exact (Nat.cast_le.mpr hqfloor).trans (Nat.floor_le ht)
            simp [hq1, hqt]
  have hsumlog : ∀ n : ℕ,
      (∑ m ∈ Finset.Ioc 0 n, Real.log (m : ℝ)) = Real.log (n.factorial : ℝ) := by
    intro n
    rw [← Real.log_prod]
    · congr 1
      rw [← Finset.Ico_succ_succ_eq_Ioc (0 : ℕ) n]
      simpa [Order.succ_eq_add_one] using (show (∏ x ∈ Finset.Ico 1 (n + 1), (x : ℝ)) = (n.factorial : ℝ) by
        rw [← Nat.cast_prod]
        norm_num [Finset.prod_Ico_id_eq_factorial])
    · intro m hm
      have hmpos : 0 < m := (Finset.mem_Ioc.mp hm).1
      exact_mod_cast (ne_of_gt hmpos)
  have hB : ∀ n : ℕ,
      (∑ m ∈ Finset.Ioc 0 n, Real.log (m : ℝ)) =
        ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ) := by
    intro n
    simpa [ArithmeticFunction.vonMangoldt_mul_zeta] using
      (ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n)
  have hfloor_upper : ∀ n q : ℕ, ((n / q : ℕ) : ℝ) ≤ (n : ℝ) / (q : ℝ) := by
    intro n q
    exact Nat.cast_div_le
  have hfloor_lower : ∀ n q : ℕ, (n : ℝ) / (q : ℝ) - 1 ≤ ((n / q : ℕ) : ℝ) := by
    intro n q
    by_cases hq : q = 0
    · subst q
      norm_num
    · have hlt : (n : ℝ) / (q : ℝ) < (⌊(n : ℝ) / (q : ℝ)⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one ((n : ℝ) / (q : ℝ))
      rw [Nat.floor_div_natCast] at hlt
      rw [Nat.floor_natCast] at hlt
      linarith
  have hpsi_le : ∀ n : ℕ,
      (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q) ≤
        (Real.log 4 + 4) * (n : ℝ) := by
    intro n
    simpa [Chebyshev.psi, Nat.floor_natCast] using
      (Chebyshev.psi_le_const_mul_self (x := (n : ℝ)) (by positivity))
  have hlogfac_upper : ∀ n : ℕ,
      Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hfac : (n.factorial : ℝ) ≤ (n ^ n : ℕ) := by
        exact_mod_cast (Nat.factorial_le_pow n)
      have hpos : 0 < (n.factorial : ℝ) := by positivity
      have hlog := Real.log_le_log hpos hfac
      simpa [Nat.cast_pow, Real.log_pow] using hlog
  have hlogfac_lower : ∀ n : ℕ, 1 ≤ n ->
      (n : ℝ) * Real.log (n : ℝ) - (1 + |c0|) * (n : ℝ) ≤
        Real.log (n.factorial : ℝ) := by
    intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    have hs := Stirling.le_log_factorial_stirling (n := n) hn0
    have hlognonneg : 0 ≤ Real.log (n : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hn)
    have hnnonneg : 0 ≤ (n : ℝ) := by positivity
    have hc : -|c0| * (n : ℝ) ≤ c0 := by
      by_cases hc0 : 0 ≤ c0
      · have hleft : -|c0| * (n : ℝ) ≤ 0 := by
          nlinarith [abs_nonneg c0, hnnonneg]
        exact hleft.trans hc0
      · have hc0lt : c0 < 0 := lt_of_not_ge hc0
        have habs : |c0| = -c0 := abs_of_neg hc0lt
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [habs]
        nlinarith
    have hc' : -|Real.log (2 * Real.pi) / 2| * (n : ℝ) ≤ Real.log (2 * Real.pi) / 2 := by
      simpa [c0] using hc
    nlinarith
  have hB_le_nA : ∀ n : ℕ,
      (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ)) ≤
        (n : ℝ) * (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q / (q : ℝ)) := by
    intro n
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro q hq
    have hqpos_nat : 0 < q := (Finset.mem_Ioc.mp hq).1
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqpos_nat
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt q := ArithmeticFunction.vonMangoldt_nonneg
    calc
      ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ)
          ≤ ArithmeticFunction.vonMangoldt q * ((n : ℝ) / (q : ℝ)) := by
            exact mul_le_mul_of_nonneg_left (hfloor_upper n q) hΛ
      _ = (n : ℝ) * (ArithmeticFunction.vonMangoldt q / (q : ℝ)) := by
            field_simp [hqpos.ne']
  have hnA_le_B_psi : ∀ n : ℕ,
      (n : ℝ) * (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q / (q : ℝ)) ≤
        (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ)) +
          ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q := by
    intro n
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro q hq
    have hqpos_nat : 0 < q := (Finset.mem_Ioc.mp hq).1
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqpos_nat
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt q := ArithmeticFunction.vonMangoldt_nonneg
    have hdiv_le : (n : ℝ) / (q : ℝ) ≤ ((n / q : ℕ) : ℝ) + 1 := by
      linarith [hfloor_lower n q]
    calc
      (n : ℝ) * (ArithmeticFunction.vonMangoldt q / (q : ℝ))
          = ArithmeticFunction.vonMangoldt q * ((n : ℝ) / (q : ℝ)) := by
            field_simp [hqpos.ne']
      _ ≤ ArithmeticFunction.vonMangoldt q * (((n / q : ℕ) : ℝ) + 1) := by
            exact mul_le_mul_of_nonneg_left hdiv_le hΛ
      _ = ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ) +
            ArithmeticFunction.vonMangoldt q := by
            ring
  let K1 : ℝ := 1 + |c0|
  let K2 : ℝ := Real.log 4 + 4
  let Cnat : ℝ := max K1 K2
  have hK1_nonneg : 0 ≤ K1 := by
    dsimp [K1]
    positivity
  have hK2_nonneg : 0 ≤ K2 := by
    dsimp [K2]
    have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith
  have hCnat_nonneg : 0 ≤ Cnat := by
    exact hK1_nonneg.trans (le_max_left K1 K2)
  have hK1_le_Cnat : K1 ≤ Cnat := le_max_left K1 K2
  have hK2_le_Cnat : K2 ≤ Cnat := le_max_right K1 K2
  have hnat_ioc : ∀ n : ℕ, 1 ≤ n ->
      |(∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q / (q : ℝ)) -
        Real.log (n : ℝ)| ≤ Cnat := by
    intro n hn
    set A : ℝ := ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q / (q : ℝ)
    set B : ℝ := ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ)
    set P : ℝ := ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q
    have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hB_eq : B = Real.log (n.factorial : ℝ) := by
      dsimp [B]
      exact (hB n).symm.trans (hsumlog n)
    have hB_le : B ≤ (n : ℝ) * A := by
      simpa [A, B] using hB_le_nA n
    have hnA_le : (n : ℝ) * A ≤ B + P := by
      simpa [A, B, P] using hnA_le_B_psi n
    have hP_le : P ≤ K2 * (n : ℝ) := by
      dsimp [P, K2]
      exact hpsi_le n
    have hA_upper : A - Real.log (n : ℝ) ≤ Cnat := by
      have hmul : (n : ℝ) * A ≤ (n : ℝ) * (Real.log (n : ℝ) + K2) := by
        have hfac := hlogfac_upper n
        rw [hB_eq] at hnA_le
        nlinarith
      have hA_le : A ≤ Real.log (n : ℝ) + K2 := le_of_mul_le_mul_left hmul hnpos
      nlinarith
    have hA_lower : -Cnat ≤ A - Real.log (n : ℝ) := by
      have hmul : (n : ℝ) * (Real.log (n : ℝ) - K1) ≤ (n : ℝ) * A := by
        have hfac := hlogfac_lower n hn
        rw [hB_eq] at hB_le
        dsimp [K1]
        nlinarith
      have hlower : Real.log (n : ℝ) - K1 ≤ A := le_of_mul_le_mul_left hmul hnpos
      nlinarith
    exact abs_le.mpr ⟨hA_lower, hA_upper⟩
  have hIoc_eq_Icc : ∀ n : ℕ, Finset.Ioc 0 n = Finset.Icc 1 n := by
    intro n
    ext q
    simp [Finset.mem_Ioc, Finset.mem_Icc, Nat.succ_le_iff]
  refine ⟨Cnat + Real.log 2, ?_, ?_⟩
  · have hlog2_nonneg : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith
  · intro t ht
    have ht0 : 0 ≤ t := by linarith
    let N : ℕ := ⌊t⌋₊
    have hN : 1 ≤ N := by
      dsimp [N]
      exact (Nat.one_le_floor_iff t).mpr ht
    have hpartial := htsum t ht0
    have hnat := hnat_ioc N hN
    have hnat' :
        |(∑ q ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt q / (q : ℝ)) -
          Real.log (N : ℝ)| ≤ Cnat := by
      simpa [hIoc_eq_Icc N] using hnat
    have hNpos_nat : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
    have htpos : 0 < t := by linarith
    have hN_le_t : (N : ℝ) ≤ t := by
      dsimp [N]
      exact Nat.floor_le ht0
    have ht_lt_N_add_one : t < (N : ℝ) + 1 := by
      dsimp [N]
      simpa using (Nat.lt_floor_add_one t)
    have ht_le_twoN : t ≤ 2 * (N : ℝ) := by
      have hN_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hlogN_le_logt : Real.log (N : ℝ) ≤ Real.log t := Real.log_le_log hNpos hN_le_t
    have hlogt_le_log2N : Real.log t ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log htpos ht_le_twoN
    have hlog2N : Real.log (2 * (N : ℝ)) = Real.log (2 : ℝ) + Real.log (N : ℝ) := by
      rw [Real.log_mul] <;> positivity
    have hlogdiff : |Real.log (N : ℝ) - Real.log t| ≤ Real.log (2 : ℝ) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hlogN_le_logt), neg_sub]
      rw [hlog2N] at hlogt_le_log2N
      linarith
    rw [hpartial]
    calc
      |(∑ q ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt q / (q : ℝ)) - Real.log t|
          = |((∑ q ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt q / (q : ℝ)) - Real.log (N : ℝ)) +
              (Real.log (N : ℝ) - Real.log t)| := by
            dsimp [N]
            ring_nf
      _ ≤ |(∑ q ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt q / (q : ℝ)) - Real.log (N : ℝ)| +
            |Real.log (N : ℝ) - Real.log t| := abs_add_le _ _
      _ ≤ Cnat + Real.log (2 : ℝ) := add_le_add hnat' hlogdiff

@[blueprint "lem:mangoldt-tail-range-eq-ico"
  (statement := /-- For every natural cutoff $N$, natural parameter $m$, and
  real threshold $y$, the thresholded range sum of the von Mangoldt tail
  summand is the same as the contiguous sum over
  $\lceil y\rceil\leq q<N$. -/)
  (proof := /-- Rewrite the thresholded range sum as a filtered range sum and
  use the defining universal property of the natural ceiling to identify the
  filter with the interval $[\lceil y\rceil,N)$. -/)
  (title := /-- Thresholded range sums as interval sums -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_range_eq_ico (m N : ℕ) (y : ℝ) :
    (∑ q ∈ Finset.range N,
      if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) =
      ∑ q ∈ Finset.Ico ⌈y⌉₊ N, mangoldt_tail_term m q := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext q
    simp [Nat.ceil_le, and_comm]
  · intro q hq
    rfl

@[blueprint "lem:mangoldt-reciprocal-partial-sum-nat"
  (statement := /-- At a natural cutoff $n$, the real-variable reciprocal von
  Mangoldt partial sum is exactly the finite sum
  $\sum_{1\leq q\leq n}\Lambda(q)/q$. -/)
  (proof := /-- Expand \cref{def:mangoldt-reciprocal-partial-sum}. The
  unconditional sum has support contained in the finite interval
  $1\leq q\leq n$, and on that interval the indicator condition is true. -/)
  (title := /-- Natural cutoffs for reciprocal Mangoldt sums -/)
  (latexEnv := "lemma")]
lemma mangoldt_reciprocal_partial_sum_nat (n : ℕ) :
    mangoldt_reciprocal_partial_sum (n : ℝ) =
      ∑ q ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
  rw [mangoldt_reciprocal_partial_sum]
  calc
    (∑' q : ℕ,
        if 1 ≤ q ∧ (q : ℝ) ≤ (n : ℝ) then
          ArithmeticFunction.vonMangoldt q / (q : ℝ)
        else 0) =
        ∑ q ∈ Finset.Icc 1 n,
          if 1 ≤ q ∧ (q : ℝ) ≤ (n : ℝ) then
            ArithmeticFunction.vonMangoldt q / (q : ℝ)
          else 0 := by
      refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        (s := Finset.Icc 1 n)
        (f := fun q : ℕ =>
          if 1 ≤ q ∧ (q : ℝ) ≤ (n : ℝ) then
            ArithmeticFunction.vonMangoldt q / (q : ℝ)
          else 0) ?_
      intro q hq
      by_cases hcond : 1 ≤ q ∧ (q : ℝ) ≤ (n : ℝ)
      · exfalso
        exact hq (Finset.mem_Icc.mpr ⟨hcond.1, Nat.cast_le.mp hcond.2⟩)
      · exact if_neg hcond
    _ = ∑ q ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      rcases Finset.mem_Icc.mp hq with ⟨hq1, hqn⟩
      have hqr : (q : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hqn
      simp [hq1, hqr]

@[blueprint "lem:real-sub-div-square-le-inv-sub-inv"
  (statement := /-- If $0<a\leq b$, then
  $(b-a)/b^2\leq 1/a-1/b$. -/)
  (proof := /-- Clear the positive denominators $a$ and $b$; the resulting
  polynomial inequality is immediate from $a\leq b$. -/)
  (title := /-- A reciprocal-difference algebra inequality -/)
  (latexEnv := "lemma")]
lemma real_sub_div_square_le_inv_sub_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ^ 2 ≤ 1 / a - 1 / b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  field_simp [ha.ne', hb.ne']
  nlinarith

@[blueprint "lem:mangoldt-log-increment-pointwise-le"
  (statement := /-- If $m\geq 1$ and $r\geq 2$, then the weighted logarithmic
  increment from $r$ to $r+1$ is bounded by the corresponding telescoping
  reciprocal-log difference. -/)
  (proof := /-- Use \cref{lem:real-sub-div-square-le-inv-sub-inv} with
  $a=\log(mr)$ and $b=\log(m(r+1))$.  Positivity and monotonicity of the
  logarithm apply because $mr\geq 2$ and $m(r+1)\geq mr$. -/)
  (title := /-- Pointwise logarithmic-increment comparison -/)
  (latexEnv := "lemma")]
lemma mangoldt_log_increment_pointwise_le (m r : ℕ) (hm : 1 ≤ m) (hr : 2 ≤ r) :
    (Real.log ((r + 1 : ℕ) : ℝ) - Real.log (r : ℝ)) /
        (Real.log (((m * (r + 1) : ℕ) : ℝ))) ^ 2 ≤
      1 / Real.log (((m * r : ℕ) : ℝ)) -
        1 / Real.log (((m * (r + 1) : ℕ) : ℝ)) := by
  have hmr_two : 2 ≤ m * r := by
    exact Nat.mul_le_mul hm hr
  have hmr_pos_log : 0 < Real.log (((m * r : ℕ) : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hmr_two)
  have hmr_le : (m * r : ℕ) ≤ m * (r + 1) := by
    exact Nat.mul_le_mul_left m (Nat.le_succ r)
  have hlog_le : Real.log (((m * r : ℕ) : ℝ)) ≤
      Real.log (((m * (r + 1) : ℕ) : ℝ)) := by
    apply Real.log_le_log
    · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hmr_two)
    · exact_mod_cast hmr_le
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hr_pos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hr)
  have hr_succ_pos : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hlogdiff :
      Real.log (((m * (r + 1) : ℕ) : ℝ)) - Real.log (((m * r : ℕ) : ℝ)) =
        Real.log ((r + 1 : ℕ) : ℝ) - Real.log (r : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    rw [Real.log_mul hm_pos.ne' hr_succ_pos.ne', Real.log_mul hm_pos.ne' hr_pos.ne']
    ring
  have hcore := real_sub_div_square_le_inv_sub_inv hmr_pos_log hlog_le
  rw [hlogdiff] at hcore
  simpa [Nat.cast_mul] using hcore

@[blueprint "lem:log-increment-sum-ico-two"
  (statement := /-- For every natural $r\geq 1$, the logarithmic increments
  from $2$ through $r$ telescope:
  $\sum_{2\leq q<r+1}(\log q-\log(q-1))=\log r$. -/)
  (proof := /-- Reindex by $q=i+1$ and apply the standard telescoping identity
  for $\sum_{1\leq i<r}(\log(i+1)-\log i)$, using $\log 1=0$. -/)
  (title := /-- Telescoping logarithmic increments -/)
  (latexEnv := "lemma")]
lemma log_increment_sum_ico_two (r : ℕ) (hr : 1 ≤ r) :
    (∑ q ∈ Finset.Ico 2 (r + 1),
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) = Real.log (r : ℝ) := by
  rw [show (2 : ℕ) = 1 + 1 by rfl]
  rw [← Finset.sum_Ico_add
    (f := fun q : ℕ => Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))
    (a := 1) (b := r) (c := 1)]
  have hsum := Finset.sum_Ico_sub (m := 1) (n := r)
    (f := fun i : ℕ => Real.log (i : ℝ)) hr
  simpa [Nat.add_comm, Nat.add_assoc, Nat.sub_add_cancel, Real.log_one] using hsum

@[blueprint "lem:mangoldt-reciprocal-sum-ico-two"
  (statement := /-- For every natural $r\geq 1$, the sum of
  $\Lambda(q)/q$ over $2\leq q<r+1$ is the reciprocal von Mangoldt partial sum
  at the natural cutoff $r$. -/)
  (proof := /-- Use \cref{lem:mangoldt-reciprocal-partial-sum-nat}.  The
  interval $2\leq q<r+1$ is $1<q\leq r$, and the omitted $q=1$ term is zero
  because $\Lambda(1)=0$. -/)
  (title := /-- Reciprocal Mangoldt sums from two -/)
  (latexEnv := "lemma")]
lemma mangoldt_reciprocal_sum_ico_two (r : ℕ) (hr : 1 ≤ r) :
    (∑ q ∈ Finset.Ico 2 (r + 1), ArithmeticFunction.vonMangoldt q / (q : ℝ)) =
      mangoldt_reciprocal_partial_sum (r : ℝ) := by
  rw [mangoldt_reciprocal_partial_sum_nat]
  have hI : Finset.Ico 2 (r + 1) = Finset.Ioc 1 r := by
    simpa [Nat.succ_eq_add_one] using (Finset.Ico_succ_succ_eq_Ioc (1 : ℕ) r)
  rw [hI]
  rw [Finset.Icc_eq_cons_Ioc hr]
  simp

@[blueprint "lem:mangoldt-mertens-error-partial-bound"
  (statement := /-- Assume the reciprocal von Mangoldt Mertens error is bounded
  by $D$.  Then for every interval $n\leq q<k$ with $n\geq 2$, the partial sum
  of
  $\Lambda(q)/q-(\log q-\log(q-1))$ has absolute value at most $2D$. -/)
  (proof := /-- The interval sum is the difference of the two endpoint errors
  $\sum_{q\leq r}\Lambda(q)/q-\log r$ at $r=k-1$ and $r=n-1$.  Use
  \cref{lem:mangoldt-reciprocal-sum-ico-two} and
  \cref{lem:log-increment-sum-ico-two} to identify these endpoint errors with
  the real-variable reciprocal partial sums minus $\log r$, then apply the
  assumed Mertens bound and the triangle inequality. -/)
  (title := /-- Bounded partial sums of the Mertens error -/)
  (latexEnv := "lemma")]
lemma mangoldt_mertens_error_partial_bound (D : ℝ) (hD_nonneg : 0 ≤ D)
    (hD : ∀ t : ℝ, 1 ≤ t ->
      |mangoldt_reciprocal_partial_sum t - Real.log t| ≤ D)
    (n k : ℕ) (hn : 2 ≤ n) :
    |∑ q ∈ Finset.Ico n k,
      (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)))| ≤ 2 * D := by
  let e : ℕ → ℝ := fun q =>
    ArithmeticFunction.vonMangoldt q / (q : ℝ) -
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))
  have hendpoint : ∀ r : ℕ, 1 ≤ r -> |∑ q ∈ Finset.Ico 2 (r + 1), e q| ≤ D := by
    intro r hr
    have hrec := mangoldt_reciprocal_sum_ico_two r hr
    have hlog := log_increment_sum_ico_two r hr
    have hsum : (∑ q ∈ Finset.Ico 2 (r + 1), e q) =
        mangoldt_reciprocal_partial_sum (r : ℝ) - Real.log (r : ℝ) := by
      dsimp [e]
      rw [Finset.sum_sub_distrib]
      rw [hrec, hlog]
    rw [hsum]
    exact hD (r : ℝ) (by exact_mod_cast hr)
  by_cases hkn : k ≤ n
  · rw [Finset.Ico_eq_empty_of_le hkn]
    simp
    nlinarith
  · have hnk : n < k := not_le.mp hkn
    have hk_pred_one : 1 ≤ k - 1 := by omega
    have hn_pred_one : 1 ≤ n - 1 := by omega
    have hk_sum := hendpoint (k - 1) hk_pred_one
    have hn_sum := hendpoint (n - 1) hn_pred_one
    have hk_sum' : |∑ q ∈ Finset.Ico 2 k, e q| ≤ D := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hk_sum
    have hn_sum' : |∑ q ∈ Finset.Ico 2 n, e q| ≤ D := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hn_sum
    have hconsec := Finset.sum_Ico_consecutive (f := e) (m := 2) (n := n) (k := k) hn hnk.le
    have hinterval : (∑ q ∈ Finset.Ico n k, e q) =
        (∑ q ∈ Finset.Ico 2 k, e q) - (∑ q ∈ Finset.Ico 2 n, e q) := by
      linarith
    rw [show (∑ q ∈ Finset.Ico n k,
      (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)))) =
        ∑ q ∈ Finset.Ico n k, e q by rfl]
    rw [hinterval]
    calc
      |(∑ q ∈ Finset.Ico 2 k, e q) - (∑ q ∈ Finset.Ico 2 n, e q)| ≤
          |∑ q ∈ Finset.Ico 2 k, e q| + |∑ q ∈ Finset.Ico 2 n, e q| := by
        simpa [sub_eq_add_neg] using
          abs_add_le (∑ q ∈ Finset.Ico 2 k, e q) (-(∑ q ∈ Finset.Ico 2 n, e q))
      _ ≤ D + D := by linarith
      _ = 2 * D := by ring

@[blueprint "lem:mangoldt-mertens-error-weighted-bound"
  (statement := /-- Assume the reciprocal von Mangoldt Mertens error is bounded
  by $D$.  Then, for every $m\geq 1$, $y\geq 2$, and cutoff $N$, the weighted
  interval sum of the Mertens error over $\lceil y\rceil\leq q<N$ is at most
  $4D/\log^2(my)$. -/)
  (proof := /-- Apply summation by parts to the error sequence with weight
  $\log^{-2}(mq)$.  The partial sums are bounded by
  \cref{lem:mangoldt-mertens-error-partial-bound}; the weight is nonnegative
  and decreasing on the interval because $mq\geq my\geq 2$.  The resulting
  endpoint and variation terms are each bounded by $2D/\log^2(my)$. -/)
  (title := /-- Weighted Mertens-error bound -/)
  (latexEnv := "lemma")]
lemma mangoldt_mertens_error_weighted_bound (D : ℝ) (hD_nonneg : 0 ≤ D)
    (hD : ∀ t : ℝ, 1 ≤ t ->
      |mangoldt_reciprocal_partial_sum t - Real.log t| ≤ D)
    (m N : ℕ) (hm : 1 ≤ m) (y : ℝ) (hy : 2 ≤ y) :
    (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
      (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
          (Real.log (((m * q : ℕ) : ℝ))) ^ 2) ≤
      4 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
  let n : ℕ := ⌈y⌉₊
  let e : ℕ → ℝ := fun q =>
    ArithmeticFunction.vonMangoldt q / (q : ℝ) -
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))
  let w : ℕ → ℝ := fun q => 1 / (Real.log (((m * q : ℕ) : ℝ))) ^ 2
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hy_nonneg : 0 ≤ y := by linarith
  have hmy_two : (2 : ℝ) ≤ (m : ℝ) * y := by
    calc
      (2 : ℝ) ≤ 1 * y := by simpa using hy
      _ ≤ (m : ℝ) * y := by
        exact mul_le_mul_of_nonneg_right hm_real hy_nonneg
  have hLpos : 0 < Real.log ((m : ℝ) * y) := by
    exact Real.log_pos (by linarith)
  have hyn : y ≤ (n : ℝ) := by
    simpa [n] using Nat.le_ceil y
  have hn : 2 ≤ n := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := hy.trans hyn
    exact_mod_cast h2n
  rw [show ⌈y⌉₊ = n by rfl]
  by_cases hN : n < N
  · let g : ℕ → ℝ := fun q => if n ≤ q then e q else 0
    have hG_eq : ∀ k : ℕ, (∑ q ∈ Finset.range k, g q) = ∑ q ∈ Finset.Ico n k, e q := by
      intro k
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext q
        simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
      · intro q hq
        simp [g, (Finset.mem_Ico.mp hq).1]
    have hG_bound : ∀ k : ℕ, |∑ q ∈ Finset.range k, g q| ≤ 2 * D := by
      intro k
      rw [hG_eq k]
      exact mangoldt_mertens_error_partial_bound D hD_nonneg hD n k hn
    have htarget :
        (∑ q ∈ Finset.Ico n N,
          (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
            (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
              (Real.log (((m * q : ℕ) : ℝ))) ^ 2) =
          ∑ q ∈ Finset.range N, w q * g q := by
      symm
      dsimp [g]
      simp_rw [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext q
        simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
      · intro q hq
        dsimp [w, e]
        ring
    rw [htarget]
    have hbp := Finset.sum_range_by_parts (f := w) (g := g) (n := N)
    have hbp' : ∑ i ∈ Finset.range N, w i * g i =
        w (N - 1) * (∑ i ∈ Finset.range N, g i) -
          ∑ i ∈ Finset.range (N - 1),
            (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) := by
      simpa only [smul_eq_mul] using hbp
    rw [hbp']
    have hLsq_pos : 0 < (Real.log ((m : ℝ) * y)) ^ 2 := sq_pos_of_pos hLpos
    have htwoD_nonneg : 0 ≤ 2 * D := by positivity
    have hfourD_nonneg : 0 ≤ 4 * D := by positivity
    have hN_pred_ge : n ≤ N - 1 := Nat.le_pred_of_lt hN
    have hN_pred_two : 2 ≤ N - 1 := hn.trans hN_pred_ge
    have hw_le_L : ∀ q : ℕ, n ≤ q -> w q ≤ 1 / (Real.log ((m : ℝ) * y)) ^ 2 := by
      intro q hnq
      have hq_real : y ≤ (q : ℝ) := hyn.trans (by exact_mod_cast hnq)
      have harg : (m : ℝ) * y ≤ (((m * q : ℕ) : ℝ)) := by
        rw [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_left hq_real (by positivity)
      have hlog : Real.log ((m : ℝ) * y) ≤ Real.log (((m * q : ℕ) : ℝ)) :=
        Real.log_le_log (by linarith) harg
      dsimp [w]
      gcongr
    have hw_nonneg : ∀ q : ℕ, n ≤ q -> 0 ≤ w q := by
      intro q hnq
      dsimp [w]
      positivity
    have hboundary : w (N - 1) * (∑ i ∈ Finset.range N, g i) ≤
        2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
      have hG_le : (∑ i ∈ Finset.range N, g i) ≤ 2 * D :=
        (le_abs_self _).trans (hG_bound N)
      have hwN_nonneg : 0 ≤ w (N - 1) := hw_nonneg (N - 1) hN_pred_ge
      have hwN_le := hw_le_L (N - 1) hN_pred_ge
      calc
        w (N - 1) * (∑ i ∈ Finset.range N, g i) ≤ w (N - 1) * (2 * D) := by
          exact mul_le_mul_of_nonneg_left hG_le hwN_nonneg
        _ ≤ (1 / (Real.log ((m : ℝ) * y)) ^ 2) * (2 * D) := by
          exact mul_le_mul_of_nonneg_right hwN_le htwoD_nonneg
        _ = 2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by ring
    have hvar_point : ∀ i ∈ Finset.range (N - 1),
        -((w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)) ≤
          2 * D * (if n ≤ i then w i - w (i + 1) else 0) := by
      intro i hi
      by_cases hni : n ≤ i
      · have hi_tail : n ≤ i + 1 := hni.trans (Nat.le_succ i)
        have hG_le : (∑ j ∈ Finset.range (i + 1), g j) ≤ 2 * D :=
          (le_abs_self _).trans (hG_bound (i + 1))
        have hw_mono : w (i + 1) ≤ w i := by
          have harg : (((m * i : ℕ) : ℝ)) ≤ (((m * (i + 1) : ℕ) : ℝ)) := by
            exact_mod_cast Nat.mul_le_mul_left m (Nat.le_succ i)
          have hi_two : 2 ≤ i := hn.trans hni
          have hlog_pos_i : 0 < Real.log (((m * i : ℕ) : ℝ)) := by
            have htwo : 2 ≤ m * i := Nat.mul_le_mul hm hi_two
            apply Real.log_pos
            exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two htwo)
          have hlog_le : Real.log (((m * i : ℕ) : ℝ)) ≤
              Real.log (((m * (i + 1) : ℕ) : ℝ)) :=
            Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two (Nat.mul_le_mul hm hi_two))) harg
          dsimp [w]
          gcongr
        have hdiff_nonneg : 0 ≤ w i - w (i + 1) := sub_nonneg.mpr hw_mono
        calc
          -((w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)) =
              (w i - w (i + 1)) * (∑ j ∈ Finset.range (i + 1), g j) := by ring
          _ ≤ (w i - w (i + 1)) * (2 * D) := by
            exact mul_le_mul_of_nonneg_left hG_le hdiff_nonneg
          _ = 2 * D * (if n ≤ i then w i - w (i + 1) else 0) := by simp [hni, mul_comm, mul_left_comm, mul_assoc]
      · have hG_zero : (∑ j ∈ Finset.range (i + 1), g j) = 0 := by
          rw [hG_eq (i + 1)]
          rw [Finset.Ico_eq_empty_of_le]
          · simp
          · omega
        simp [hni, hG_zero]
    have hvariation :
        -∑ i ∈ Finset.range (N - 1),
          (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) ≤
          2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
      calc
        -∑ i ∈ Finset.range (N - 1),
          (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) =
            ∑ i ∈ Finset.range (N - 1),
              -((w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)) := by
          rw [Finset.sum_neg_distrib]
        _ ≤ ∑ i ∈ Finset.range (N - 1),
              2 * D * (if n ≤ i then w i - w (i + 1) else 0) := by
          exact Finset.sum_le_sum hvar_point
        _ = 2 * D * (∑ i ∈ Finset.Ico n (N - 1), (w i - w (i + 1))) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext i
            simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
          · intro i hi
            simp [(Finset.mem_Ico.mp hi).1]
        _ = 2 * D * (w n - w (N - 1)) := by
          have hsum := Finset.sum_Ico_sub (m := n) (n := N - 1) (f := w) hN_pred_ge
          have hsum' : (∑ i ∈ Finset.Ico n (N - 1), (w i - w (i + 1))) = w n - w (N - 1) := by
            calc
              (∑ i ∈ Finset.Ico n (N - 1), (w i - w (i + 1))) =
                  - (∑ i ∈ Finset.Ico n (N - 1), (w (i + 1) - w i)) := by
                rw [← Finset.sum_neg_distrib]
                apply Finset.sum_congr rfl
                intro i hi
                ring
              _ = -(w (N - 1) - w n) := by rw [hsum]
              _ = w n - w (N - 1) := by ring
          rw [hsum']
        _ ≤ 2 * D * w n := by
          have hwN_nonneg : 0 ≤ w (N - 1) := hw_nonneg (N - 1) hN_pred_ge
          nlinarith [htwoD_nonneg]
        _ ≤ 2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
          have hwn_le := hw_le_L n le_rfl
          calc
            2 * D * w n ≤ 2 * D * (1 / (Real.log ((m : ℝ) * y)) ^ 2) := by
              exact mul_le_mul_of_nonneg_left hwn_le htwoD_nonneg
            _ = 2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by ring
    calc
      w (N - 1) * (∑ i ∈ Finset.range N, g i) -
          ∑ i ∈ Finset.range (N - 1),
            (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) ≤
          2 * D / (Real.log ((m : ℝ) * y)) ^ 2 +
            2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
        linarith
      _ = 4 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by ring
  · rw [Finset.Ico_eq_empty_of_le (not_lt.mp hN)]
    simp
    positivity

@[blueprint "lem:mangoldt-log-increment-weighted-bound"
  (statement := /-- Let $m\geq 1$, $y\geq 2$, and $N$ be natural.  With
  $n=\lceil y\rceil$, the weighted logarithmic-increment sum over
  $n\leq q<N$ is bounded by
  $1/\log(my)+\log(2)/\log^2(my)$. -/)
  (proof := /-- The first increment is at most $\log 2$ times the initial
  weight.  For later increments, apply
  \cref{lem:mangoldt-log-increment-pointwise-le} to compare
  $(\log q-\log(q-1))/\log^2(mq)$ with the telescoping difference
  $1/\log(m(q-1))-1/\log(mq)$.  Since $\lceil y\rceil\geq y$, the endpoint
  discrepancy is absorbed by the displayed $\log 2$ error term. -/)
  (title := /-- Weighted logarithmic increments -/)
  (latexEnv := "lemma")]
lemma mangoldt_log_increment_weighted_bound (m N : ℕ) (hm : 1 ≤ m) (y : ℝ)
    (hy : 2 ≤ y) :
    (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
        (Real.log (((m * q : ℕ) : ℝ))) ^ 2) ≤
      1 / Real.log ((m : ℝ) * y) +
        Real.log 2 / (Real.log ((m : ℝ) * y)) ^ 2 := by
  let n : ℕ := ⌈y⌉₊
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hy_nonneg : 0 ≤ y := by linarith
  have hmy_two : (2 : ℝ) ≤ (m : ℝ) * y := by
    calc
      (2 : ℝ) ≤ 1 * y := by simpa using hy
      _ ≤ (m : ℝ) * y := by
        exact mul_le_mul_of_nonneg_right hm_real hy_nonneg
  have hLpos : 0 < Real.log ((m : ℝ) * y) := by
    exact Real.log_pos (by linarith)
  have hyn : y ≤ (n : ℝ) := by
    simpa [n] using Nat.le_ceil y
  have hn : 2 ≤ n := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := hy.trans hyn
    exact_mod_cast h2n
  by_cases hN : n < N
  · rw [show ⌈y⌉₊ = n by rfl]
    rw [← Finset.add_sum_Ioo_eq_sum_Ico
      (f := fun q : ℕ =>
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
          (Real.log (((m * q : ℕ) : ℝ))) ^ 2) hN]
    have hn_real : (2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hnum : Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log 2 := by
      have hnpos : 0 < n := by omega
      have hn1pos : 0 < n - 1 := by omega
      have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hnpos)
      have hn1_ne : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hn1pos)
      rw [← Real.log_div hn_ne hn1_ne]
      apply Real.log_le_log
      · positivity
      · field_simp [hn1_ne]
        rw [Nat.cast_sub (by omega : 1 ≤ n)] at *
        norm_num at *
        nlinarith
    have hlog_mn : Real.log ((m : ℝ) * y) ≤ Real.log (((m * n : ℕ) : ℝ)) := by
      have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
      have harg : (m : ℝ) * y ≤ (((m * n : ℕ) : ℝ)) := by
        rw [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_left hyn hm_nonneg
      exact Real.log_le_log (by linarith) harg
    have hlog_mn_pos : 0 < Real.log (((m * n : ℕ) : ℝ)) := hLpos.trans_le hlog_mn
    have hfirst :
        (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) /
            (Real.log (((m * n : ℕ) : ℝ))) ^ 2 ≤
          Real.log 2 / (Real.log ((m : ℝ) * y)) ^ 2 := by
      have hstep₁ :
          (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) /
              (Real.log (((m * n : ℕ) : ℝ))) ^ 2 ≤
            Real.log 2 / (Real.log (((m * n : ℕ) : ℝ))) ^ 2 := by
        gcongr
      have hstep₂ :
          Real.log 2 / (Real.log (((m * n : ℕ) : ℝ))) ^ 2 ≤
            Real.log 2 / (Real.log ((m : ℝ) * y)) ^ 2 := by
        gcongr
      exact hstep₁.trans hstep₂
    let F : ℕ → ℝ := fun r => 1 / Real.log (((m * r : ℕ) : ℝ))
    have htel :
        (∑ x ∈ Finset.Ioo n N, (F (x - 1) - F x)) = F n - F (N - 1) := by
      rw [← Finset.Ico_succ_left_eq_Ioo]
      rw [show Order.succ n = n + 1 by rfl]
      rw [show N = N - 1 + 1 by omega]
      rw [← Finset.sum_Ico_add
        (f := fun x : ℕ => F (x - 1) - F x) (a := n) (b := N - 1) (c := 1)]
      have hsum := Finset.sum_Ico_sub (m := n) (n := N - 1) (f := F)
        (Nat.le_pred_of_lt hN)
      have hsum' :
          (∑ i ∈ Finset.Ico n (N - 1), (F i - F (i + 1))) = F n - F (N - 1) := by
        calc
          (∑ i ∈ Finset.Ico n (N - 1), (F i - F (i + 1))) =
              - (∑ i ∈ Finset.Ico n (N - 1), (F (i + 1) - F i)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = -(F (N - 1) - F n) := by rw [hsum]
          _ = F n - F (N - 1) := by ring
      simpa [Nat.add_comm, Nat.add_assoc, Nat.sub_add_cancel] using hsum'
    have htail_point : ∀ x ∈ Finset.Ioo n N,
        (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
            (Real.log (((m * x : ℕ) : ℝ))) ^ 2 ≤ F (x - 1) - F x := by
      intro x hx
      have hx_left : n < x := (Finset.mem_Ioo.mp hx).1
      have hx_pred_ge : 2 ≤ x - 1 := by omega
      have hx_one_le : 1 ≤ x := by omega
      have h := mangoldt_log_increment_pointwise_le m (x - 1) hm hx_pred_ge
      dsimp [F]
      simpa [Nat.sub_add_cancel hx_one_le] using h
    have htail_le :
        (∑ x ∈ Finset.Ioo n N,
          (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
            (Real.log (((m * x : ℕ) : ℝ))) ^ 2) ≤ F n - F (N - 1) := by
      calc
        (∑ x ∈ Finset.Ioo n N,
          (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
            (Real.log (((m * x : ℕ) : ℝ))) ^ 2) ≤
            ∑ x ∈ Finset.Ioo n N, (F (x - 1) - F x) := by
          exact Finset.sum_le_sum htail_point
        _ = F n - F (N - 1) := htel
    have hN_pred_ge : n ≤ N - 1 := Nat.le_pred_of_lt hN
    have hN_pred_two : 2 ≤ N - 1 := hn.trans hN_pred_ge
    have hlog_N_pred_pos : 0 < Real.log (((m * (N - 1) : ℕ) : ℝ)) := by
      have htwo : 2 ≤ m * (N - 1) := Nat.mul_le_mul hm hN_pred_two
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two htwo)
    have hF_N_nonneg : 0 ≤ F (N - 1) := by
      dsimp [F]
      positivity
    have htail :
        (∑ x ∈ Finset.Ioo n N,
          (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
            (Real.log (((m * x : ℕ) : ℝ))) ^ 2) ≤
          1 / Real.log ((m : ℝ) * y) := by
      have hFn : F n ≤ 1 / Real.log ((m : ℝ) * y) := by
        dsimp [F]
        gcongr
      linarith
    linarith
  · rw [show ⌈y⌉₊ = n by rfl]
    rw [Finset.Ico_eq_empty_of_le (not_lt.mp hN)]
    simp
    positivity

@[blueprint "lem:mangoldt-tail-range-sum-bound"
  (statement := /-- There is a real constant $C\geq 0$ such that, for every
  natural $m\geq 1$, every real $y\geq 2$, and every natural cutoff $N$, the
  finite thresholded range sum of the von Mangoldt tail summand up to $N$ is at
  most $1/\log(my)+C/\log^2(my)$. -/)
  (proof := /-- Rewrite the thresholded range sum using
  \cref{lem:mangoldt-tail-range-eq-ico}.  Decompose $\Lambda(q)/q$ into the
  logarithmic increment $\log q-\log(q-1)$ plus the reciprocal-Mertens error.
  The logarithmic-increment contribution is bounded by
  \cref{lem:mangoldt-log-increment-weighted-bound}.  Choose the Mertens
  constant from \cref{lem:mertens-von-mangoldt-reciprocal} and apply
  \cref{lem:mangoldt-mertens-error-weighted-bound} to the error contribution.
  Adding the two estimates gives the stated finite range bound after taking the
  constant $\log 2+4D$. -/)
  (title := /-- Finite range form of the Mangoldt tail bound -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_range_sum_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m -> ∀ y : ℝ, 2 ≤ y -> ∀ N : ℕ,
      (∑ q ∈ Finset.range N,
        if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) ≤
        1 / Real.log ((m : ℝ) * y) + C / (Real.log ((m : ℝ) * y)) ^ 2 := by
  obtain ⟨D, hD_nonneg, hD⟩ := mertens_von_mangoldt_reciprocal
  refine ⟨Real.log 2 + 4 * D, by positivity, ?_⟩
  intro m hm y hy N
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hy_nonneg : 0 ≤ y := by linarith
  have hmy_two : (2 : ℝ) ≤ (m : ℝ) * y := by
    calc
      (2 : ℝ) ≤ 1 * y := by simpa using hy
      _ ≤ (m : ℝ) * y := by
        exact mul_le_mul_of_nonneg_right hm_real hy_nonneg
  have hLpos : 0 < Real.log ((m : ℝ) * y) := by
    exact Real.log_pos (by linarith)
  rw [mangoldt_tail_range_eq_ico]
  let n : ℕ := ⌈y⌉₊
  have hn : 2 ≤ n := by
    have hyn : y ≤ (n : ℝ) := by
      simpa [n] using Nat.le_ceil y
    have h2n : (2 : ℝ) ≤ (n : ℝ) := hy.trans hyn
    exact_mod_cast h2n
  have hsplit :
      (∑ q ∈ Finset.Ico ⌈y⌉₊ N, mangoldt_tail_term m q) =
        (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
            (Real.log (((m * q : ℕ) : ℝ))) ^ 2) +
        (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
          (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
            (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
              (Real.log (((m * q : ℕ) : ℝ))) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [mangoldt_tail_term]
    ring
  have hmain := mangoldt_log_increment_weighted_bound m N hm y hy
  have herror := mangoldt_mertens_error_weighted_bound D hD_nonneg hD m N hm y hy
  rw [hsplit]
  calc
    (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
          (Real.log (((m * q : ℕ) : ℝ))) ^ 2) +
      (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
        (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
            (Real.log (((m * q : ℕ) : ℝ))) ^ 2) ≤
        (1 / Real.log ((m : ℝ) * y) +
          Real.log 2 / (Real.log ((m : ℝ) * y)) ^ 2) +
          4 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
      exact add_le_add hmain herror
    _ = 1 / Real.log ((m : ℝ) * y) +
        (Real.log 2 + 4 * D) / (Real.log ((m : ℝ) * y)) ^ 2 := by
      ring

@[blueprint "lem:mangoldt-tail-upper-bound"
  (statement := /-- There is a real constant $C\geq 0$, independent of $m$ and
  $y$, such that, for every natural $m\geq 1$ and every real $y\geq 2$, the von
  Mangoldt tail series is summable and
  $\sum_{q\geq y}\Lambda(q)/(q\log^2(mq))\leq
  1/\log(my)+C/\log^2(my)$. -/)
  (proof := /-- Choose the constant supplied by
  \cref{lem:mangoldt-tail-range-sum-bound}.  For fixed $m\geq 1$ and
  $y\geq 2$, the tail summands are non-negative, so the uniform finite-range
  bound implies summability of the corresponding series.  The standard
  comparison of a non-negative real series with its bounded partial sums then
  gives the same bound for the t-sum defining the von Mangoldt tail. -/)
  (title := /-- Upper von Mangoldt tail estimate -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_upper_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m -> ∀ y : ℝ, 2 ≤ y ->
      Summable (fun q : ℕ => if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) ∧
        mangoldt_tail_sum m y ≤
          1 / Real.log ((m : ℝ) * y) + C / (Real.log ((m : ℝ) * y)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := mangoldt_tail_range_sum_bound
  refine ⟨C, hC, ?_⟩
  intro m hm y hy
  have hnonneg : ∀ q : ℕ, 0 ≤
      (if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) := by
    intro q
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · norm_num
  have hsumm : Summable (fun q : ℕ =>
      if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) :=
    summable_of_sum_range_le hnonneg (hbound m hm y hy)
  refine ⟨hsumm, ?_⟩
  simpa [mangoldt_tail_sum] using
    hsumm.tsum_le_of_sum_range_le (hbound m hm y hy)

@[blueprint "lem:mangoldt-tail-finite-sum-le"
  (statement := /-- Let $m$ be a natural number with $m\geq 1$, let $y$ be a
  real number with $y\geq 2$, and let $S$ be a finite set of natural numbers.
  Then
  $\sum_{q\in S}1_{y\leq q}\Lambda(q)/(q\log^2(mq))\leq
  \sum_{q\geq y}\Lambda(q)/(q\log^2(mq))$. -/)
  (proof := /-- By \cref{lem:mangoldt-tail-upper-bound}, the series defining
  \cref{def:mangoldt-tail-sum} is summable for the stated values of $m$ and
  $y$.  The summand in \cref{def:mangoldt-tail-term} is non-negative whenever
  it is selected: the von Mangoldt function is non-negative and the denominator
  is non-negative; the unselected summands are zero.  The standard comparison of
  a finite sum with the t-sum of a summable real series whose omitted terms are
  non-negative gives the asserted bound for the finite set $S$. -/)
  (title := /-- Finite tails are bounded by the full von Mangoldt tail -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_finite_sum_le (m : ℕ) (hm : 1 ≤ m) (y : ℝ) (hy : 2 ≤ y)
    (s : Finset ℕ) :
    (∑ q ∈ s, if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) ≤
      mangoldt_tail_sum m y := by
  obtain ⟨_, _, hbound⟩ := mangoldt_tail_upper_bound
  have hsumm : Summable (fun q : ℕ =>
      if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) :=
    (hbound m hm y hy).1
  have hnonneg : ∀ q : ℕ, 0 ≤
      (if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) := by
    intro q
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · norm_num
  simpa [mangoldt_tail_sum] using hsumm.sum_le_tsum s (fun q _ => hnonneg q)

@[blueprint "def:finite-chain-initial-mass"
  (statement := /-- For real parameters $x$ and $X$, and for a natural number
  $n$, this is the finite initial mass
  $b_{x,X}(n)$ used in the truncated von Mangoldt downward chain. It is zero
  outside the real interval $[x,X]$, while on that interval it is
  $\nu_0(n)$ minus the total incoming von Mangoldt mass from states $nq\leq X$,
  namely
  $\sum_{q\geq2,\ nq\leq X}\nu_0(nq)\Lambda(q)/\log(nq)$. -/)
  (title := /-- Finite von Mangoldt initial mass -/)
  (latexEnv := "definition")]
noncomputable def finite_chain_initial_mass (x X : ℝ) (n : ℕ) : ℝ :=
  if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then
    erdos_weight n -
      ∑' q : ℕ,
        if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
          erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
            Real.log ((n * q : ℕ) : ℝ)
        else 0
  else 0

@[blueprint "lem:finite-chain-initial-mass-sum-eq-cut-capacity"
  (statement := /-- For every $x\geq2$ and every real $X$, the total finite
  initial mass $\sum_n b_{x,X}(n)$ from
  \cref{def:finite-chain-initial-mass} is exactly the finite cut capacity
  \cref{def:cut-capacity}. -/)
  (proof := /-- Expand \cref{def:finite-chain-initial-mass}.  The first part of
  the total mass is
  $\sum_{x\leq r\leq X}\nu_0(r)$; by
  \cref{lem:von-mangoldt-divisor-sum} and \cref{def:erdos-weight}, this is
  $\sum_{x\leq r\leq X}(r\log^2 r)^{-1}\sum_{q\mid r}\Lambda(q)$, with
  $x\geq2$ excluding the singular cases $r=0,1$.  The second part is a finite
  double sum over pairs $(n,q)$ with $x\leq n\leq X$, $q\geq2$, and $nq\leq X$.
  Relabeling $r=nq$ identifies this double sum with
  $\sum_{x\leq r\leq X}(r\log^2 r)^{-1}
  \sum_{q\mid r,\ r/q\geq x}\Lambda(q)$.  Subtracting the latter divisor sum
  from the former leaves exactly those divisors $q\mid r$ for which
  $r/q<x$, which is the summand in \cref{def:cut-capacity}. -/)
  (title := /-- Total initial mass equals cut capacity -/)
  (latexEnv := "lemma")]
lemma finite_chain_initial_mass_sum_eq_cut_capacity (x X : ℝ) (hx : 2 ≤ x) :
    (∑' n : ℕ, finite_chain_initial_mass x X n) = cut_capacity x X := by
  classical
  let s : Finset ℕ := Finset.range (⌈X⌉₊ + 1)
  let coeff : ℕ → ℝ := fun r => 1 / ((r : ℝ) * Real.log (r : ℝ) ^ 2)
  let pairTerm : ℕ × ℕ → ℝ := fun p =>
    if x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X then
      if 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X) then
        coeff (p.1 * p.2) * ArithmeticFunction.vonMangoldt p.2
      else 0
    else 0
  have hincoming_point (n q : ℕ)
      (hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X)
      (hqcond : 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X) :
      erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
          Real.log ((n * q : ℕ) : ℝ) =
        coeff (n * q) * ArithmeticFunction.vonMangoldt q := by
    have hprod_gt_one : (1 : ℝ) < ((n * q : ℕ) : ℝ) := by
      have hn_ge_two_real : (2 : ℝ) ≤ (n : ℝ) := le_trans hx hnint.1
      have hq_ge_two_real : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqcond.1
      rw [Nat.cast_mul]
      nlinarith
    have hlog_ne : Real.log ((n * q : ℕ) : ℝ) ≠ 0 :=
      (Real.log_pos hprod_gt_one).ne'
    rw [erdos_weight]
    dsimp [coeff]
    field_simp [hlog_ne]
  have hleft : (∑' n : ℕ, finite_chain_initial_mass x X n) =
      ∑ n ∈ s, finite_chain_initial_mass x X n := by
    exact tsum_eq_sum (s := s) (fun n hn => by
      rw [finite_chain_initial_mass]
      rw [if_neg]
      intro hnx
      apply hn
      simp only [s, Finset.mem_range]
      have hnleceil : n ≤ ⌈X⌉₊ := by
        exact_mod_cast (le_trans hnx.2 (Nat.le_ceil X))
      omega)
  have hinner (n : ℕ) (hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) :
      (∑' q : ℕ,
        if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
          erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
            Real.log ((n * q : ℕ) : ℝ)
        else 0) =
      ∑ q ∈ s,
        if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
          erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
            Real.log ((n * q : ℕ) : ℝ)
        else 0 := by
    refine tsum_eq_sum (s := s) ?_
    intro q hq
    rw [if_neg]
    intro hcond
    apply hq
    simp only [s, Finset.mem_range]
    have hn_ge_one : 1 ≤ n := by
      have hn_ge_two_real : (2 : ℝ) ≤ (n : ℝ) := le_trans hx hnint.1
      exact_mod_cast (show (1 : ℝ) ≤ (n : ℝ) by linarith)
    have hq_le_prod : q ≤ n * q := Nat.le_mul_of_pos_left q hn_ge_one
    have hq_le_X : (q : ℝ) ≤ X := by
      have : ((q : ℕ) : ℝ) ≤ ((n * q : ℕ) : ℝ) := by exact_mod_cast hq_le_prod
      exact le_trans this hcond.2
    have hq_le_ceil : q ≤ ⌈X⌉₊ := by
      exact_mod_cast (le_trans hq_le_X (Nat.le_ceil X))
    omega
  have hleft_expand :
      (∑' n : ℕ, finite_chain_initial_mass x X n) =
        (∑ n ∈ s, if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) -
          ∑ p ∈ s.product s, pairTerm p := by
    rw [hleft]
    calc
      (∑ n ∈ s, finite_chain_initial_mass x X n)
          = ∑ n ∈ s,
              ((if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) -
                ∑ q ∈ s, pairTerm (n, q)) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [finite_chain_initial_mass]
            by_cases hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X
            · rw [if_pos hnint, hinner n hnint]
              simp only [if_pos hnint]
              congr 1
              apply Finset.sum_congr rfl
              intro q hq
              by_cases hqcond : 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X
              · rw [if_pos hqcond, hincoming_point n q hnint hqcond]
                have hqcond' : 2 ≤ q ∧ (n : ℝ) * (q : ℝ) ≤ X := by
                  exact ⟨hqcond.1, by simpa [Nat.cast_mul] using hqcond.2⟩
                simp [pairTerm, hnint, hqcond, hqcond', Nat.cast_mul]
              · rw [if_neg hqcond]
                have hqcond' : ¬(2 ≤ q ∧ (n : ℝ) * (q : ℝ) ≤ X) := by
                  intro h
                  apply hqcond
                  exact ⟨h.1, by simpa [Nat.cast_mul] using h.2⟩
                simp [pairTerm, hnint, hqcond, hqcond', Nat.cast_mul]
            · rw [if_neg hnint]
              simp [pairTerm, hnint]
      _ = (∑ n ∈ s, if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) -
            ∑ n ∈ s, ∑ q ∈ s, pairTerm (n, q) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ n ∈ s, if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) -
            ∑ p ∈ s.product s, pairTerm p := by
          simpa using congrArg
            (fun z => (∑ n ∈ s,
              if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) - z)
            (Finset.sum_product (s := s) (t := s)
              (f := fun p : ℕ × ℕ => pairTerm p)).symm
  have hright : cut_capacity x X =
      ∑ r ∈ s,
        if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
          coeff r * (∑ q ∈ r.divisors,
            if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
        else 0 := by
    rw [cut_capacity]
    calc
      (∑' r : ℕ,
        if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
          (1 / ((r : ℝ) * (Real.log (r : ℝ)) ^ 2)) *
            (∑ q ∈ r.divisors,
              if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
        else 0)
          = ∑ r ∈ s,
              if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
                (1 / ((r : ℝ) * (Real.log (r : ℝ)) ^ 2)) *
                  (∑ q ∈ r.divisors,
                    if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
              else 0 := by
            exact tsum_eq_sum (s := s) (fun r hr => by
              rw [if_neg]
              intro hrx
              apply hr
              simp only [s, Finset.mem_range]
              have hrleceil : r ≤ ⌈X⌉₊ := by
                exact_mod_cast (le_trans hrx.2 (Nat.le_ceil X))
              omega)
      _ = ∑ r ∈ s,
          if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
            coeff r * (∑ q ∈ r.divisors,
              if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            by_cases hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
            · simp [coeff, hrint]
            · simp [hrint]
  have hbase_point (r : ℕ) (hr : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X) :
      erdos_weight r = coeff r * (∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q) := by
    have hr_gt_one : (1 : ℝ) < (r : ℝ) := by linarith [le_trans hx hr.1]
    have hlog_ne : Real.log (r : ℝ) ≠ 0 := (Real.log_pos hr_gt_one).ne'
    rw [von_mangoldt_divisor_sum, erdos_weight]
    dsimp [coeff]
    field_simp [hlog_ne]
  have hbase_sum :
      (∑ n ∈ s, if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) =
        ∑ r ∈ s,
          if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
            coeff r * (∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q)
          else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
    · rw [if_pos hrint, if_pos hrint, hbase_point r hrint]
    · simp [hrint]
  have hpair_fiber (r : ℕ) (hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X)
      (p : ℕ × ℕ) (hp : p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r)) :
      pairTerm p =
        if 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ) then coeff r * ArithmeticFunction.vonMangoldt p.2 else 0 := by
    have hprod : p.1 * p.2 = r := (Finset.mem_filter.mp hp).2
    by_cases hcond : 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ)
    · have hp2_ge_one : 1 ≤ p.2 := by omega
      have hp1_le_prod : p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right p.1 hp2_ge_one
      have hp1_le_X : (p.1 : ℝ) ≤ X := by
        have : (p.1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by exact_mod_cast hp1_le_prod
        rw [hprod] at this
        exact le_trans this hrint.2
      have hprod_le_X : (((p.1 * p.2 : ℕ) : ℝ) ≤ X) := by simpa [hprod] using hrint.2
      have hprod_le_X' : (p.1 : ℝ) * (p.2 : ℝ) ≤ X := by
        simpa [Nat.cast_mul] using hprod_le_X
      have hcond' : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X) := ⟨hcond.1, hprod_le_X⟩
      have hcond'' : 2 ≤ p.2 ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X := ⟨hcond.1, hprod_le_X'⟩
      have houter : x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X := ⟨hcond.2, hp1_le_X⟩
      have hprod_coeff : coeff (p.1 * p.2) = coeff r := by rw [hprod]
      simp [pairTerm, houter, hcond', hcond'', hcond, hprod_coeff, Nat.cast_mul]
    · have hnot_outer_or_inner :
          ¬(x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X) ∨
            ¬(2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)) := by
        by_cases houter : x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X
        · right
          intro hinner
          apply hcond
          exact ⟨hinner.1, houter.1⟩
        · exact Or.inl houter
      rcases hnot_outer_or_inner with houter | hinner
      · simp [pairTerm, houter, hcond]
      · have hinner' : ¬(2 ≤ p.2 ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X) := by
          intro h
          apply hinner
          exact ⟨h.1, by simpa [Nat.cast_mul] using h.2⟩
        simp [pairTerm, hinner, hinner', hcond, Nat.cast_mul]
  have hbij_sum (r : ℕ) (hrmem : r ∈ s) (hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X) :
      (∑ p ∈ ((s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r)).filter
          (fun p : ℕ × ℕ => 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ)),
          coeff r * ArithmeticFunction.vonMangoldt p.2) =
        ∑ q ∈ r.divisors.filter (fun q : ℕ => 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ)),
          coeff r * ArithmeticFunction.vonMangoldt q := by
    refine Finset.sum_bij' (fun p hp => p.2) (fun q hq => (r / q, q)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hpfiber, hpcond⟩
      have hprod : p.1 * p.2 = r := hpfiber.2
      have hr_ne : r ≠ 0 := by
        have : (0 : ℝ) < (r : ℝ) := by linarith [hx, hrint.1]
        exact_mod_cast this.ne'
      have hp2pos : 0 < p.2 := by omega
      have hp2dvd : p.2 ∣ r := by
        refine ⟨p.1, ?_⟩
        rw [mul_comm, hprod]
      have hp1_eq : p.1 = r / p.2 := by
        rw [← hprod]
        simp [hp2pos]
      constructor
      · exact Nat.mem_divisors.mpr ⟨hp2dvd, hr_ne⟩
      · constructor
        · exact hpcond.1
        · simpa [← hp1_eq] using hpcond.2
    · intro q hq
      simp only [Finset.mem_filter] at hq ⊢
      rcases hq with ⟨hqdivmem, hqcond⟩
      have hqdiv : q ∣ r := (Nat.mem_divisors.mp hqdivmem).1
      have hr_ne : r ≠ 0 := (Nat.mem_divisors.mp hqdivmem).2
      have hprod : (r / q) * q = r := Nat.div_mul_cancel hqdiv
      have hqle : q ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr_ne) hqdiv
      have hdivle : r / q ≤ r := Nat.div_le_self r q
      have hr_lt : r < ⌈X⌉₊ + 1 := by simpa [s, Finset.mem_range] using hrmem
      have hqmems : q ∈ s := by simp only [s, Finset.mem_range]; omega
      have hdivmems : r / q ∈ s := by simp only [s, Finset.mem_range]; omega
      constructor
      · constructor
        · exact Finset.mem_product.mpr ⟨hdivmems, hqmems⟩
        · exact hprod
      · exact hqcond
    · intro p hp
      simp only [Finset.mem_filter] at hp
      rcases hp with ⟨hpfiber, hpcond⟩
      have hprod : p.1 * p.2 = r := hpfiber.2
      have hp2pos : 0 < p.2 := by omega
      have hp1_eq : r / p.2 = p.1 := by rw [← hprod]; simp [hp2pos]
      ext
      · exact hp1_eq
      · rfl
    · intro q hq
      rfl
    · intro p hp
      rfl
  have hfiber_high (r : ℕ) (hrmem : r ∈ s) (hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X) :
      (∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r), pairTerm p) =
        coeff r * (∑ q ∈ r.divisors,
          if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0) := by
    calc
      (∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r), pairTerm p)
          = ∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r),
              if 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ) then coeff r * ArithmeticFunction.vonMangoldt p.2 else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            exact hpair_fiber r hrint p hp
      _ = ∑ p ∈ ((s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r)).filter
              (fun p : ℕ × ℕ => 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ)),
              coeff r * ArithmeticFunction.vonMangoldt p.2 := by
            exact (Finset.sum_filter (s := (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r))
              (p := fun p : ℕ × ℕ => 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ))
              (f := fun p : ℕ × ℕ => coeff r * ArithmeticFunction.vonMangoldt p.2)).symm
      _ = ∑ q ∈ r.divisors.filter (fun q : ℕ => 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ)),
              coeff r * ArithmeticFunction.vonMangoldt q := hbij_sum r hrmem hrint
      _ = coeff r * (∑ q ∈ r.divisors,
          if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0) := by
            rw [Finset.mul_sum]
            simpa [mul_ite] using
              (Finset.sum_filter (s := r.divisors)
                (p := fun q : ℕ => 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ))
                (f := fun q : ℕ => coeff r * ArithmeticFunction.vonMangoldt q))
  have hfiber_zero (r : ℕ) (hrnot : ¬(x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X)) :
      (∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r), pairTerm p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hprod : p.1 * p.2 = r := (Finset.mem_filter.mp hp).2
    by_cases houter : x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X
    · by_cases hinner : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
      · have hp2_ge_one : 1 ≤ p.2 := by omega
        have hp1_le_prod : p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right p.1 hp2_ge_one
        have hxle_r : x ≤ (r : ℝ) := by
          have : (p.1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by exact_mod_cast hp1_le_prod
          rw [hprod] at this
          exact le_trans houter.1 this
        have hrleX : (r : ℝ) ≤ X := by simpa [hprod] using hinner.2
        exact False.elim (hrnot ⟨hxle_r, hrleX⟩)
      · have hinner' : ¬(2 ≤ p.2 ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X) := by
          intro h
          apply hinner
          exact ⟨h.1, by simpa [Nat.cast_mul] using h.2⟩
        simp [pairTerm, houter, hinner, hinner', Nat.cast_mul]
    · simp [pairTerm, houter]
  have hpair_zero_notmem (p : ℕ × ℕ) (hp : p ∈ s.product s)
      (hprodmem : ¬ p.1 * p.2 ∈ s) : pairTerm p = 0 := by
    by_cases houter : x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X
    · by_cases hinner : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
      · apply False.elim
        apply hprodmem
        simp only [s, Finset.mem_range]
        have hleceil : p.1 * p.2 ≤ ⌈X⌉₊ := by
          exact_mod_cast (le_trans hinner.2 (Nat.le_ceil X))
        omega
      · have hinner' : ¬(2 ≤ p.2 ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X) := by
          intro h
          apply hinner
          exact ⟨h.1, by simpa [Nat.cast_mul] using h.2⟩
        simp [pairTerm, houter, hinner, hinner', Nat.cast_mul]
    · simp [pairTerm, houter]
  have hpair_sum :
      (∑ p ∈ s.product s, pairTerm p) =
        ∑ r ∈ s,
          if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
            coeff r * (∑ q ∈ r.divisors,
              if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0)
          else 0 := by
    calc
      (∑ p ∈ s.product s, pairTerm p)
          = ∑ p ∈ s.product s, if p.1 * p.2 ∈ s then pairTerm p else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            by_cases hprodmem : p.1 * p.2 ∈ s
            · simp [hprodmem]
            · rw [if_neg hprodmem, hpair_zero_notmem p hp hprodmem]
      _ = ∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 ∈ s), pairTerm p := by
            exact (Finset.sum_filter (s := s.product s)
              (p := fun p : ℕ × ℕ => p.1 * p.2 ∈ s) (f := pairTerm)).symm
      _ = ∑ r ∈ s, ∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r),
              pairTerm p := by
            exact (Finset.sum_fiberwise_eq_sum_filter (s.product s) s
              (fun p : ℕ × ℕ => p.1 * p.2) pairTerm).symm
      _ = ∑ r ∈ s,
          if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
            coeff r * (∑ q ∈ r.divisors,
              if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro r hrmem
            by_cases hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
            · rw [if_pos hrint, hfiber_high r hrmem hrint]
            · rw [if_neg hrint, hfiber_zero r hrint]
  have hfinal_point (r : ℕ) (hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X) :
      coeff r * (∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q) -
        coeff r * (∑ q ∈ r.divisors,
          if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0) =
        coeff r * (∑ q ∈ r.divisors,
          if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0) := by
    have hdiv_split :
        (∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q) -
          (∑ q ∈ r.divisors,
            if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0) =
          ∑ q ∈ r.divisors,
            if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hlt : ((r / q : ℕ) : ℝ) < x
      · have hnle : ¬ x ≤ ((r / q : ℕ) : ℝ) := not_le_of_gt hlt
        simp [hlt, hnle]
      · have hge : x ≤ ((r / q : ℕ) : ℝ) := le_of_not_gt hlt
        by_cases hq2 : 2 ≤ q
        · simp [hlt, hge, hq2]
        · have hqpos : 0 < q := Nat.pos_of_mem_divisors hq
          have hqeq : q = 1 := by omega
          simp [hlt, hge, hq2, hqeq]
    rw [← mul_sub, hdiv_split]
  rw [hleft_expand, hright, hbase_sum, hpair_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hrmem
  by_cases hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
  · rw [if_pos hrint, if_pos hrint, if_pos hrint]
    exact hfinal_point r hrint
  · rw [if_neg hrint, if_neg hrint, if_neg hrint]
    ring

@[blueprint "lem:cut-capacity-le-tail-majorant"
  (statement := /-- For every $x\geq 2$ and every real $X$, the finite cut
  capacity is bounded above by the reindexed tail majorant depending only on
  $x$. -/)
  (proof := /-- It suffices to bound each finite partial sum in
  \cref{def:cut-capacity}.  For every contributing divisor $q\mid r$, put
  $n=r/q$. Then $n<x$, and the condition $r\geq x$ gives $q\geq x/n$; together
  with the non-triviality forced by $r\geq x>n$, this gives
  $q\geq\max\{2,x/n\}$.  The summand is therefore the corresponding
  $n^{-1}$ multiple of the tail term from \cref{def:mangoldt-tail-term}.  Thus
  the finite partial sum embeds into a finite sum over pairs $(n,q)$ with
  $1\leq n<x$.  For each such $n$,
  \cref{lem:mangoldt-tail-finite-sum-le} bounds the finite $q$-sum by the full
  tail in \cref{def:mangoldt-tail-sum}.  Summing over the finitely many
  admissible $n$ gives the corresponding finite form of
  \cref{def:tail-majorant}, and hence the desired t-sum inequality. -/)
  (title := /-- Reindexing the cut capacity -/)
  (latexEnv := "lemma")]
lemma cut_capacity_le_tail_majorant (x X : ℝ) (hx : 2 ≤ x) :
    cut_capacity x X ≤ tail_majorant x := by
  rw [cut_capacity]
  apply tsum_le_of_sum_le'
  · rw [tail_majorant]
    apply tsum_nonneg
    intro n
    split_ifs with hn
    · apply mul_nonneg
      · positivity
      · rw [mangoldt_tail_sum]
        apply tsum_nonneg
        intro q
        split_ifs
        · rw [mangoldt_tail_term]
          exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
        · norm_num
    · norm_num
  · intro s
    let M : ℕ := ⌈X⌉₊ + 1
    let ns : Finset ℕ := (Finset.range ⌈x⌉₊).filter (fun n => 1 ≤ n ∧ (n : ℝ) < x)
    let qs : Finset ℕ := Finset.range M
    let pairs : Finset (ℕ × ℕ) := ns.product qs
    let pairTerm : ℕ × ℕ → ℝ := fun p =>
      (1 / (p.1 : ℝ)) *
        (if max (2 : ℝ) (x / (p.1 : ℝ)) ≤ (p.2 : ℝ) then
          mangoldt_tail_term p.1 p.2 else 0)
    have hpair_nonneg : ∀ p, 0 ≤ pairTerm p := by
      intro p
      simp only [pairTerm]
      apply mul_nonneg
      · positivity
      · split_ifs
        · rw [mangoldt_tail_term]
          exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
        · norm_num
    have hD_sum (r : ℕ) :
        (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
            (∑ q ∈ r.divisors,
              if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0) =
          ∑ q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x),
            (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
              ArithmeticFunction.vonMangoldt q := by
      rw [Finset.mul_sum]
      simpa [mul_ite] using
        (Finset.sum_filter (s := r.divisors)
          (p := fun q : ℕ => ((r / q : ℕ) : ℝ) < x)
          (f := fun q : ℕ =>
            (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
              ArithmeticFunction.vonMangoldt q)).symm
    have hterm (r q : ℕ) (hrx : x ≤ (r : ℝ))
        (hq : q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x)) :
        (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
            ArithmeticFunction.vonMangoldt q = pairTerm (r / q, q) := by
      have hqdiv : q ∣ r := (Nat.mem_divisors.mp (Finset.mem_filter.mp hq).1).1
      have hqpos : 0 < q := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hq).1
      have hprod : (r / q) * q = r := Nat.div_mul_cancel hqdiv
      have hcast : (((r / q) * q : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast hprod
      have hnlt : ((r / q : ℕ) : ℝ) < x := (Finset.mem_filter.mp hq).2
      have hrpos : 0 < r := by
        have : (0 : ℝ) < (r : ℝ) := by linarith
        exact_mod_cast this
      have hqle : q ≤ r := Nat.le_of_dvd hrpos hqdiv
      have hnpos : 0 < r / q := Nat.div_pos hqle hqpos
      have hqtwo : (2 : ℝ) ≤ (q : ℝ) := by
        by_contra hnot
        have hq_lt_two : q < 2 := by exact_mod_cast lt_of_not_ge hnot
        have hq_le_one : q ≤ 1 := Nat.lt_succ_iff.mp hq_lt_two
        have hq_eq_one : q = 1 := Nat.le_antisymm hq_le_one hqpos
        have hr_eq : r / q = r := by simp [hq_eq_one]
        rw [hr_eq] at hnlt
        linarith
      have hxdiv : x / ((r / q : ℕ) : ℝ) ≤ (q : ℝ) := by
        have hnpos_real : 0 < ((r / q : ℕ) : ℝ) := by exact_mod_cast hnpos
        rw [div_le_iff₀ hnpos_real]
        calc
          x ≤ (r : ℝ) := hrx
          _ = (q : ℝ) * ((r / q : ℕ) : ℝ) := by
            rw [← hcast]
            simp [Nat.cast_mul, mul_comm]
      have hthresh : max (2 : ℝ) (x / ((r / q : ℕ) : ℝ)) ≤ (q : ℝ) :=
        max_le hqtwo hxdiv
      simp only [pairTerm]
      rw [if_pos hthresh, mangoldt_tail_term]
      rw [← hcast]
      simp only [Nat.cast_mul]
      ring_nf
    have hmem_pair (r q : ℕ) (hr : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X)
        (hq : q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x)) :
        (r / q, q) ∈ pairs := by
      have hqdiv : q ∣ r := (Nat.mem_divisors.mp (Finset.mem_filter.mp hq).1).1
      have hqpos : 0 < q := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hq).1
      have hnlt : ((r / q : ℕ) : ℝ) < x := (Finset.mem_filter.mp hq).2
      have hrpos : 0 < r := by
        have : (0 : ℝ) < (r : ℝ) := by linarith
        exact_mod_cast this
      have hqle : q ≤ r := Nat.le_of_dvd hrpos hqdiv
      have hnpos : 0 < r / q := Nat.div_pos hqle hqpos
      have hnone : 1 ≤ r / q := Nat.succ_le_of_lt hnpos
      have hnltceil : r / q < ⌈x⌉₊ := by
        exact_mod_cast (lt_of_lt_of_le hnlt (Nat.le_ceil x))
      have hq_le_X : (q : ℝ) ≤ X := by
        have hqr : (q : ℝ) ≤ (r : ℝ) := by exact_mod_cast hqle
        linarith
      have hq_le_ceil : q ≤ ⌈X⌉₊ := by
        exact_mod_cast (le_trans hq_le_X (Nat.le_ceil X))
      have hq_lt_M : q < M := by
        dsimp [M]
        omega
      simp [pairs, ns, qs, hnltceil, hnone, hnlt, hq_lt_M]
    have hper (r : ℕ) :
        (if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
          1 / ((r : ℝ) * Real.log (r : ℝ) ^ 2) *
            ∑ q ∈ r.divisors,
              if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0
        else 0) ≤
          ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p := by
      by_cases hr : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
      · rw [if_pos hr]
        calc
          1 / ((r : ℝ) * Real.log (r : ℝ) ^ 2) *
              (∑ q ∈ r.divisors,
                if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0)
              = (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
                  (∑ q ∈ r.divisors,
                    if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0) := by
                ring_nf
          _ = ∑ q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x),
                (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
                  ArithmeticFunction.vonMangoldt q := hD_sum r
          _ = ∑ q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x),
                pairTerm (r / q, q) := by
              apply Finset.sum_congr rfl
              intro q hq
              exact hterm r q hr.1 hq
          _ = ∑ p ∈ (r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x)).image
                (fun q => (r / q, q)), pairTerm p := by
              rw [Finset.sum_image]
              intro a _ b _ hab
              exact Prod.ext_iff.mp hab |>.2
          _ ≤ ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro p hp
                rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
                have hqdiv : q ∣ r := (Nat.mem_divisors.mp (Finset.mem_filter.mp hq).1).1
                have hprod : (r / q) * q = r := Nat.div_mul_cancel hqdiv
                simp [hmem_pair r q hr hq, hprod]
              · intro p _ _
                exact hpair_nonneg p
      · rw [if_neg hr]
        exact Finset.sum_nonneg (fun p _ => hpair_nonneg p)
    have hsum_le :
        (∑ i ∈ s,
          if x ≤ (i : ℝ) ∧ (i : ℝ) ≤ X then
            1 / ((i : ℝ) * Real.log (i : ℝ) ^ 2) *
              ∑ q ∈ i.divisors,
                if ((i / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0
          else 0) ≤ ∑ p ∈ pairs, pairTerm p := by
      calc
        (∑ i ∈ s,
          if x ≤ (i : ℝ) ∧ (i : ℝ) ≤ X then
            1 / ((i : ℝ) * Real.log (i : ℝ) ^ 2) *
              ∑ q ∈ i.divisors,
                if ((i / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0
          else 0)
            ≤ ∑ i ∈ s, ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = i), pairTerm p := by
              apply Finset.sum_le_sum
              intro i _
              exact hper i
        _ = ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ s), pairTerm p := by
          exact Finset.sum_fiberwise_eq_sum_filter pairs s
            (fun p : ℕ × ℕ => p.1 * p.2) pairTerm
        _ ≤ ∑ p ∈ pairs, pairTerm p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            exact (Finset.mem_filter.mp hp).1
          · intro p _ _
            exact hpair_nonneg p
    have htail_eq : tail_majorant x =
        ∑ n ∈ ns,
          if 1 ≤ n ∧ (n : ℝ) < x then
            (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
          else 0 := by
      rw [tail_majorant]
      exact tsum_eq_sum (s := ns) (fun n hn => by
        split_ifs with h
        · exfalso
          apply hn
          simp [ns]
          constructor
          · have hltceil : n < ⌈x⌉₊ := by
              exact_mod_cast (lt_of_lt_of_le h.2 (Nat.le_ceil x))
            simpa using hltceil
          · exact h
        · rfl)
    have hfinite_tail_le : (∑ p ∈ pairs, pairTerm p) ≤ tail_majorant x := by
      rw [htail_eq]
      change (∑ p ∈ ns ×ˢ qs, pairTerm p) ≤
        ∑ n ∈ ns,
          if 1 ≤ n ∧ (n : ℝ) < x then
            (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
          else 0
      rw [Finset.sum_product]
      apply Finset.sum_le_sum
      intro n hn
      have hnmem : n < ⌈x⌉₊ ∧ 1 ≤ n ∧ (n : ℝ) < x := by simpa [ns] using hn
      have hnprop : 1 ≤ n ∧ (n : ℝ) < x := hnmem.2
      rw [if_pos hnprop]
      simp only [pairTerm]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (mangoldt_tail_finite_sum_le n hnprop.1 (max (2 : ℝ) (x / (n : ℝ)))
          (le_max_left _ _) qs) (by positivity)
    exact hsum_le.trans hfinite_tail_le

@[blueprint "lem:tail-majorant-bound"
  (statement := /-- There is a real constant $C\geq 0$ such that, for every
  real number $x\geq 2$, the reindexed tail majorant is at most
  $1+C/\log x$. -/)
  (proof := /-- Let $D\geq 0$ be the constant supplied by
  \cref{lem:mangoldt-tail-upper-bound}, set $K=1+\log 2$, and fix a real
  number $x\geq 2$ with $L=\log x$. By \cref{def:tail-majorant}, only the
  integers $1\leq n<x$ contribute.  For such an $n$, put
  $y=\max(2,x/n)$. Then $y\geq 2$ and $ny\geq x$, so
  \cref{lem:mangoldt-tail-upper-bound} gives
  $\sum_{q\geq y}\Lambda(q)/(q\log^2(nq))\leq L^{-1}+D L^{-2}$. Hence the
  majorant is at most $(L^{-1}+D L^{-2})\sum_{1\leq n\leq \lceil x\rceil}1/n$.
  Since $\lceil x\rceil\leq 2x$, the harmonic estimate
  $\sum_{1\leq n\leq \lceil x\rceil}1/n\leq L+K$ applies. Therefore the
  majorant is at most
  $1+(K+D)/L+KD/L^2$.  As $L\geq \log 2$, the final term is at most
  $(KD/\log 2)/L$. Taking $C=K+D+KD/\log 2$ proves the asserted bound. -/)
  (title := /-- Bounding the reindexed tail majorant -/)
  (latexEnv := "lemma")]
lemma tail_majorant_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x -> tail_majorant x ≤ 1 + C / Real.log x := by
  classical
  obtain ⟨D, hD_nonneg, hD_bound⟩ := mangoldt_tail_upper_bound
  let K : ℝ := 1 + Real.log (2 : ℝ)
  let C : ℝ := K + D + K * D / Real.log (2 : ℝ)
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_nonneg, ?_⟩
  intro x hx
  let N : ℕ := ⌈x⌉₊
  let L : ℝ := Real.log x
  let A : ℝ := 1 / L + D / L ^ 2
  have hx_pos : 0 < x := by linarith
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith)
  have hlog2_le_L : Real.log (2 : ℝ) ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) hx
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hfinite : tail_majorant x =
      ∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then
          (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
        else 0 := by
    unfold tail_majorant
    dsimp [N]
    refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
      (s := Finset.range ⌈x⌉₊)
      (f := fun n : ℕ =>
        if 1 ≤ n ∧ (n : ℝ) < x then
          (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
        else 0) ?_
    intro n hn
    have hn_not_lt_x : ¬ (n : ℝ) < x := by
      intro hnx
      have hn_lt_ceil : n < ⌈x⌉₊ := by
        by_contra hnot
        have hceil_le_n : ⌈x⌉₊ ≤ n := le_of_not_gt hnot
        have hx_le_n : x ≤ (n : ℝ) := by
          exact (Nat.le_ceil x).trans (Nat.cast_le.mpr hceil_le_n)
        exact (not_lt_of_ge hx_le_n) hnx
      exact hn (Finset.mem_range.mpr hn_lt_ceil)
    simp [hn_not_lt_x]
  have hterm_le : ∀ n : ℕ,
      (if 1 ≤ n ∧ (n : ℝ) < x then
        (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
      else 0) ≤
      (if 1 ≤ n ∧ (n : ℝ) < x then (1 / (n : ℝ)) * A else 0) := by
    intro n
    by_cases hn : 1 ≤ n ∧ (n : ℝ) < x
    · have hn_pos_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn.1
      have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
      let y : ℝ := max (2 : ℝ) (x / (n : ℝ))
      have hy : 2 ≤ y := by
        dsimp [y]
        exact le_max_left _ _
      have hxy : x ≤ (n : ℝ) * y := by
        have hdiv_le : x / (n : ℝ) ≤ y := by
          dsimp [y]
          exact le_max_right _ _
        calc
          x = (n : ℝ) * (x / (n : ℝ)) := by
            field_simp [hn_pos.ne']
          _ ≤ (n : ℝ) * y := mul_le_mul_of_nonneg_left hdiv_le (le_of_lt hn_pos)
      have hlog_ge : L ≤ Real.log ((n : ℝ) * y) := by
        dsimp [L]
        exact Real.log_le_log hx_pos hxy
      have hlog_pos : 0 < Real.log ((n : ℝ) * y) := hL_pos.trans_le hlog_ge
      have htail := (hD_bound n hn.1 y hy).2
      have hone : 1 / Real.log ((n : ℝ) * y) ≤ 1 / L := by
        exact one_div_le_one_div_of_le hL_pos hlog_ge
      have hsquare : D / (Real.log ((n : ℝ) * y)) ^ 2 ≤ D / L ^ 2 := by
        have hsquares : L ^ 2 ≤ (Real.log ((n : ℝ) * y)) ^ 2 := by
          nlinarith [hlog_ge, le_of_lt hL_pos, le_of_lt hlog_pos]
        exact div_le_div_of_nonneg_left hD_nonneg (sq_pos_of_pos hL_pos) hsquares
      have htail_A : mangoldt_tail_sum n y ≤ A := by
        calc
          mangoldt_tail_sum n y ≤
              1 / Real.log ((n : ℝ) * y) + D / (Real.log ((n : ℝ) * y)) ^ 2 := htail
          _ ≤ 1 / L + D / L ^ 2 := add_le_add hone hsquare
          _ = A := by rfl
      have hmul := mul_le_mul_of_nonneg_left htail_A (by positivity : 0 ≤ 1 / (n : ℝ))
      simpa [hn, y, A] using hmul
    · simp [hn]
  have hsum_A :
      (∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then (1 / (n : ℝ)) * A else 0) ≤
        ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) * A := by
    calc
      (∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then (1 / (n : ℝ)) * A else 0) =
          ∑ n ∈ (Finset.range N).filter (fun n : ℕ => 1 ≤ n ∧ (n : ℝ) < x),
            (1 / (n : ℝ)) * A := by
            rw [Finset.sum_filter]
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) * A := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn
          exact Finset.mem_Icc.mpr ⟨hn.2.1, Nat.le_of_lt hn.1⟩
        · intro n hnI hnnot
          positivity
  have hrecip_eq_harm :
      (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ))) = (harmonic N : ℝ) := by
    simpa [one_div, harmonic_eq_sum_Icc]
  have htail_le_HA : tail_majorant x ≤ (harmonic N : ℝ) * A := by
    calc
      tail_majorant x = ∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then
          (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
        else 0 := hfinite
      _ ≤ ∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then (1 / (n : ℝ)) * A else 0 := by
          exact Finset.sum_le_sum (by intro n hn; exact hterm_le n)
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) * A := hsum_A
      _ = (harmonic N : ℝ) * A := by
        rw [← Finset.sum_mul, hrecip_eq_harm]
  have hN_lt_add_one : (N : ℝ) < x + 1 := by
    dsimp [N]
    exact Nat.ceil_lt_add_one (by linarith : 0 ≤ x)
  have hN_le_two_x : (N : ℝ) ≤ 2 * x := by
    nlinarith [hN_lt_add_one, hx]
  have hN_pos : 0 < (N : ℝ) := by
    have hx_le_N : x ≤ (N : ℝ) := by
      dsimp [N]
      exact Nat.le_ceil x
    linarith
  have hlogN_le : Real.log (N : ℝ) ≤ Real.log (2 : ℝ) + L := by
    have hlog_le := Real.log_le_log hN_pos hN_le_two_x
    have hlog_mul : Real.log (2 * x) = Real.log (2 : ℝ) + Real.log x := by
      rw [Real.log_mul] <;> positivity
    simpa [L, hlog_mul] using hlog_le
  have hH_le : (harmonic N : ℝ) ≤ L + K := by
    have hh := harmonic_le_one_add_log N
    calc
      (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := hh
      _ ≤ 1 + (Real.log (2 : ℝ) + L) := by linarith
      _ = L + K := by
        dsimp [K]
        ring
  have htail_le_main : tail_majorant x ≤ (L + K) * A :=
    le_trans htail_le_HA (mul_le_mul_of_nonneg_right hH_le hA_nonneg)
  have halg : (L + K) * A ≤ 1 + C / L := by
    have hKD_nonneg : 0 ≤ K * D := by positivity
    have hKD_div : K * D / L ≤ K * D / Real.log (2 : ℝ) := by
      exact div_le_div_of_nonneg_left hKD_nonneg hlog2_pos hlog2_le_L
    have hKD_sq : K * D / L ^ 2 ≤ (K * D / Real.log (2 : ℝ)) / L := by
      calc
        K * D / L ^ 2 = (K * D / L) / L := by
          field_simp [hL_pos.ne']
        _ ≤ (K * D / Real.log (2 : ℝ)) / L :=
          div_le_div_of_nonneg_right hKD_div (le_of_lt hL_pos)
    have hdecomp : (L + K) * A = 1 + (K + D) / L + K * D / L ^ 2 := by
      dsimp [A]
      field_simp [hL_pos.ne']
      ring
    have htarget : 1 + (K + D) / L + K * D / L ^ 2 ≤
        1 + (K + D) / L + (K * D / Real.log (2 : ℝ)) / L := by
      linarith
    have hcombine : 1 + (K + D) / L + (K * D / Real.log (2 : ℝ)) / L =
        1 + C / L := by
      dsimp [C]
      field_simp [hL_pos.ne']
      ring
    calc
      (L + K) * A = 1 + (K + D) / L + K * D / L ^ 2 := hdecomp
      _ ≤ 1 + (K + D) / L + (K * D / Real.log (2 : ℝ)) / L := htarget
      _ = 1 + C / L := hcombine
  exact le_trans htail_le_main halg

@[blueprint "lem:finite-truncation-principle"
  (statement := /-- If there is a real constant $C\geq 0$ such that every
  primitive set supported in a finite interval $[x,X]$ with $2\leq x\leq X$
  satisfies $f(A)\leq 1+C/\log x$, then there is a real constant $C\geq 0$ such
  that every primitive set supported in $[x,\infty)$ with $x\geq 2$ satisfies
  $f(A)\leq 1+C/\log x$. -/)
  (proof := /-- Unpack \cref{def:erdos1196-finite-bound}.  Fix $x\geq 2$ and
  a primitive set $A$ supported above $x$.  For each natural number $N$, put
  $B=A\cap \{0,\ldots,N-1\}$.  By \cref{def:primitive-set}, $B$ is primitive,
  and by \cref{def:supported-above,def:supported-in-interval} it is supported
  in $[x,\max\{x,N\}]$.  The finite hypothesis therefore bounds
  $f(B)$ by $1+C/\log x$.  By \cref{def:erdos-sum,def:erdos-weight}, this is
  exactly the $N$th finite partial sum of the nonnegative series defining
  $f(A)$.  Since all partial sums of this nonnegative real series are bounded by
  $1+C/\log x$, the standard bounded-partial-sums theorem for nonnegative real
  series gives $f(A)\leq 1+C/\log x$.  Together with the same nonnegative
  constant $C$, this is precisely \cref{def:erdos1196-bound}. -/)
  (title := /-- Removing the finite truncation -/)
  (latexEnv := "lemma")]
lemma finite_truncation_principle :
    (∃ C : ℝ, erdos1196_finite_bound C) -> ∃ C : ℝ, erdos1196_bound C := by
  rintro ⟨C, hC_nonneg, hfinite⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro x hx A hA_primitive hA_supported
  let f : ℕ → ℝ := fun n => A.indicator erdos_weight n
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    by_cases hnA : n ∈ A
    · have h2n : (2 : ℝ) ≤ (n : ℝ) := le_trans hx (hA_supported n hnA)
      have hn_pos : 0 < (n : ℝ) := by linarith
      have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
      simp only [f, Set.indicator_of_mem hnA]
      unfold erdos_weight
      positivity
    · simp [f, Set.indicator_of_notMem hnA]
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, f n ≤ 1 + C / Real.log x := by
    intro N
    let B : Set ℕ := A ∩ (Finset.range N : Set ℕ)
    have hB_primitive : primitive_set B := by
      exact hA_primitive.subset (by intro n hn; exact hn.1)
    have hB_supported : supported_in_interval B x (max x (N : ℝ)) := by
      intro n hn
      constructor
      · exact hA_supported n hn.1
      · exact le_trans (Nat.cast_le.mpr (Nat.le_of_lt (Finset.mem_range.mp hn.2)))
          (le_max_right x (N : ℝ))
    have hB_sum : erdos_sum B = ∑ n ∈ Finset.range N, f n := by
      unfold erdos_sum
      rw [tsum_eq_sum]
      · refine Finset.sum_congr rfl ?_
        intro n hn
        by_cases hnA : n ∈ A
        · have hnB : n ∈ B := ⟨hnA, hn⟩
          simp [f, Set.indicator_of_mem hnB, Set.indicator_of_mem hnA]
        · have hnB : n ∉ B := by
            intro h
            exact hnA h.1
          simp [f, Set.indicator_of_notMem hnB, Set.indicator_of_notMem hnA]
      · intro n hn
        have hn_not_lt : ¬ n < N := by
          intro hnlt
          exact hn (Finset.mem_range.mpr hnlt)
        have hnB : n ∉ B := by
          intro h
          exact hn_not_lt (Finset.mem_range.mp h.2)
        simp [Set.indicator_of_notMem hnB]
    have hB_bound := hfinite x (max x (N : ℝ)) hx (le_max_left x (N : ℝ)) B
      hB_primitive hB_supported
    simpa [hB_sum] using hB_bound
  have hf_summable : Summable f := summable_of_sum_range_le hf_nonneg hpartial
  have hsum_le : (∑' n : ℕ, f n) ≤ 1 + C / Real.log x :=
    hf_summable.tsum_le_of_sum_range_le hpartial
  simpa [erdos_sum, f] using hsum_le

@[blueprint "lem:inv-mul-log-sq-sum-le-div-log"
  (statement := /-- For every real $x\geq 2$, real $X$, and finite set
  $R\subseteq\mathbb{N}$ contained in $[x,X]$, one has
  $\sum_{n\in R}(n\log^2 n)^{-1}\leq 2/\log x$. -/)
  (proof := /-- Embed $R$ into the integer interval $[\lceil x\rceil, \lceil X\rceil+1)$.
  The first term $n=\lceil x\rceil$ is bounded by $1/\log x$ since
  $2\log 2\geq 1$.  For every subsequent $n\geq \lceil x\rceil + 1$, the
  elementary inequality $1/n\leq \log n - \log(n-1)$ bounds
  $(n\log^2 n)^{-1}\leq (\log(n-1))^{-1} - (\log n)^{-1}$, which telescopes to
  at most $1/\log\lceil x\rceil \leq 1/\log x$. -/)
  (title := /-- Elementary telescoping bound for $\sum (n\log^2 n)^{-1}$ -/)
  (latexEnv := "lemma")]
lemma inv_mul_log_sq_sum_le_div_log (x X : ℝ) (hx : 2 ≤ x) (R : Finset ℕ)
    (hR : ∀ n ∈ R, x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) :
    (∑ n ∈ R, 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) ≤ 2 / Real.log x := by
  let k : ℕ := ⌈x⌉₊
  let M : ℕ := ⌈X⌉₊ + 1
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hxk : x ≤ (k : ℝ) := Nat.le_ceil x
  have hk_two_real : (2 : ℝ) ≤ (k : ℝ) := le_trans hx hxk
  have hk_two : 2 ≤ k := by exact_mod_cast hk_two_real
  have hR_sub : R ⊆ Finset.Ico k M := by
    intro n hn
    have hn_int := hR n hn
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.ceil_le.mpr hn_int.1
    · have hn_le : n ≤ ⌈X⌉₊ := by
        exact_mod_cast (le_trans hn_int.2 (Nat.le_ceil X))
      omega
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
    intro n
    positivity
  have hsum_le_ico :
      (∑ n ∈ R, 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) ≤
        ∑ n ∈ Finset.Ico k M, 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hR_sub (fun n _ _ => hterm_nonneg n)
  by_cases hMk : M ≤ k
  · rw [Finset.Ico_eq_empty_of_le hMk, Finset.sum_empty] at hsum_le_ico
    exact le_trans hsum_le_ico (by positivity)
  · have hkM : k < M := not_le.mp hMk
    have hsplit :
        (∑ n ∈ Finset.Ico k M, 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) =
          1 / ((k : ℝ) * (Real.log (k : ℝ)) ^ 2) +
            ∑ n ∈ Finset.Ico (k + 1) M, 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
      exact Finset.sum_eq_sum_Ico_succ_bot hkM _
    have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlogk_ge_logx : Real.log x ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by linarith) hxk
    have hlogk_ge_log2 : Real.log (2 : ℝ) ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by norm_num) hk_two_real
    have hlogk_pos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le hlogx_pos hlogk_ge_logx
    have h2log2_ge_one : (1 : ℝ) ≤ 2 * Real.log (2 : ℝ) := by
      have h := Real.log_two_gt_d9
      linarith
    have hfirst_le : 1 / ((k : ℝ) * (Real.log (k : ℝ)) ^ 2) ≤ 1 / Real.log x := by
      apply one_div_le_one_div_of_le hlogx_pos
      have hklogk : (1 : ℝ) ≤ (k : ℝ) * Real.log (k : ℝ) := by
        calc
          (1 : ℝ) ≤ 2 * Real.log (2 : ℝ) := h2log2_ge_one
          _ ≤ (k : ℝ) * Real.log (k : ℝ) := by
            exact mul_le_mul hk_two_real hlogk_ge_log2 hlog2_pos.le (by linarith)
      calc
        Real.log x ≤ 1 * Real.log (k : ℝ) := by linarith
        _ ≤ ((k : ℝ) * Real.log (k : ℝ)) * Real.log (k : ℝ) := by
          exact mul_le_mul_of_nonneg_right hklogk hlogk_pos.le
        _ = (k : ℝ) * (Real.log (k : ℝ)) ^ 2 := by ring
    let g : ℕ → ℝ := fun m => 1 / Real.log (m : ℝ)
    have htail_le :
        (∑ n ∈ Finset.Ico (k + 1) M, 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) ≤
          ∑ n ∈ Finset.Ico (k + 1) M, (g (n - 1) - g n) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Finset.mem_Ico] at hn
      have hn_ge3 : 3 ≤ n := by omega
      have hn_pred_ge2 : 2 ≤ n - 1 := by omega
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hn_pred_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < n - 1)
      have hn_pred_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        simp
      have hlog_pred_pos : 0 < Real.log ((n - 1 : ℕ) : ℝ) := by
        apply Real.log_pos
        exact_mod_cast (by omega : 1 < n - 1)
      have hlog_pred_le : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log hn_pred_pos (by exact_mod_cast (by omega : n - 1 ≤ n))
      have hlog_n_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le hlog_pred_pos hlog_pred_le
      have hinv_le_logdiff :
          1 / (n : ℝ) ≤ Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) := by
        have hratio_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) / (n : ℝ) :=
          div_pos hn_pred_pos hn_pos
        have hlog_ineq := Real.log_le_sub_one_of_pos hratio_pos
        rw [Real.log_div hn_pred_pos.ne' hn_pos.ne'] at hlog_ineq
        have hsub : ((n - 1 : ℕ) : ℝ) / (n : ℝ) - 1 = -(1 / (n : ℝ)) := by
          rw [hn_pred_cast]
          field_simp [hn_pos.ne']
          ring
        linarith
      have hdenom_pos : 0 < Real.log (n : ℝ) * Real.log ((n - 1 : ℕ) : ℝ) :=
        mul_pos hlog_n_pos hlog_pred_pos
      have hsq_le :
          1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) ≤
            (1 / (n : ℝ)) / (Real.log (n : ℝ) * Real.log ((n - 1 : ℕ) : ℝ)) := by
        have h1 :
            (1 / (n : ℝ)) / (Real.log (n : ℝ) * Real.log ((n - 1 : ℕ) : ℝ)) =
              1 / ((n : ℝ) * (Real.log (n : ℝ) * Real.log ((n - 1 : ℕ) : ℝ))) := by
          field_simp [hn_pos.ne', hlog_n_pos.ne', hlog_pred_pos.ne']
        rw [h1]
        apply one_div_le_one_div_of_le (mul_pos hn_pos hdenom_pos)
        have h2 : Real.log (n : ℝ) * Real.log ((n - 1 : ℕ) : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
          rw [sq]
          exact mul_le_mul_of_nonneg_left hlog_pred_le hlog_n_pos.le
        exact mul_le_mul_of_nonneg_left h2 hn_pos.le
      have hdiff_eq :
          (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) /
              (Real.log (n : ℝ) * Real.log ((n - 1 : ℕ) : ℝ)) =
            g (n - 1) - g n := by
        dsimp [g]
        field_simp [hlog_n_pos.ne', hlog_pred_pos.ne']
      calc
        1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) ≤
            (1 / (n : ℝ)) / (Real.log (n : ℝ) * Real.log ((n - 1 : ℕ) : ℝ)) := hsq_le
        _ ≤ (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) /
              (Real.log (n : ℝ) * Real.log ((n - 1 : ℕ) : ℝ)) := by
          exact div_le_div_of_nonneg_right hinv_le_logdiff hdenom_pos.le
        _ = g (n - 1) - g n := hdiff_eq
    have htelescope :
        (∑ n ∈ Finset.Ico (k + 1) M, (g (n - 1) - g n)) ≤ g k := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hrewrite :
          (∑ i ∈ Finset.range (M - (k + 1)), (g (k + 1 + i - 1) - g (k + 1 + i))) =
            ∑ i ∈ Finset.range (M - (k + 1)), (g (k + i) - g (k + (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i _
        have h1 : k + 1 + i - 1 = k + i := by omega
        have h2 : k + 1 + i = k + (i + 1) := by omega
        rw [h1, h2]
      rw [hrewrite]
      have hsub := Finset.sum_range_sub' (fun i => g (k + i)) (M - (k + 1))
      rw [hsub]
      have hlast_nonneg : 0 ≤ g (k + (M - (k + 1))) := by
        dsimp [g]
        have hge2 : (2 : ℝ) ≤ ((k + (M - (k + 1)) : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 2 ≤ k + (M - (k + 1)))
        have hlp : 0 < Real.log ((k + (M - (k + 1)) : ℕ) : ℝ) :=
          Real.log_pos (by linarith)
        exact div_nonneg zero_le_one hlp.le
      simp only [Nat.add_zero]
      linarith
    have hgk_le : g k ≤ 1 / Real.log x := by
      dsimp [g]
      exact one_div_le_one_div_of_le hlogx_pos hlogk_ge_logx
    have htotal :
        (∑ n ∈ Finset.Ico k M, 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) ≤ 2 / Real.log x := by
      rw [hsplit]
      have : 1 / Real.log x + 1 / Real.log x = 2 / Real.log x := by ring
      linarith
    exact le_trans hsum_le_ico htotal

@[blueprint "lem:finite-chain-erdos-le-initial-mass"
  (statement := /-- There exists a constant $C_{\mathrm{err}}\geq 0$ such that
  for every $x\geq2$, every real $X$, and every primitive set
  $A\subseteq\mathbb N$ supported in $[x,X]$, the Erd\H{o}s sum of $A$ is at
  most the total finite initial mass $\sum_n b_{x,X}(n)$ from
  \cref{def:finite-chain-initial-mass} plus $C_{\mathrm{err}}/\log x$. -/)
  (proof := /-- Put $b(n)=b_{x,X}(n)$ as in
  \cref{def:finite-chain-initial-mass}, and let $C_{\mathrm{tail}}\geq 0$ be
  the constant from \cref{lem:mangoldt-tail-upper-bound}. First prove the lower
  bound $b(n)\geq -C_{\mathrm{tail}}/(n\log^2 n)$ for every $n$. If
  $x\leq n\leq X$, then $n\geq2$; the finite incoming sum over $q$ with
  $nq\leq X$ is bounded by $n^{-1}$ times the full tail at threshold $2$, using
  \cref{lem:mangoldt-tail-finite-sum-le}, and
  \cref{lem:mangoldt-tail-upper-bound} bounds this by
  $(n\log n)^{-1}+C_{\mathrm{tail}}/(n\log^2 n)$. Outside $[x,X]$ the mass is
  zero. By \cref{lem:finite-chain-initial-mass-sum-eq-cut-capacity}, the total
  initial mass equals the nonnegative cut capacity, so the right-hand side is
  nonnegative. It remains to bound each finite partial sum of
  \cref{def:erdos-sum}. Fix a finite set of indices $s$ and restrict to the
  finite interval $R=\{n:x\leq n\leq X\}$. Let $H(n)$ be the indicator that $n$
  is divisible by some element of $A\cap s$. For each $r\in R$, the
  contribution of $A\cap s$ at $r$ plus the $H$-weighted incoming contribution
  from factor pairs $nq=r$ is at most $H(r)\nu_0(r)$. If $r\in A\cap s$, the
  incoming term vanishes by \cref{def:primitive-set}; if $H(r)=0$, it vanishes
  by definition; otherwise it is bounded by the full von Mangoldt divisor sum,
  which is $\log r$ by \cref{lem:von-mangoldt-divisor-sum}. Summing these
  inequalities over $r\in R$ and reindexing the fibers $(n,q)$ gives the
  partial-sum bound by $\sum_{n\in R}H(n)b(n)$. Since $0\leq H(n)\leq1$ and
  $b(n)+C_{\mathrm{tail}}/(n\log^2 n)\geq0$, this is at most
  $\sum_{n\in R}b(n)+C_{\mathrm{tail}}\sum_{n\in R}(n\log^2 n)^{-1}$. Applying
  \cref{lem:inv-mul-log-sq-sum-le-div-log} bounds the error sum by
  $2C_{\mathrm{tail}}/\log x$, and
  \cref{def:supported-in-interval,def:finite-chain-initial-mass} identifies
  $\sum_{n\in R}b(n)$ with the t-sum. -/)
  (title := /-- Hitting mass bounds the finite Erd\H{o}s sum -/)
  (latexEnv := "lemma")]
lemma finite_chain_erdos_le_initial_mass :
    ∃ C_err : ℝ, 0 ≤ C_err ∧
      ∀ (A : Set ℕ) (x X : ℝ), 2 ≤ x -> primitive_set A -> supported_in_interval A x X ->
        erdos_sum A ≤ (∑' n : ℕ, finite_chain_initial_mass x X n) + C_err / Real.log x := by
  classical
  obtain ⟨C_tail, hC_tail_nonneg, htail_upper⟩ := mangoldt_tail_upper_bound
  refine ⟨2 * C_tail, by linarith, ?_⟩
  intro A x X hx hprim hsupp
  have hmass_lower : ∀ n : ℕ,
      -(C_tail / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) ≤ finite_chain_initial_mass x X n := by
    intro n
    rw [finite_chain_initial_mass]
    by_cases hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X
    · rw [if_pos hnint]
      have hn_two : 2 ≤ n := by exact_mod_cast (le_trans hx hnint.1)
      have hn_one : 1 ≤ n := by omega
      have hlog_pos : 0 < Real.log (n : ℝ) := by
        apply Real.log_pos
        exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn_two)
      have hinner_le :
          (∑' q : ℕ,
            if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
              erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                Real.log ((n * q : ℕ) : ℝ)
            else 0) ≤ (1 / (n : ℝ)) * mangoldt_tail_sum n 2 := by
        apply tsum_le_of_sum_le'
        · apply mul_nonneg
          · positivity
          · rw [mangoldt_tail_sum]
            apply tsum_nonneg
            intro q
            split_ifs
            · rw [mangoldt_tail_term]
              exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
            · norm_num
        · intro s
          have hpoint : ∀ q : ℕ,
              (if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                  Real.log ((n * q : ℕ) : ℝ)
              else 0) ≤
                (1 / (n : ℝ)) *
                  (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) := by
            intro q
            by_cases hqcond : 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X
            · rw [if_pos hqcond]
              have hqreal : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqcond.1
              rw [if_pos hqreal]
              rw [erdos_weight, mangoldt_tail_term]
              rw [Nat.cast_mul]
              ring_nf
              exact le_rfl
            · rw [if_neg hqcond]
              apply mul_nonneg
              · positivity
              · split_ifs
                · rw [mangoldt_tail_term]
                  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
                · norm_num
          calc
            (∑ q ∈ s,
              if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                  Real.log ((n * q : ℕ) : ℝ)
              else 0) ≤
                ∑ q ∈ s,
                  (1 / (n : ℝ)) *
                    (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) := by
                apply Finset.sum_le_sum
                intro q _
                exact hpoint q
            _ = (1 / (n : ℝ)) *
                  ∑ q ∈ s,
                    (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) := by
                rw [Finset.mul_sum]
            _ ≤ (1 / (n : ℝ)) * mangoldt_tail_sum n 2 := by
                exact mul_le_mul_of_nonneg_left
                  (mangoldt_tail_finite_sum_le n hn_one 2 (by norm_num) s) (by positivity)
      have hlog_2n_ge : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) * (2 : ℝ)) := by
        apply Real.log_le_log (by positivity)
        linarith
      have htail_le : mangoldt_tail_sum n 2 ≤
          1 / Real.log (n : ℝ) + C_tail / (Real.log (n : ℝ)) ^ 2 := by
        have hraw := (htail_upper n hn_one 2 (by norm_num)).2
        have h1 : 1 / Real.log ((n : ℝ) * (2 : ℝ)) ≤ 1 / Real.log (n : ℝ) :=
          one_div_le_one_div_of_le hlog_pos hlog_2n_ge
        have h2 : C_tail / (Real.log ((n : ℝ) * (2 : ℝ))) ^ 2 ≤
            C_tail / (Real.log (n : ℝ)) ^ 2 := by
          apply div_le_div_of_nonneg_left hC_tail_nonneg (sq_pos_of_pos hlog_pos)
          exact sq_le_sq' (by linarith) hlog_2n_ge
        linarith
      have hscaled_le : (1 / (n : ℝ)) * mangoldt_tail_sum n 2 ≤
          erdos_weight n + C_tail / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
        calc
          (1 / (n : ℝ)) * mangoldt_tail_sum n 2 ≤
              (1 / (n : ℝ)) * (1 / Real.log (n : ℝ) + C_tail / (Real.log (n : ℝ)) ^ 2) := by
              exact mul_le_mul_of_nonneg_left htail_le (by positivity)
          _ = erdos_weight n + C_tail / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
              rw [erdos_weight]
              ring_nf
      linarith
    · rw [if_neg hnint]
      have hnonneg : 0 ≤ C_tail / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by positivity
      linarith
  have hRHS_nonneg :
      0 ≤ (∑' n : ℕ, finite_chain_initial_mass x X n) + (2 * C_tail) / Real.log x := by
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hcut_nonneg : 0 ≤ cut_capacity x X := by
      rw [cut_capacity]
      apply tsum_nonneg
      intro r
      split_ifs
      · apply mul_nonneg (by positivity)
        apply Finset.sum_nonneg
        intro q _
        split_ifs
        · exact ArithmeticFunction.vonMangoldt_nonneg
        · norm_num
      · norm_num
    rw [finite_chain_initial_mass_sum_eq_cut_capacity x X hx]
    have hterm : 0 ≤ (2 * C_tail) / Real.log x := by positivity
    linarith
  rw [erdos_sum]
  apply tsum_le_of_sum_le'
  · exact hRHS_nonneg
  · intro s
    let M : ℕ := ⌈X⌉₊ + 1
    let R : Finset ℕ := (Finset.range M).filter (fun n => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X)
    have hb_tsum_eq :
        (∑' n : ℕ, finite_chain_initial_mass x X n) =
          ∑ n ∈ R, finite_chain_initial_mass x X n := by
      exact tsum_eq_sum (s := R) (fun n hn => by
        have hnnot : ¬ (x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) := by
          intro hnx
          apply hn
          have hn_le_ceil : n ≤ ⌈X⌉₊ := by
            exact_mod_cast (le_trans hnx.2 (Nat.le_ceil X))
          have hn_lt_M : n < M := by
            dsimp [M]
            omega
          simp [R, hn_lt_M, hnx]
        rw [finite_chain_initial_mass, if_neg hnnot])
    have hleft_eq :
        (∑ i ∈ s, A.indicator erdos_weight i) =
          ∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0 := by
      have hs_eq :
          (∑ i ∈ s, A.indicator erdos_weight i) =
            ∑ i ∈ s.filter (fun i => i ∈ A), erdos_weight i := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hiA : i ∈ A
        · simp [Set.indicator_of_mem hiA, hiA]
        · simp [Set.indicator_of_notMem hiA, hiA]
      have hR_eq :
          (∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0) =
            ∑ n ∈ R.filter (fun n => n ∈ s ∧ n ∈ A), erdos_weight n := by
        exact (Finset.sum_filter (s := R)
          (p := fun n => n ∈ s ∧ n ∈ A) (f := erdos_weight)).symm
      rw [hs_eq, hR_eq]
      symm
      apply Finset.sum_bij (fun n hn => n)
      · intro n hn
        simp only [Finset.mem_filter] at hn ⊢
        exact ⟨hn.2.1, hn.2.2⟩
      · intro a ha b hb h
        exact h
      · intro b hb
        simp only [Finset.mem_filter] at hb
        have hB := hsupp b hb.2
        have hb_le_ceil : b ≤ ⌈X⌉₊ := by
          exact_mod_cast (le_trans hB.2 (Nat.le_ceil X))
        have hb_lt_M : b < M := by
          dsimp [M]
          omega
        refine ⟨b, ?_, rfl⟩
        simp [R, hb_lt_M, hB, hb]
      · intro n hn
        rfl
    have hmass_finite (n : ℕ) (hnR : n ∈ R) :
        finite_chain_initial_mass x X n = erdos_weight n -
          ∑ q ∈ Finset.range M,
            if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
              erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                Real.log ((n * q : ℕ) : ℝ)
            else 0 := by
      have hnR' : n < M ∧ x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X := by
        simpa [R] using hnR
      have hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X := hnR'.2
      rw [finite_chain_initial_mass, if_pos hnint]
      congr 1
      exact tsum_eq_sum (s := Finset.range M) (fun q hq => by
        have hqnot : ¬ (2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X) := by
          intro hcond
          apply hq
          have hq_le_prod : q ≤ n * q := by
            have hn_one : 1 ≤ n := by
              have hn_two : 2 ≤ n := by exact_mod_cast (le_trans hx hnint.1)
              omega
            exact Nat.le_mul_of_pos_left q hn_one
          have hq_le_X : (q : ℝ) ≤ X := by
            have : ((q : ℕ) : ℝ) ≤ ((n * q : ℕ) : ℝ) := by
              exact_mod_cast hq_le_prod
            exact le_trans this hcond.2
          have hq_le_ceil : q ≤ ⌈X⌉₊ := by
            exact_mod_cast (le_trans hq_le_X (Nat.le_ceil X))
          have hq_lt_M : q < M := by
            dsimp [M]
            omega
          exact Finset.mem_range.mpr hq_lt_M
        rw [if_neg hqnot])
    have hfinite :
        (∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0) ≤
          (∑ n ∈ R, finite_chain_initial_mass x X n) + (2 * C_tail) / Real.log x := by
      let shadow : ℕ → ℝ := fun n =>
        if ∃ a : ℕ, a ∈ s ∧ a ∈ A ∧ a ∣ n then 1 else 0
      let pairs : Finset (ℕ × ℕ) := R.product (Finset.range M)
      let pairTerm : ℕ × ℕ → ℝ := fun p =>
        if 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X) then
          shadow p.1 * (erdos_weight (p.1 * p.2) *
            ArithmeticFunction.vonMangoldt p.2 / Real.log ((p.1 * p.2 : ℕ) : ℝ))
        else 0
      have hshadow_le_one : ∀ n, shadow n ≤ 1 := by
        intro n
        dsimp [shadow]
        split_ifs <;> norm_num
      have hfiber_bound : ∀ r ∈ R,
          ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p ≤ erdos_weight r := by
        intro r hr
        have hrR : r < M ∧ x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X := by
          simpa [R] using hr
        have hr_two : 2 ≤ r := by exact_mod_cast (le_trans hx hrR.2.1)
        have hr_ne : r ≠ 0 := by omega
        have hlog_pos : 0 < Real.log (r : ℝ) := by
          apply Real.log_pos
          exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hr_two)
        let F : Finset (ℕ × ℕ) := pairs.filter (fun p => p.1 * p.2 = r)
        let boundTerm : ℕ → ℝ := fun q =>
          erdos_weight r * ArithmeticFunction.vonMangoldt q / Real.log (r : ℝ)
        have hbound_nonneg : ∀ q, 0 ≤ boundTerm q := by
          intro q
          dsimp [boundTerm]
          have hw : 0 ≤ erdos_weight r := by
            rw [erdos_weight]
            positivity
          exact div_nonneg (mul_nonneg hw ArithmeticFunction.vonMangoldt_nonneg) hlog_pos.le
        have hpoint : ∀ p ∈ F, pairTerm p ≤ boundTerm p.2 := by
          intro p hp
          have hp' := Finset.mem_filter.mp hp
          have hprod : p.1 * p.2 = r := hp'.2
          dsimp [pairTerm, boundTerm]
          by_cases hcond : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
          · rw [if_pos hcond, hprod]
            simpa using
              mul_le_mul_of_nonneg_right (hshadow_le_one p.1) (hbound_nonneg p.2)
          · rw [if_neg hcond]
            exact hbound_nonneg p.2
        have hsum_le : (∑ p ∈ F, pairTerm p) ≤ ∑ p ∈ F, boundTerm p.2 := by
          apply Finset.sum_le_sum
          intro p hp
          exact hpoint p hp
        have hsum_image : (∑ p ∈ F, boundTerm p.2) =
            ∑ q ∈ F.image Prod.snd, boundTerm q := by
          symm
          rw [Finset.sum_image]
          intro a ha b hb hab
          have ha' := Finset.mem_filter.mp ha
          have hb' := Finset.mem_filter.mp hb
          have hpa : a.1 * a.2 = r := ha'.2
          have hpb : b.1 * b.2 = r := hb'.2
          have ha2_pos : 0 < a.2 := by
            by_contra hnot
            have ha2z : a.2 = 0 := Nat.eq_zero_of_not_pos hnot
            rw [ha2z] at hpa
            simp at hpa
            exact hr_ne hpa.symm
          have hfst : a.1 = b.1 := by
            apply Nat.mul_right_cancel ha2_pos
            rw [hpa, hab, hpb]
          exact Prod.ext hfst hab
        have himage_subset : F.image Prod.snd ⊆ r.divisors := by
          intro q hq
          rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
          have hp' := Finset.mem_filter.mp hp
          have hprod : p.1 * p.2 = r := hp'.2
          have hqdiv : p.2 ∣ r := by
            refine ⟨p.1, ?_⟩
            rw [mul_comm, hprod]
          exact Nat.mem_divisors.mpr ⟨hqdiv, hr_ne⟩
        have himage_le : (∑ q ∈ F.image Prod.snd, boundTerm q) ≤
            ∑ q ∈ r.divisors, boundTerm q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact himage_subset
          · intro q hq hqnot
            exact hbound_nonneg q
        have hdiv_eq : (∑ q ∈ r.divisors, boundTerm q) = erdos_weight r := by
          dsimp [boundTerm]
          calc
            (∑ q ∈ r.divisors,
              erdos_weight r * ArithmeticFunction.vonMangoldt q / Real.log (r : ℝ)) =
                (erdos_weight r / Real.log (r : ℝ)) *
                  ∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro q hq
                ring
            _ = (erdos_weight r / Real.log (r : ℝ)) * Real.log (r : ℝ) := by
                rw [von_mangoldt_divisor_sum]
            _ = erdos_weight r := by
                field_simp [hlog_pos.ne']
        calc
          (∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p) =
              ∑ p ∈ F, pairTerm p := rfl
          _ ≤ ∑ p ∈ F, boundTerm p.2 := hsum_le
          _ = ∑ q ∈ F.image Prod.snd, boundTerm q := hsum_image
          _ ≤ ∑ q ∈ r.divisors, boundTerm q := himage_le
          _ = erdos_weight r := hdiv_eq
      have hfiber_zero_active : ∀ r ∈ R, r ∈ s ∧ r ∈ A ->
          ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p = 0 := by
        intro r hr hactive
        apply Finset.sum_eq_zero
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hprod : p.1 * p.2 = r := hp'.2
        dsimp [pairTerm]
        by_cases hcond : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
        · rw [if_pos hcond]
          have hshadow_p1 : shadow p.1 = 0 := by
            dsimp [shadow]
            rw [if_neg]
            intro hex
            rcases hex with ⟨a, has, haA, hadiv⟩
            have hadivr : a ∣ r := by
              rcases hadiv with ⟨k, hk⟩
              refine ⟨k * p.2, ?_⟩
              rw [← hprod, hk, Nat.mul_assoc]
            have har : a = r := hprim.eq haA hactive.2 hadivr
            subst a
            have hrR : r < M ∧ x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X := by
              simpa [R] using hr
            have hp2_gt_one : 1 < p.2 := by omega
            have hp1_pos : 0 < p.1 := by
              by_contra hp10
              have hp1z : p.1 = 0 := Nat.eq_zero_of_not_pos hp10
              rw [hp1z] at hprod
              simp at hprod
              have hr_two : 2 ≤ r := by exact_mod_cast (le_trans hx hrR.2.1)
              omega
            have hp1_lt_r : p.1 < r := by
              rw [← hprod]
              exact lt_mul_of_one_lt_right hp1_pos hp2_gt_one
            exact not_le_of_gt hp1_lt_r (Nat.le_of_dvd hp1_pos hadiv)
          rw [hshadow_p1]
          ring
        · rw [if_neg hcond]
      have hshadow_factor_zero : ∀ r ∈ R, shadow r = 0 ->
          ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p = 0 := by
        intro r hr hsr
        apply Finset.sum_eq_zero
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hprod : p.1 * p.2 = r := hp'.2
        dsimp [pairTerm]
        by_cases hcond : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
        · rw [if_pos hcond]
          have hshadow_p1 : shadow p.1 = 0 := by
            dsimp [shadow] at hsr ⊢
            by_cases hex : ∃ a : ℕ, a ∈ s ∧ a ∈ A ∧ a ∣ p.1
            · exfalso
              have hexr : ∃ a : ℕ, a ∈ s ∧ a ∈ A ∧ a ∣ r := by
                rcases hex with ⟨a, has, haA, hadiv⟩
                refine ⟨a, has, haA, ?_⟩
                rcases hadiv with ⟨k, hk⟩
                refine ⟨k * p.2, ?_⟩
                rw [← hprod, hk, Nat.mul_assoc]
              rw [if_pos hexr] at hsr
              norm_num at hsr
            · rw [if_neg hex]
          rw [hshadow_p1]
          ring
        · rw [if_neg hcond]
      have hfiber : ∀ r ∈ R,
          (if r ∈ s ∧ r ∈ A then erdos_weight r else 0) +
            ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p ≤
              shadow r * erdos_weight r := by
        intro r hr
        by_cases hactive : r ∈ s ∧ r ∈ A
        · have hsh : shadow r = 1 := by
            dsimp [shadow]
            rw [if_pos]
            exact ⟨r, hactive.1, hactive.2, dvd_rfl⟩
          rw [if_pos hactive, hfiber_zero_active r hr hactive, hsh]
          linarith
        · rw [if_neg hactive]
          by_cases hshadow : shadow r = 0
          · rw [hshadow_factor_zero r hr hshadow, hshadow]
            norm_num
          · have hsh : shadow r = 1 := by
              dsimp [shadow] at hshadow ⊢
              by_cases hex : ∃ a : ℕ, a ∈ s ∧ a ∈ A ∧ a ∣ r
              · rw [if_pos hex]
              · rw [if_neg hex] at hshadow
                exfalso
                exact hshadow rfl
            rw [hsh]
            simpa using hfiber_bound r hr
      have hsum_fiber :
          (∑ r ∈ R, ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p) =
            ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p := by
        exact Finset.sum_fiberwise_eq_sum_filter pairs R
          (fun p : ℕ × ℕ => p.1 * p.2) pairTerm
      have hupper :
          (∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0) +
              ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p ≤
            ∑ n ∈ R, shadow n * erdos_weight n := by
        calc
          (∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0) +
              ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p =
                ∑ n ∈ R,
                  ((if n ∈ s ∧ n ∈ A then erdos_weight n else 0) +
                    ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = n), pairTerm p) := by
                rw [Finset.sum_add_distrib, hsum_fiber]
          _ ≤ ∑ n ∈ R, shadow n * erdos_weight n := by
                apply Finset.sum_le_sum
                intro n hn
                exact hfiber n hn
      have hpair_all_eq :
          (∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p) =
            ∑ p ∈ pairs, pairTerm p := by
        apply Finset.sum_subset
        · intro p hp
          exact (Finset.mem_filter.mp hp).1
        · intro p hpairs hpnot
          have hprod_not : p.1 * p.2 ∉ R := by
            intro hpR
            apply hpnot
            simp [hpairs, hpR]
          have hp : p.1 ∈ R ∧ p.2 ∈ Finset.range M := by
            simpa [pairs] using hpairs
          dsimp [pairTerm]
          by_cases hcond : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
          · exfalso
            apply hprod_not
            have hp1R : p.1 < M ∧ x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X := by
              simpa [R] using hp.1
            have hp2one : 1 ≤ p.2 := by omega
            have hp1_le_prod : p.1 ≤ p.1 * p.2 :=
              Nat.le_mul_of_pos_right p.1 hp2one
            have hxprod : x ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
              have : (p.1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
                exact_mod_cast hp1_le_prod
              exact le_trans hp1R.2.1 this
            have hprod_le_ceil : p.1 * p.2 ≤ ⌈X⌉₊ := by
              exact_mod_cast (le_trans hcond.2 (Nat.le_ceil X))
            have hprod_lt_M : p.1 * p.2 < M := by
              dsimp [M]
              omega
            simp only [R, Finset.mem_filter, Finset.mem_range]
            exact ⟨hprod_lt_M, by simpa [Nat.cast_mul] using hxprod,
              by simpa [Nat.cast_mul] using hcond.2⟩
          · rw [if_neg hcond]
      have hpair_product :
          (∑ p ∈ pairs, pairTerm p) =
            ∑ n ∈ R, shadow n *
              ∑ q ∈ Finset.range M,
                if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                  erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                    Real.log ((n * q : ℕ) : ℝ)
                else 0 := by
        dsimp [pairs, pairTerm]
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro n hn
        simp only [Prod.fst, Prod.snd]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hcond : 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X
        · simp [hcond]
        · simp [hcond]
      have hshadow_bound :
          (∑ n ∈ R, shadow n * erdos_weight n) ≤
            (∑ n ∈ R, finite_chain_initial_mass x X n) + (2 * C_tail) / Real.log x +
              ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p := by
        rw [hpair_all_eq, hpair_product]
        have herr_sum :
            (∑ n ∈ R, C_tail / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) ≤
              (2 * C_tail) / Real.log x := by
          have hR_int : ∀ n ∈ R, x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X := by
            intro n hn
            exact (Finset.mem_filter.mp hn).2
          have htele := inv_mul_log_sq_sum_le_div_log x X hx R hR_int
          calc
            (∑ n ∈ R, C_tail / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) =
                C_tail * ∑ n ∈ R, 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro n _
              ring
            _ ≤ C_tail * (2 / Real.log x) := by
              exact mul_le_mul_of_nonneg_left htele hC_tail_nonneg
            _ = (2 * C_tail) / Real.log x := by ring
        have hsum_le :
            (∑ n ∈ R, shadow n * finite_chain_initial_mass x X n) ≤
              (∑ n ∈ R, finite_chain_initial_mass x X n) + (2 * C_tail) / Real.log x := by
          have hpt :
              (∑ n ∈ R, shadow n * finite_chain_initial_mass x X n) ≤
                ∑ n ∈ R, (finite_chain_initial_mass x X n +
                  C_tail / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) := by
            apply Finset.sum_le_sum
            intro n _
            let e : ℝ := C_tail / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)
            have he_nonneg : 0 ≤ e := by dsimp [e]; positivity
            have hbe_nonneg : 0 ≤ finite_chain_initial_mass x X n + e := by
              have hl := hmass_lower n
              dsimp [e]
              linarith
            have h1 : shadow n * (finite_chain_initial_mass x X n + e) ≤
                1 * (finite_chain_initial_mass x X n + e) :=
              mul_le_mul_of_nonneg_right (hshadow_le_one n) hbe_nonneg
            have hsn : 0 ≤ shadow n := by dsimp [shadow]; split_ifs <;> norm_num
            have h2 : 0 ≤ shadow n * e := mul_nonneg hsn he_nonneg
            dsimp [e] at h1 h2 ⊢
            linarith
          rw [Finset.sum_add_distrib] at hpt
          linarith
        calc
          (∑ n ∈ R, shadow n * erdos_weight n) =
              ∑ n ∈ R, shadow n *
                (finite_chain_initial_mass x X n +
                  ∑ q ∈ Finset.range M,
                    if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                      erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                        Real.log ((n * q : ℕ) : ℝ)
                    else 0) := by
                apply Finset.sum_congr rfl
                intro n hn
                rw [hmass_finite n hn]
                ring
          _ = (∑ n ∈ R, shadow n * finite_chain_initial_mass x X n) +
              ∑ n ∈ R, shadow n *
                ∑ q ∈ Finset.range M,
                  if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                    erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                      Real.log ((n * q : ℕ) : ℝ)
                  else 0 := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro n hn
                ring
          _ ≤ (∑ n ∈ R, finite_chain_initial_mass x X n) + (2 * C_tail) / Real.log x +
              ∑ n ∈ R, shadow n *
                ∑ q ∈ Finset.range M,
                  if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                    erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                      Real.log ((n * q : ℕ) : ℝ)
                  else 0 := by
                linarith
      linarith
    rw [hb_tsum_eq, hleft_eq]
    exact hfinite

@[blueprint "lem:finite-chain-cut-bound"
  (statement := /-- There exists an absolute constant $C_{\mathrm{err}}\geq 0$
  such that, for every $x\geq 2$, every real $X$, and every primitive set
  $A\subseteq\mathbb N$ supported in $[x,X]$, the Erd\H{o}s sum of $A$ is at
  most the finite cut capacity \cref{def:cut-capacity} plus
  $C_{\mathrm{err}}/\log x$. -/)
  (proof := /-- Combine \cref{lem:finite-chain-erdos-le-initial-mass} with the
  exact reindexing identity
  \cref{lem:finite-chain-initial-mass-sum-eq-cut-capacity}. -/)
  (title := /-- Finite chain cut bound (Mertens-only) -/)
  (latexEnv := "lemma")]
lemma finite_chain_cut_bound :
    ∃ C_err : ℝ, 0 ≤ C_err ∧
      ∀ (A : Set ℕ) (x X : ℝ), 2 ≤ x -> primitive_set A -> supported_in_interval A x X ->
        erdos_sum A ≤ cut_capacity x X + C_err / Real.log x := by
  obtain ⟨C_err, hC_nonneg, hbound⟩ := finite_chain_erdos_le_initial_mass
  refine ⟨C_err, hC_nonneg, ?_⟩
  intro A x X hx hprim hsupp
  calc
    erdos_sum A ≤ (∑' n : ℕ, finite_chain_initial_mass x X n) + C_err / Real.log x :=
      hbound A x X hx hprim hsupp
    _ = cut_capacity x X + C_err / Real.log x := by
      rw [finite_chain_initial_mass_sum_eq_cut_capacity x X hx]

@[blueprint "lem:finite-large-primitive-bound"
  (statement := /-- There is a nonnegative real constant $C$ satisfying
  \cref{def:erdos1196-finite-bound}: every primitive set supported in a finite
  interval $[x,X]$ with $2\leq x\leq X$ has Erd\H{o}s sum at most
  $1+C/\log x$. -/)
  (proof := /-- Combine the Mertens-only cut bound
  \cref{lem:finite-chain-cut-bound}, \cref{lem:cut-capacity-le-tail-majorant},
  and \cref{lem:tail-majorant-bound}. -/)
  (title := /-- Finite large primitive-set bound -/)
  (latexEnv := "lemma")]
lemma finite_large_primitive_bound :
    ∃ C : ℝ, erdos1196_finite_bound C := by
  obtain ⟨C1, hC1_nonneg, hC1_bound⟩ := tail_majorant_bound
  obtain ⟨C2, hC2_nonneg, hC2_bound⟩ := finite_chain_cut_bound
  refine ⟨C1 + C2, by linarith, ?_⟩
  intro x X hx _ A hprim hsupp
  calc
    erdos_sum A ≤ cut_capacity x X + C2 / Real.log x := hC2_bound A x X hx hprim hsupp
    _ ≤ tail_majorant x + C2 / Real.log x := by
      linarith [cut_capacity_le_tail_majorant x X hx]
    _ ≤ (1 + C1 / Real.log x) + C2 / Real.log x := by
      linarith [hC1_bound x hx]
    _ = 1 + (C1 + C2) / Real.log x := by ring

@[blueprint "thm:erdos-sarkozy-szemeredi-1196"
  (statement := /-- There exists a nonnegative real constant $C$ such that, for
  every real number $x$ with $2\leq x$ and every primitive set
  $A\subseteq\mathbb{N}$ contained in $[x,\infty)$, the Erd\H{o}s sum satisfies
  $f(A)\leq 1+C/\log x$. -/)
  (proof := /-- The finite theorem \cref{lem:finite-large-primitive-bound}
  supplies an absolute constant for all primitive sets supported in finite
  intervals $[x,X]$. Applying the limiting principle
  \cref{lem:finite-truncation-principle} removes the upper endpoint and gives
  the stated bound for all primitive sets contained in $[x,\infty)$. -/)
  (title := /-- Erd\H{o}s--S\'ark\"ozy--Szemer\'edi problem \#1196 -/)
  (latexEnv := "theorem")]
theorem erdos_sarkozy_szemeredi_1196 :
    ∃ C : ℝ, erdos1196_bound C := by
  exact finite_truncation_principle finite_large_primitive_bound
