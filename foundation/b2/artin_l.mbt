///|
/// artin_l.mbt — 33. 阿廷L-函數 (Artin L-functions)
///
/// For a character χ of G_Q with finite image (≡ Dirichlet character),
/// L(χ, s) = ∏_p (1 − χ(p) p^{−s})^{-1} = Σ_n χ(n) n^{−s}.
/// For higher-dim reps: L(ρ, s) = ∏_p det(1 − ρ(Frob_p) p^{−s})^{-1};
/// additivity L(ρ₁ ⊕ ρ₂) = L(ρ₁)L(ρ₂) (Artin formalism).
///
/// Theorem engine:
///   T33a (Artin = Dirichlet): Euler 乘積 = Dirichlet 級數（order-4 特徵 mod 5 等）
///   T33b (Artin 形式論): L(χ₁ ⊕ χ₂, s) = L(χ₁, s)·L(χ₂, s)（Euler 因子逐項）
///   T33c (Dedekind zeta 分解): ζ_{Q(i)}(s) = ζ(s)·L(χ₋₄, s)
///       （由 a²+b² 表數公式 r₂(n) = 4Σ_{d|n}χ₋₄(d) 精確＋數值雙驗證）

///|
/// A Dirichlet character mod n, stored as χ values at generators... simplest
/// concrete encoding: χ(a) = ω^{ind_g(a)} with ω = e^{2πi/order}, g a fixed
/// primitive root / generator. We store the exponent table: exp[a] = ind.
/// Values as Cx.
pub(all) struct DirChar {
  n : Int32
  values : Array[Cx]
}

///|
/// Build the order-4 character mod 5 (ψ(2) = i) — values delegated to psi5,
/// the single source of truth for this character.
pub fn dir_char_mod5() -> DirChar {
  let vals : Array[Cx] = []
  let mut a = 0
  while a < 5 {
    vals.push(psi5(a))
    a = a + 1
  }
  DirChar::{ n: 5, values: vals, }
}

///|
/// Quadratic character χ₋₄ mod 4: χ(1) = 1, χ(3) = −1.
pub fn dir_char_chi4() -> DirChar {
  let vals : Array[Cx] = []
  vals.push(Cx(0.0, 0.0))
  vals.push(Cx(1.0, 0.0))
  vals.push(Cx(0.0, 0.0))
  vals.push(Cx(-1.0, 0.0))
  DirChar::{ n: 4, values: vals, }
}

///|
/// χ(n) for arbitrary n (0 if gcd(n, m) > 1).
pub fn DirChar::value(self : DirChar, n : Int32) -> Cx {
  let mut m = n % self.n
  if m < 0 {
    m = m + self.n
  }
  self.values[m]
}

///|
/// Dirichlet series partial sum Σ_{n=1}^{N} χ(n) n^{−s}.
pub fn dirichlet_series_char(chi : DirChar, n_max : Int32, s : Double) -> Cx {
  let mut acc = Cx(0.0, 0.0)
  let mut n = 1
  while n <= n_max {
    let ns = @math.pow(n.to_double(), s)
    acc = acc.add(chi.value(n).scale(1.0 / ns))
    n = n + 1
  }
  acc
}

///|
/// Euler product partial ∏_{p ≤ pmax} (1 − χ(p) p^{−s})^{−1}.
pub fn euler_product_char(chi : DirChar, p_max : Int32, s : Double) -> Cx {
  let mut acc = Cx(1.0, 0.0)
  for p in primes_upto(p_max) {
    let ps = @math.pow(p.to_double(), s)
    let one_minus = Cx(1.0, 0.0).add(chi.value(p).scale(-1.0 / ps))
    // inverse of one_minus
    let denom = one_minus.0 * one_minus.0 + one_minus.1 * one_minus.1
    let inv = Cx(one_minus.0 / denom, -one_minus.1 / denom)
    acc = acc.mul(inv)
  }
  acc
}

///|
/// Artin formalism, numerical version: L(χ₁, s)·L(χ₂, s) computed two ways —
/// (a) product of two Dirichlet series; (b) Euler product of the direct-sum
/// representation det(1 − diag(χ₁(p), χ₂(p)) p^{−s}) = (1−χ₁X)(1−χ₂X).
/// Returns the absolute difference.
pub fn artin_direct_sum_error(
  chi1 : DirChar,
  chi2 : DirChar,
  n_max : Int32,
  p_max : Int32,
  s : Double,
) -> Double {
  let l1 = dirichlet_series_char(chi1, n_max, s)
  let l2 = dirichlet_series_char(chi2, n_max, s)
  let via_series = l1.mul(l2)
  let via_euler = euler_product_char(chi1, p_max, s).mul(
    euler_product_char(chi2, p_max, s),
  )
  via_series.sub(via_euler).abs()
}

///|
/// r_2(n) = #{(a,b) ∈ Z² : a² + b² = n} by direct enumeration.
pub fn r2_direct(n : Int32) -> Int32 {
  let mut count = 0
  let mut a = -n
  while a <= n {
    let mut b = -n
    while b <= n {
      if a * a + b * b == n {
        count = count + 1
      }
      b = b + 1
    }
    a = a + 1
  }
  count
}

///|
/// Formula: r_2(n) = 4 Σ_{d | n} χ₋₄(d).
pub fn r2_formula(n : Int32) -> Int32 {
  let chi = dir_char_chi4()
  let mut s = 0
  let mut d = 1
  while d <= n {
    if n % d == 0 {
      let v = chi.value(d).0
      let iv = if v > 0.5 { 1 } else if v < -0.5 { -1 } else { 0 }
      s = s + iv
    }
    d = d + 1
  }
  4 * s
}

///|
/// ζ_{Q(i)}(s) = Σ_n (#ideals of norm n) n^{−s} = Σ_n r₂(n)/4 · n^{−s}.
pub fn zeta_qi_series(n_max : Int32, s : Double) -> Double {
  let mut acc = 0.0
  let mut n = 1
  while n <= n_max {
    acc = acc + (r2_formula(n) / 4).to_double() / @math.pow(n.to_double(), s)
    n = n + 1
  }
  acc
}

///|
/// ζ(s) partial sum (Euler–Maclaurin-free: direct sum + tail bound ok at s ≥ 6).
pub fn zeta_series(n_max : Int32, s : Double) -> Double {
  let mut acc = 0.0
  let mut n = 1
  while n <= n_max {
    acc = acc + 1.0 / @math.pow(n.to_double(), s)
    n = n + 1
  }
  acc
}

///|
/// L(χ₋₄, s) partial sum.
pub fn l_chi4_series(n_max : Int32, s : Double) -> Double {
  let chi = dir_char_chi4()
  let c = dirichlet_series_char(chi, n_max, s)
  c.0
}
