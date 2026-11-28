///|
/// theta.mbt — 39. 塞塔對應 (theta correspondence)
///
/// θ(z, τ) = Σ_{n∈Z} q^{n²} z^n (q = e^{πiτ}); Jacobi triple product:
/// Σ q^{n²} z^{2n} = ∏_{m≥1} (1−q^{2m})(1 + q^{2m−1}z²)(1 + q^{2m−1}z^{−2}).
/// θ₃(q)² = Σ_n r₂(n) q^n (two squares), and the theta lift of the trivial
/// character of O(1) to SL_2 gives the weight-1/2... classical theta series
/// of the quadratic form x² + y²:
///
/// Theorem engine:
///   T39a (Jacobi 三重積): Σ q^{n²}z^{2n} = ∏ 三重積（數值，多組 q, z）
///   T39b (塞塔 ↔ 二次型計數): [q^n] θ₃(q)² = r₂(n)（級數乘法 vs 直接計數）
///   T39c (塞塔 ↔ L-函數): r₂(n) = 4Σ_{d|n}χ₋₄(d)（= T33c 的 θ 語言重述，
///       並以 ζ_{Q(i)} = ζ·L(χ₋₄) 的數值閉環）

///|
/// Jacobi triple product: LHS = Σ_n q^{n²} z^{2n}, RHS = product, both
/// truncated at n, m ≤ n_max. Returns |lhs − rhs|.
pub fn jacobi_triple_product_error(
  q : Double,
  z : Double,
  n_max : Int32,
) -> Double {
  // LHS
  let mut lhs = 0.0
  let mut n = -n_max
  while n <= n_max {
    lhs = lhs +
      @math.pow(q, (n * n).to_double()) * @math.pow(z, (2 * n).to_double())
    n = n + 1
  }
  // RHS
  let mut rhs = 1.0
  let mut m = 1
  while m <= n_max {
    let q2m = @math.pow(q, (2 * m).to_double())
    let q2m1 = @math.pow(q, (2 * m - 1).to_double())
    let z2 = z * z
    let inv_z2 = 1.0 / z2
    rhs = rhs * (1.0 - q2m) * (1.0 + q2m1 * z2) * (1.0 + q2m1 * inv_z2)
    m = m + 1
  }
  let d = lhs - rhs
  if d < 0.0 {
    -d
  } else {
    d
  }
}

///|
/// θ₃(q) = Σ q^{n²} coefficients: theta3_coeffs[n] = # of representations
/// n = k² (0 or 1) — actually coefficient of q^n in Σ q^{k²} is 1 if n is a
/// perfect square. θ₃² coefficients via convolution = r₂(n).
pub fn theta3_squared_coefficients(n_max : Int32) -> Array[Int32] {
  // coefficients of θ₃
  let th : Array[Int32] = []
  let mut i = 0
  while i <= n_max {
    th.push(0)
    i = i + 1
  }
  th[0] = 1
  let mut k = 1
  while k * k <= n_max {
    th[k * k] = 2 // n = ±k both contribute
    k = k + 1
  }
  // square the series
  let sq : Array[Int32] = []
  let mut j = 0
  while j <= n_max {
    sq.push(0)
    j = j + 1
  }
  let mut a = 0
  while a <= n_max {
    let mut b = 0
    while b <= n_max {
      if a + b <= n_max {
        sq[a + b] = sq[a + b] + th[a] * th[b]
      }
      b = b + 1
    }
    a = a + 1
  }
  sq
}

///|
/// Verify T39b: θ₃² coefficients = r₂(n) direct counts.
pub fn theta_r2_error(n_max : Int32) -> Int32 {
  let sq = theta3_squared_coefficients(n_max)
  let mut max_err = 0
  let mut n = 0
  while n <= n_max {
    let direct = r2_direct(n)
    let d = if sq[n] > direct { sq[n] - direct } else { direct - sq[n] }
    if d > max_err {
      max_err = d
    }
    n = n + 1
  }
  max_err
}

///|
/// Dirichlet series of θ₃² vs ζ(s)L(χ₋₄, s)·4... Σ r₂(n) n^{−s} = 4ζ(s)L(χ₋₄,s).
pub fn theta_l_function_error(n_max : Int32, s : Double) -> Double {
  let sq = theta3_squared_coefficients(n_max)
  let mut lhs = 0.0
  let mut n = 1
  while n <= n_max {
    lhs = lhs + sq[n].to_double() / @math.pow(n.to_double(), s)
    n = n + 1
  }
  let rhs = 4.0 * zeta_series(n_max, s) * l_chi4_series(n_max, s)
  let d = lhs - rhs
  if d < 0.0 {
    -d
  } else {
    d
  }
}
