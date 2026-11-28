///|
/// aut_l.mbt — 34. 自守L-函數 (automorphic L-functions)
///
/// L(π, s) = Σ a_n n^{−s} = ∏_p L(π_p, s) with L(π_p) = det(1 − A_p p^{−s})^{-1},
/// A_p = Satake (diag(α_p, β_p)). Rankin–Selberg convolution:
/// L(π × π, s) = Σ |a_n|² n^{−s} = ∏_p (1−α²p^{−s})^{-1}(1−αβ p^{−s})^{-1}(1−β²p^{−s})^{-1}.
///
/// Theorem engine:
///   T34a (Rankin–Selberg Euler 乘積): Σ|a_n|²n^{−s} = ∏ 三因子 Euler 乘積
///   T34b (Satake 三重積): local factor 由 (α², αβ, β²) = Sym² Satake 決定
///       （與 T35 的函子性交會：RS = Sym² ⊗ det^{−1}）
///   T34c (GL₂ 新形式 L-函數): 權 2 層 11 形式的 L = Euler 乘積（在模性中驗證）

///|
/// s_m = α^m + β^m recursion for a weight-k eigenform at prime p:
/// s_0 = 2, s_1 = a_p, s_m = a_p·s_{m−1} − p^{k−1}·s_{m−2}.
pub fn satake_power_sums(
  a_p : Int64,
  p : Int32,
  k : Int32,
  m_max : Int32,
) -> Array[Int64] {
  let pk = pow64(p.to_int64(), k - 1)
  let s : Array[Int64] = []
  s.push(2L)
  s.push(a_p)
  let mut m = 2
  while m <= m_max {
    s.push(a_p * s[m - 1] - pk * s[m - 2])
    m = m + 1
  }
  s
}

///|
/// Sym² (= Rankin–Selberg GL₃) coefficients b_n (Double), multiplicative:
/// b_{p^j} = h_j(α², αβ, β²) — complete homogeneous symmetric polynomials,
/// the Dirichlet coefficients of det(1 − A_p^{Sym²} X)^{-1}:
///   h_0 = 1, h_j = e1·h_{j−1} − e2·h_{j−2} + e3·h_{j−3}
/// with (e1, e2, e3) = sym2_satake(a_p, p, k).
pub fn rankin_selberg_coefficients(
  a : Array[Int64],
  k : Int32,
  n_max : Int32,
) -> Array[Double] {
  let b : Array[Double] = []
  let mut i = 0
  while i <= n_max {
    b.push(0.0)
    i = i + 1
  }
  b[1] = 1.0
  for p2 in primes_upto(n_max) {
    let (e1, e2, e3) = sym2_satake(a[p2], p2, k)
    // h_j in Double (values reach p^{(k−1)j} ~ 2^{55})
    let h : Array[Double] = []
    h.push(1.0)
    let mut j = 1
    let mut pj = p2
    while pj <= n_max {
      let t1 = e1.to_double() * h[j - 1]
      let t2 = if j >= 2 { e2.to_double() * h[j - 2] } else { 0.0 }
      let t3 = if j >= 3 { e3.to_double() * h[j - 3] } else { 0.0 }
      h.push(t1 - t2 + t3)
      b[pj] = h[j]
      pj = pj * p2
      j = j + 1
    }
  }
  let mut n = 2
  while n <= n_max {
    let mut u = 2
    while u * u <= n {
      if n % u == 0 {
        let v = n / u
        if gcd_int(u, v) == 1 && b[u] != 0.0 {
          b[n] = b[u] * b[v]
          u = n
        }
      }
      u = u + 1
    }
    n = n + 1
  }
  b
}

///|
/// Dirichlet series Σ b_n n^{−s} (Double).
pub fn dirichlet_series_double(
  b : Array[Double],
  n_max : Int32,
  s : Double,
) -> Double {
  let mut acc = 0.0
  let mut n = 1
  while n <= n_max && n < b.length() {
    acc = acc + b[n] / @math.pow(n.to_double(), s)
    n = n + 1
  }
  acc
}

///|
/// Euler product of the Rankin–Selberg L: for each p ≤ p_max,
/// factor = (1 − b_p X + e2 X² − e3 X³)^{-1} with X = p^{−s},
/// e1 = b_p, e2 = p^{k−1}·e1... wait for π×π: (α², αβ, β²):
/// e1 = α²+αβ+β² = a_p² − p^{k−1}, e2 = αβ(α²+αβ+β²) = p^{k−1}·e1,
/// e3 = (αβ)³ = p^{3(k−1)}.
pub fn rankin_selberg_euler(
  a : Array[Int64],
  k : Int32,
  p_max : Int32,
  s : Double,
) -> Double {
  let mut acc = 1.0
  for p in primes_upto(p_max) {
    if p < a.length() {
      let pk = pow64(p.to_int64(), k - 1).to_double()
      let ap = a[p].to_double()
      let e1 = ap * ap - pk
      let e2 = pk * e1
      let e3 = pk * pk * pk
      let x = 1.0 / @math.pow(p.to_double(), s)
      let factor = 1.0 - e1 * x + e2 * x * x - e3 * x * x * x
      acc = acc / factor
    }
  }
  acc
}

///|
/// Symmetric square coefficients b_n for the GL_3 lift Sym²π:
/// b_p = a_p² − p^{k−1}, b_{p^j} = α^{2j} + α^jβ^j + β^{2j} = same as RS;
/// for π self-dual with unitary normalization, Sym² π ⊗ det^{−1}... we use
/// the GL_3 lift with Satake (α², αβ, β²) directly (unnormalized sym²).
pub fn sym2_coefficients(
  a : Array[Int64],
  k : Int32,
  n_max : Int32,
) -> Array[Double] {
  rankin_selberg_coefficients(a, k, n_max)
}

///|
/// Verify Sym² local identity: b_p = a_p² − p^{k−1} for all p ≤ p_max.
pub fn sym2_local_identity_error(
  a : Array[Int64],
  k : Int32,
  p_max : Int32,
) -> Double {
  let b = sym2_coefficients(a, k, p_max)
  let mut max_err = 0.0
  for p in primes_upto(p_max) {
    if p < a.length() {
      let want = a[p].to_double() * a[p].to_double() -
        pow64(p.to_int64(), k - 1).to_double()
      let diff = if b[p] > want { b[p] - want } else { want - b[p] }
      if diff > max_err {
        max_err = diff
      }
    }
  }
  max_err
}
