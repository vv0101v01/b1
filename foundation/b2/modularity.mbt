///|
/// modularity.mbt — 40. 模性定理 (modularity theorem)
///
/// E = X₀(11): y² + y = x³ − x² − 10x − 20 (conductor 11). The newform of
/// S₂(Γ₀(11)) is f = η(τ)²η(11τ)² = q ∏(1−qⁿ)²(1−q^{11n})² = Σ a_n q^n.
///
/// Modularity means a_p = p + 1 − #E(F_p) for ALL p. We verify this
/// prime-by-prime by brute-force point counting, PLUS:
///   — Hecke relation a_{p²} = a_p² − p (weight 2)
///   — Hasse bound |a_p| ≤ 2√p (Riemann hypothesis for curves!)
///   — known coefficients a₂ = −2, a₃ = −1, a₅ = 1, a₇ = −2, a₁₁ = 1, a₁₃ = 4
///
/// Theorem engine:
///   T40a (模性逐素數驗證): a_p(q-展開) = p+1−#E(F_p), p ≤ 47
///   T40b (Hasse 界): |a_p| ≤ 2√p（模性 ⇒ 曲線 RH）
///   T40c (Hecke 關係): a_{m}a_{n} = Σ_{d|gcd}d·a_{mn/d²}（weight 2）

///|
/// The X₀(11) curve as WCurve (a1, a2, a3, a4, a6).
pub fn x011_curve() -> WCurve {
  WCurve(0, -1, 1, -10, -20)
}

///|
/// q-expansion of η(τ)²η(11τ)² = q ∏(1−qⁿ)²(1−q^{11n})² up to q^{n_max}.
/// Returns coefficients a[0..n_max] with a[0] = 0, a[1] = 1.
pub fn newform_level11(n_max : Int32) -> Array[Int64] {
  let prod : Array[Int64] = []
  let mut i = 0
  while i <= n_max {
    prod.push(0L)
    i = i + 1
  }
  prod[0] = 1L
  // multiply by (1 − q^m)² for m = 1..n_max and m = 11, 22, ...
  let mut m = 1
  while m <= n_max {
    // factor (1 − q^m)² = 1 − 2q^m + q^{2m}
    let next : Array[Int64] = []
    let mut t = 0
    while t <= n_max {
      next.push(0L)
      t = t + 1
    }
    let mut j = 0
    while j <= n_max {
      if prod[j] != 0L {
        next[j] = next[j] + prod[j]
        if j + m <= n_max {
          next[j + m] = next[j + m] - 2 * prod[j]
        }
        if j + 2 * m <= n_max {
          next[j + 2 * m] = next[j + 2 * m] + prod[j]
        }
      }
      j = j + 1
    }
    let mut j2 = 0
    while j2 <= n_max {
      prod[j2] = next[j2]
      j2 = j2 + 1
    }
    m = m + 1
  }
  // second pass for (1 − q^{11m})², m = 1..n_max/11
  let mut m2 = 1
  while 11 * m2 <= n_max {
    let mm = 11 * m2
    let next : Array[Int64] = []
    let mut t = 0
    while t <= n_max {
      next.push(0L)
      t = t + 1
    }
    let mut j = 0
    while j <= n_max {
      if prod[j] != 0L {
        next[j] = next[j] + prod[j]
        if j + mm <= n_max {
          next[j + mm] = next[j + mm] - 2 * prod[j]
        }
        if j + 2 * mm <= n_max {
          next[j + 2 * mm] = next[j + 2 * mm] + prod[j]
        }
      }
      j = j + 1
    }
    let mut j2 = 0
    while j2 <= n_max {
      prod[j2] = next[j2]
      j2 = j2 + 1
    }
    m2 = m2 + 1
  }
  // shift by q: a[n] = prod[n − 1]
  let res : Array[Int64] = []
  res.push(0L)
  let mut n = 1
  while n <= n_max {
    res.push(prod[n - 1])
    n = n + 1
  }
  res
}

///|
/// Verify modularity at prime p: a_p from q-expansion = p + 1 − #E(F_p).
/// Returns (match, a_qexp, a_count).
pub fn modularity_check_prime(p : Int32) -> (Bool, Int64, Int64) {
  let e = x011_curve()
  let count = e.count_points(p, 1)
  let a_count = (p + 1 - count).to_int64()
  let f = newform_level11(p)
  let a_q = f[p]
  (a_q == a_count, a_q, a_count)
}

///|
/// Max Hasse violation over p ≤ p_max: max(0, |a_p| − 2√p) as Double.
pub fn hasse_violation(p_max : Int32) -> Double {
  let f = newform_level11(p_max)
  let mut worst = 0.0
  for p in primes_upto(p_max) {
    let ap = f[p].to_double()
    let bound = 2.0 * p.to_double().sqrt()
    let absv = if ap < 0.0 { -ap } else { ap }
    let v = absv - bound
    if v > worst {
      worst = v
    }
  }
  worst
}

///|
/// T40c Hecke relation check for weight 2 level 11: a_m a_n = Σ_{d|gcd} d·a_{mn/d²}
/// for m, n ≤ n_max with mn ≤ n_max. Returns violation count.
pub fn modularity_hecke_violations(n_max : Int32) -> Int32 {
  let f = newform_level11(n_max)
  let mut bad = 0
  let mut m = 1
  while m <= n_max {
    let mut n = 1
    while n <= n_max {
      if m * n <= n_max {
        let lhs = f[m] * f[n]
        let mut rhs = 0L
        let mut d = 1
        while d * d <= m * n + 1 {
          if m % d == 0 && n % d == 0 {
            rhs = rhs + d.to_int64() * f[m * n / (d * d)]
          }
          d = d + 1
        }
        if lhs != rhs {
          bad = bad + 1
        }
      }
      n = n + 1
    }
    m = m + 1
  }
  bad
}

///|
/// Known prime coefficients of 11.a (LMFDB): a₂ = −2, a₃ = −1, a₅ = 1,
/// a₇ = −2, a₁₁ = 1. Verifies the q-expansion against the tabulated newform.
pub fn level11_known_prime_check() -> (Bool, String) {
  let f = newform_level11(12)
  let checks = [(2, -2L), (3, -1L), (5, 1L), (7, -2L), (11, 1L)]
  let mut ok = true
  let mut s = ""
  for (p, want) in checks {
    let got = f[p]
    let pass = got == want
    if !pass {
      ok = false
    }
    s = s + "a_\{p}: got \{got}, want \{want} — \{pass}\n"
  }
  (ok, s)
}
