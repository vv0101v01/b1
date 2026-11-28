///|
/// autf.mbt — 自守形式 (automorphic forms)：SL_2(Z) 的模形式 q-展開
/// Eisenstein 級數 E4, E6、判別式 Δ、Hecke 算子、特徵形式
///
/// Theorem engine:
///   T18 (模判別式恆等式): E4³ − E6² = 1728 Δ
///   T19 (Hecke 特徵形式): T_p Δ = τ(p) Δ；S_12 = C·Δ
///   T20 (Hecke 交換性): T_m T_n = Σ_{d|(m,n)} d^{k−1} T_{mn/d²}
///   T21 (Ramanujan 乘性): τ(mn) = τ(m)τ(n) 當 gcd(m,n) = 1

///|
/// q-series truncated at q^N: coefficients of q^0..q^{N-1} (Int64).
pub(all) struct QSeries(Array[Int64])

///|
pub fn QSeries::coeff(self : QSeries, n : Int32) -> Int64 {
  if n < 0 || n >= self.0.length() {
    0L
  } else {
    self.0[n]
  }
}

///|
/// Series addition.
pub fn QSeries::add(self : QSeries, other : QSeries) -> QSeries {
  let res : Array[Int64] = []
  let mut n = 0
  while n < self.0.length() {
    res.push(self.0[n] + other.coeff(n))
    n = n + 1
  }
  QSeries(res)
}

///|
/// Series subtraction.
pub fn QSeries::sub(self : QSeries, other : QSeries) -> QSeries {
  let res : Array[Int64] = []
  let mut n = 0
  while n < self.0.length() {
    res.push(self.0[n] - other.coeff(n))
    n = n + 1
  }
  QSeries(res)
}

///|
/// Series multiplication mod q^N.
pub fn QSeries::mul(self : QSeries, other : QSeries) -> QSeries {
  let n0 = self.0.length()
  let res : Array[Int64] = []
  let mut i = 0
  while i < n0 {
    let mut acc = 0L
    let mut j = 0
    while j <= i {
      acc = acc + self.0[j] * other.coeff(i - j)
      j = j + 1
    }
    res.push(acc)
    i = i + 1
  }
  QSeries(res)
}

///|
/// Series equality on the first m coefficients.
pub fn QSeries::equals_upto(self : QSeries, other : QSeries, m : Int32) -> Bool {
  let mut n = 0
  while n < m && n < self.0.length() {
    if self.0[n] != other.coeff(n) {
      return false
    }
    n = n + 1
  }
  true
}

///|
/// Scale all coefficients by c.
pub fn QSeries::scale(self : QSeries, c : Int64) -> QSeries {
  let res : Array[Int64] = []
  for x in self.0 {
    res.push(x * c)
  }
  QSeries(res)
}

///|
/// Binomial coefficient C(n, k) as Int64 (n ≤ 30).
pub fn binom_i64(n : Int32, k : Int32) -> Int64 {
  if k < 0 || k > n {
    return 0L
  }
  let kk = if k > n - k { n - k } else { k }
  let mut acc = 1L
  let mut i = 0
  while i < kk {
    acc = acc * (n - i).to_int64()
    acc = acc / (i + 1).to_int64()
    i = i + 1
  }
  acc
}

///|
/// eta-product factor (1 - q^m)^e as a QSeries mod q^N.
pub fn eta_factor(m : Int32, e : Int32, n0 : Int32) -> QSeries {
  let res : Array[Int64] = []
  let mut i = 0
  while i < n0 {
    res.push(0L)
    i = i + 1
  }
  // (1 - q^m)^e = Σ_k C(e,k) (-1)^k q^{mk}
  let mut k = 0
  while k * m < n0 {
    let c = binom_i64(e, k)
    let sign = if k % 2 == 0 { 1L } else { -1L }
    res[k * m] = res[k * m] + sign * c
    k = k + 1
  }
  QSeries(res)
}

///|
/// Discriminant form Δ = q ∏_{n≥1} (1-q^n)^24 mod q^N.
pub fn delta_series(n0 : Int32) -> QSeries {
  let one : Array[Int64] = []
  let mut i = 0
  while i < n0 {
    one.push(0L)
    i = i + 1
  }
  one[0] = 1L
  let mut acc = QSeries(one)
  let mut m = 1
  while m < n0 {
    acc = acc.mul(eta_factor(m, 24, n0))
    m = m + 1
  }
  // multiply by q: shift
  let res : Array[Int64] = []
  res.push(0L)
  let mut j = 0
  while j < n0 - 1 {
    res.push(acc.coeff(j))
    j = j + 1
  }
  QSeries(res)
}

///|
/// Eisenstein series E4 = 1 + 240 Σ σ₃(n) q^n mod q^N.
pub fn e4_series(n0 : Int32) -> QSeries {
  let res : Array[Int64] = []
  let mut n = 0
  while n < n0 {
    if n == 0 {
      res.push(1L)
    } else {
      res.push(240L * sigma(n, 3))
    }
    n = n + 1
  }
  QSeries(res)
}

///|
/// Eisenstein series E6 = 1 − 504 Σ σ₅(n) q^n mod q^N.
pub fn e6_series(n0 : Int32) -> QSeries {
  let res : Array[Int64] = []
  let mut n = 0
  while n < n0 {
    if n == 0 {
      res.push(1L)
    } else {
      res.push(-504L * sigma(n, 5))
    }
    n = n + 1
  }
  QSeries(res)
}

///|
/// Hecke operator T_m on weight-k forms, applied to coefficient array f:
/// a_n(T_m f) = Σ_{d | gcd(m, n)} d^{k−1} · a_{m n / d²}.
/// Result truncated to the same length; missing coefficients treated as 0.
pub fn hecke_operator(f : Array[Int64], m : Int32, k : Int32) -> Array[Int64] {
  let n0 = f.length()
  let res : Array[Int64] = []
  let mut n = 0
  while n < n0 {
    let mut acc = 0L
    let mut d = 1
    while d * d <= m {
      if m % d == 0 {
        // d is a divisor; pair with m/d
        if n % d == 0 {
          let idx = m * n / (d * d)
          if idx < n0 {
            acc = acc + pow64(d.to_int64(), k - 1) * f[idx]
          }
        }
        let d2 = m / d
        if d2 != d && n % d2 == 0 {
          let idx2 = m * n / (d2 * d2)
          if idx2 < n0 {
            acc = acc + pow64(d2.to_int64(), k - 1) * f[idx2]
          }
        }
      }
      d = d + 1
    }
    res.push(acc)
    n = n + 1
  }
  res
}
