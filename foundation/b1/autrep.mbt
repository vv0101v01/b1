///|
/// autrep.mbt — 自守表示 (automorphic representations)：Hecke 代數、Satake 參數、L-函數
///
/// Theorem engine:
///   T22 (Satake/Ramanujan–Petersson): |a_p| < 2 p^{(k−1)/2}；|α_p| = p^{(k−1)/2}
///   T23 (Euler 乘積 = Dirichlet 級數): L(f, s) = Σ a_n n^{−s} = ∏_p (1−α_p p^{−s})^{-1}(1−β_p p^{−s})^{-1}
///   T24 (Hecke 代數結構): T_p² = T_{p²} + p^{k−1}·id（球面 Hecke 代數的 Satake 同構）

///|
/// Complex number as (re, im) pair of Doubles.
pub(all) struct Cx(Double, Double)

///|
pub fn Cx::add(self : Cx, other : Cx) -> Cx {
  Cx(self.0 + other.0, self.1 + other.1)
}

///|
pub fn Cx::sub(self : Cx, other : Cx) -> Cx {
  Cx(self.0 - other.0, self.1 - other.1)
}

///|
pub fn Cx::mul(self : Cx, other : Cx) -> Cx {
  Cx(self.0 * other.0 - self.1 * other.1, self.0 * other.1 + self.1 * other.0)
}

///|
pub fn Cx::scale(self : Cx, c : Double) -> Cx {
  Cx(self.0 * c, self.1 * c)
}

///|
pub fn Cx::abs(self : Cx) -> Double {
  (self.0 * self.0 + self.1 * self.1).sqrt()
}

///|
pub fn Cx::to_string(self : Cx) -> String {
  "\{fmt6(self.0)} + \{fmt6(self.1)}i"
}

///|
/// Satake parameters (α, β) of a weight-k level-1 eigenform at prime p:
/// roots of x² − a_p x + p^{k−1} = 0. Returns (α, β) as complex conjugates
/// when the discriminant is negative (Ramanujan–Petersson regime).
pub fn satake_params(a_p : Double, p : Int32, k : Int32) -> (Cx, Cx) {
  let pk = pow64(p.to_int64(), k - 1).to_double()
  let disc = a_p * a_p - 4.0 * pk
  if disc < 0.0 {
    let re = a_p / 2.0
    let im = (-disc).sqrt() / 2.0
    (Cx(re, im), Cx(re, -im))
  } else {
    let sq = disc.sqrt()
    (Cx((a_p + sq) / 2.0, 0.0), Cx((a_p - sq) / 2.0, 0.0))
  }
}

///|
/// Ramanujan–Petersson bound check: |a_p| < 2·p^{(k−1)/2}.
pub fn ramanujan_ok(a_p : Double, p : Int32, k : Int32) -> Bool {
  let bound = 2.0 * @math.pow(p.to_double(), (k - 1).to_double() / 2.0)
  let a = if a_p < 0.0 { -a_p } else { a_p }
  a < bound
}

///|
/// Dirichlet series partial sum Σ_{n=1}^{m} a_n n^{−s} (Double).
pub fn dirichlet_partial(a : Array[Int64], m : Int32, s : Double) -> Double {
  let mut acc = 0.0
  let mut n = 1
  while n <= m && n < a.length() {
    acc = acc + a[n].to_double() / @math.pow(n.to_double(), s)
    n = n + 1
  }
  acc
}

///|
/// Euler product partial product ∏_{p ≤ pmax} (1 − a_p p^{−s} + p^{k−1} p^{−2s})^{−1}.
pub fn euler_partial(
  a : Array[Int64],
  pmax : Int32,
  s : Double,
  k : Int32,
) -> Double {
  let mut acc = 1.0
  for p in primes_upto(pmax) {
    if p < a.length() {
      let ps = @math.pow(p.to_double(), s)
      let pk = pow64(p.to_int64(), k - 1).to_double()
      let factor = 1.0 - a[p].to_double() / ps + pk / (ps * ps)
      acc = acc / factor
    }
  }
  acc
}

///|
/// Hecke structure check on coefficient array: verify T_p² = T_{p²} + p^{k−1} id,
/// i.e. applying T_p twice equals applying T_{p²} plus p^{k−1}·identity,
/// on the first m coefficients. Returns max absolute difference.
pub fn hecke_structure_error(
  f : Array[Int64],
  p : Int32,
  k : Int32,
  m : Int32,
) -> Int64 {
  let t_p = hecke_operator(f, p, k)
  let t_p2 = hecke_operator(t_p, p, k)
  let t_pp = hecke_operator(f, p * p, k)
  // comparison range clamped so all needed source indices are in range
  let mut m2 = m
  while m2 > 0 && p * p * m2 >= f.length() {
    m2 = m2 - 1
  }
  let mut max_err = 0L
  let mut n = 1
  while n <= m2 {
    let lhs = t_p2[n]
    let rhs = t_pp[n] + pow64(p.to_int64(), k - 1) * f[n]
    let diff = if lhs > rhs { lhs - rhs } else { rhs - lhs }
    if diff > max_err {
      max_err = diff
    }
    n = n + 1
  }
  max_err
}

///|
/// Commutativity check: T_m ∘ T_n = T_n ∘ T_m on the first m coefficients.
/// Returns max absolute difference.
pub fn hecke_commutativity_error(
  f : Array[Int64],
  m1 : Int32,
  n1 : Int32,
  k : Int32,
  m : Int32,
) -> Int64 {
  let a = hecke_operator(hecke_operator(f, m1, k), n1, k)
  let b = hecke_operator(hecke_operator(f, n1, k), m1, k)
  // clamp: source index m1·n1·i must be < f.length()
  let mut m2 = m
  while m2 > 0 && m1 * n1 * m2 >= f.length() {
    m2 = m2 - 1
  }
  let mut max_err = 0L
  let mut i = 1
  while i <= m2 {
    let diff = if a[i] > b[i] { a[i] - b[i] } else { b[i] - a[i] }
    if diff > max_err {
      max_err = diff
    }
    i = i + 1
  }
  max_err
}

///|
/// Full Hecke relation check: T_m T_n = Σ_{d | gcd(m, n)} d^{k−1} T_{mn/d²}.
/// Returns max absolute difference on the first m coefficients.
pub fn hecke_relation_error(
  f : Array[Int64],
  m1 : Int32,
  n1 : Int32,
  k : Int32,
  m : Int32,
) -> Int64 {
  let lhs = hecke_operator(hecke_operator(f, m1, k), n1, k)
  // build RHS
  let n0 = f.length()
  let rhs : Array[Int64] = []
  let mut i = 0
  while i < n0 {
    rhs.push(0L)
    i = i + 1
  }
  // clamp comparison range
  let mut m2 = m
  while m2 > 0 && m1 * n1 * m2 >= n0 {
    m2 = m2 - 1
  }
  let g = gcd_int(m1, n1)
  let mut d = 1
  while d * d <= g {
    if g % d == 0 {
      let d2 = g / d
      // term d^{k-1} T_{m1 n1 / d²}
      let mm1 = m1 * n1 / (d * d)
      let t1 = hecke_operator(f, mm1, k)
      let c1 = pow64(d.to_int64(), k - 1)
      let mut j = 0
      while j < n0 {
        rhs[j] = rhs[j] + c1 * t1[j]
        j = j + 1
      }
      if d2 != d {
        let mm2 = m1 * n1 / (d2 * d2)
        let t2 = hecke_operator(f, mm2, k)
        let c2 = pow64(d2.to_int64(), k - 1)
        let mut j2 = 0
        while j2 < n0 {
          rhs[j2] = rhs[j2] + c2 * t2[j2]
          j2 = j2 + 1
        }
      }
    }
    d = d + 1
  }
  let mut max_err = 0L
  let mut i2 = 1
  while i2 <= m2 {
    let diff = if lhs[i2] > rhs[i2] {
      lhs[i2] - rhs[i2]
    } else {
      rhs[i2] - lhs[i2]
    }
    if diff > max_err {
      max_err = diff
    }
    i2 = i2 + 1
  }
  max_err
}
