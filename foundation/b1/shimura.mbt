///|
/// shimura.mbt — 志村簇 (Shimura varieties) 的可計算模型：
///   (1) GL_1 的志村集 = 類群 Cl(K)（虛二次域）
///   (2) 二元二次型約化 ↔ 類群元素
///   (3) Hilbert 類多項式 H_D：次數 = h(D)，根 = 奇異模數 (singular moduli)
///   (4) 模曲線上的 CM 點；橢圓曲線 j-不變量計數
///
/// Theorem engine:
///   T8 (類數公式/約化型計數): h(D) = #{本原約化正定二次型 disc = D}
///   T9 (Hilbert 類多項式): deg H_D = h(D)，H_D ∈ Z[X]，生成 Hilbert 類域
///   T10 (j-不變量參數化): #Ell(F_p)/≅ = p（每個 j ∈ F_p 恰一條曲線）

///|
/// A primitive positive definite binary quadratic form ax² + bxy + cy².
pub(all) struct QForm(Int32, Int32, Int32)

///|
pub fn QForm::disc(self : QForm) -> Int32 {
  self.1 * self.1 - 4 * self.0 * self.2
}

///|
/// Whether a form is reduced: |b| ≤ a ≤ c, and b ≥ 0 if |b| = a or a = c.
pub fn QForm::is_reduced(self : QForm) -> Bool {
  let a = self.0
  let b = self.1
  let c = self.2
  if a <= 0 || c <= 0 {
    return false
  }
  let ab = if b < 0 { -b } else { b }
  if ab > a {
    return false
  }
  if a > c {
    return false
  }
  if ab == a || a == c {
    return b >= 0
  }
  true
}

///|
/// Class number h(D) for fundamental discriminant D < 0: count primitive
/// reduced positive definite forms of discriminant D.
/// Primitive means gcd(a, b, c) = 1.
pub fn class_number_forms(d : Int32) -> Int32 {
  if d >= 0 {
    abort("class_number_forms: need D < 0")
  }
  reduced_forms(d).length()
}

///|
/// List all reduced forms of discriminant D (as (a, b, c)).
pub fn reduced_forms(d : Int32) -> Array[QForm] {
  let res : Array[QForm] = []
  if d >= 0 {
    return res
  }
  // reduced: |b| ≤ a ≤ c, b ≡ D (mod 2), |b| ≤ sqrt(|D|/3)
  let bd = if d % 2 == 0 { 0 } else { 1 }
  let max_b = isqrt64((if d < 0 { -d } else { d }).to_int64() / 3L).to_int() + 1
  let mut b = -max_b
  if (b % 2 + 2) % 2 != bd {
    b = b + 1
  }
  while b <= max_b {
    let b2sq = b * b
    let num = b2sq - d
    if num % 4 == 0 {
      let n4 = num / 4
      let mut a = if b < 0 { -b } else { b }
      if a == 0 {
        a = 1
      }
      while a * a <= n4 {
        if n4 % a == 0 {
          let c = n4 / a
          let g = gcd_int(gcd_int(a, if b < 0 { -b } else { b }), c)
          let form = QForm(a, b, c)
          if g == 1 && form.is_reduced() {
            res.push(form)
          }
        }
        a = a + 1
      }
    }
    b = b + 2
  }
  res
}

///|
/// Hilbert class polynomial table: (D, coefficients of H_D, low to high).
/// H_{-20} = X² - 1264000X - 681472000 (class number 2: the roots generate
/// the real quadratic class field Q(√5)).
pub fn hilbert_class_polynomials() -> Array[(Int32, Array[Int64])] {
  [
    (-3, [0L, 1L]),
    (-4, [-1728L, 1L]),
    (-7, [3375L, 1L]),
    (-8, [-8000L, 1L]),
    (-11, [32768L, 1L]),
    (-19, [884736L, 1L]),
    (-20, [-681472000L, -1264000L, 1L]),
    (-24, [14670139392L, -4834944L, 1L]),
  ]
}

///|
/// Elliptic curve over F_p: y² = x³ + ax + b, with 4a³ + 27b² ≠ 0 (mod p).
/// Stored as (a, b); the prime p is passed to the methods.
pub(all) struct ECurve(Int32, Int32)

///|
/// Discriminant condition: 4a³ + 27b² ≢ 0 mod p.
pub fn ECurve::is_nonsingular(self : ECurve, p : Int32) -> Bool {
  let a = (self.0 % p + p) % p
  let b = (self.1 % p + p) % p
  let d = (4 * pow_int(a, 3) + 27 * b * b) % p
  d != 0
}

///|
/// j-invariant mod p: 1728 · 4a³ / (4a³ + 27b²) mod p.
pub fn ECurve::j_inv(self : ECurve, p : Int32) -> Int32 {
  let a = (self.0 % p + p) % p
  let b = (self.1 % p + p) % p
  let num = 1728 * 4 * pow_int(a, 3) % p
  let den = (4 * pow_int(a, 3) + 27 * b * b) % p
  let inv = mod_inverse(den.to_int64(), p.to_int64()).to_int()
  num * inv % p
}

///|
/// Count points on E over F_p (including the point at infinity) by brute force.
pub fn ECurve::point_count(self : ECurve, p : Int32) -> Int32 {
  let a = (self.0 % p + p) % p
  let b = (self.1 % p + p) % p
  let mut count = 1 // infinity
  let mut x = 0
  while x < p {
    let rhs = (pow_int(x, 3) + a * x + b) % p
    // count y with y² = rhs
    let mut y = 0
    let mut seen = 0
    while y < p {
      if y * y % p == rhs {
        seen = seen + 1
      }
      y = y + 1
    }
    count = count + seen
    x = x + 1
  }
  count
}

///|
/// Number of distinct j-invariants of elliptic curves over F_p — the moduli
/// stack of elliptic curves over F_p has exactly p points (all j ∈ F_p).
pub fn count_j_invariants(p : Int32) -> Int32 {
  let js : Array[Int32] = []
  let mut a = 0
  while a < p {
    let mut b = 0
    while b < p {
      let e = ECurve(a, b)
      if e.is_nonsingular(p) {
        let j = e.j_inv(p)
        let mut seen = false
        for k in js {
          if k == j {
            seen = true
          }
        }
        if !seen {
          js.push(j)
        }
      }
      b = b + 1
    }
    a = a + 1
  }
  js.length()
}

///|
/// Hasse bound check: |#E(F_p) - (p+1)| ≤ 2√p.
pub fn hasse_ok(n : Int32, p : Int32) -> Bool {
  let diff = (n - (p + 1)).to_int64()
  let ad = if diff < 0L { -diff } else { diff }
  let bound = 2L * isqrt64(p.to_int64()) + 1L
  ad <= bound
}

///|
/// Supersingular test for p ≥ 5: a_p = #E - p - 1 = 0.
pub fn ECurve::is_supersingular(self : ECurve, p : Int32) -> Bool {
  if p < 5 {
    return false
  }
  self.point_count(p) == p + 1
}
