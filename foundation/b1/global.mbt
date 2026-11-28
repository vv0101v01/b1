///|
/// global.mbt — 整體域 (global fields)：Q、二次域 K = Q(√d)、函數域 F_2(t)
/// Places, valuations, absolute values, and the product formula.
///
/// Theorem engine (verified computationally below):
///   T1 (乘積公式 Product formula): 對 x ∈ K^×, ∏_v |x|_v = 1.

///|
/// Valuation of a rational r at prime p: exponent of p in r's factorization.
pub fn rat_valuation(r : Rat, p : Int64) -> Int32 {
  let mut v = 0
  let mut n = r.0
  let mut d = r.1
  if n == 0L {
    return 0
  }
  while n % p == 0L {
    n = n / p
    v = v + 1
  }
  while d % p == 0L {
    d = d / p
    v = v - 1
  }
  v
}

///|
/// Absolute value |r|_p = p^{-v_p(r)}.
pub fn rat_abs_p(r : Rat, p : Int64) -> Rat {
  let v = rat_valuation(r, p)
  if v >= 0 {
    Rat(1L, pow64(p, v))
  } else {
    Rat(pow64(p, -v), 1L)
  }
}

///|
/// Product formula for Q: |r|_∞ · ∏_p |r|_p = 1 (exact, in Rat).
/// Returns the exact product, which must equal 1 for r ≠ 0.
pub fn product_formula_rat(r : Rat) -> Rat {
  if r.is_zero() {
    abort("product_formula_rat: zero has no product formula")
  }
  let mut acc = r.abs()
  // finite primes: only primes dividing num or den matter
  let mut ns = factorize(if r.0 < 0L { -r.0 } else { r.0 })
  let ds = factorize(r.1)
  // merge primes
  let primes : Array[Int64] = []
  for (p, _) in ns {
    primes.push(p)
  }
  for (p, _) in ds {
    let mut seen = false
    for q in primes {
      if q == p {
        seen = true
      }
    }
    if !seen {
      primes.push(p)
    }
  }
  ns = []
  for p in primes {
    acc = acc.mul(rat_abs_p(r, p))
  }
  acc
}

///|
/// Element of quadratic field K = Q(√d): a + b√d with a, b ∈ Q.
pub(all) struct QuadElem(Int64, Rat, Rat)

///|
pub fn QuadElem::make(d : Int64, a : Rat, b : Rat) -> QuadElem {
  QuadElem(d, a, b)
}

///|
/// Norm N(x) = (a+b√d)(a-b√d) = a² - d·b² ∈ Q.
pub fn QuadElem::norm(self : QuadElem) -> Rat {
  self.1.mul(self.1).sub(Rat(self.0, 1L).mul(self.2.mul(self.2)))
}

///|
/// Trace Tr(x) = 2a.
pub fn QuadElem::trace(self : QuadElem) -> Rat {
  self.1.add(self.1)
}

///|
pub fn QuadElem::add(self : QuadElem, other : QuadElem) -> QuadElem {
  QuadElem(self.0, self.1.add(other.1), self.2.add(other.2))
}

///|
pub fn QuadElem::mul(self : QuadElem, other : QuadElem) -> QuadElem {
  // (a+b√d)(c+e√d) = ac + d·b·e + (ae + bc)√d
  let ac = self.1.mul(other.1)
  let dbe = Rat(self.0, 1L).mul(self.2.mul(other.2))
  let ae = self.1.mul(other.2)
  let bc = self.2.mul(other.1)
  QuadElem(self.0, ac.add(dbe), ae.add(bc))
}

///|
pub fn QuadElem::to_string(self : QuadElem) -> String {
  "\{self.1.to_string()} + \{self.2.to_string()}·√\{self.0}"
}

///|
/// Product formula for a quadratic field element x ≠ 0:
/// ∏_v |x|_v = |σ1(x)| · |σ2(x)| · ∏_p ∏_{w|p} |x|_w = 1, computed exactly.
/// Archimedean product = |N(x)|; finite part groups as p^{-v_p(N(x))}.
/// Returns the exact product as Rat (must be 1).
pub fn product_formula_quad(x : QuadElem) -> Rat {
  let n = x.norm()
  if n.is_zero() {
    abort("product_formula_quad: zero element")
  }
  let nabs = n.abs()
  let mut acc = nabs
  // finite places: ∏_{w|p} |x|_w = p^{-v_p(N(x))}
  let fnum = factorize(if nabs.0 < 0L { -nabs.0 } else { nabs.0 })
  let fden = factorize(nabs.1)
  let primes : Array[Int64] = []
  for (p, _) in fnum {
    primes.push(p)
  }
  for (p, _) in fden {
    let mut seen = false
    for q in primes {
      if q == p {
        seen = true
      }
    }
    if !seen {
      primes.push(p)
    }
  }
  for p in primes {
    acc = acc.mul(rat_abs_p(nabs, p))
  }
  acc
}

///|
/// Divisor of a rational r ≠ 0: array of (p, v_p(r)) for finite primes plus
/// the infinite place recorded as (0, ...) is omitted; returns finite part.
pub fn rat_divisor(r : Rat) -> Array[(Int64, Int32)] {
  let res : Array[(Int64, Int32)] = []
  let ns = factorize(if r.0 < 0L { -r.0 } else { r.0 })
  let ds = factorize(r.1)
  let primes : Array[Int64] = []
  for (p, _) in ns {
    primes.push(p)
  }
  for (p, _) in ds {
    let mut seen = false
    for q in primes {
      if q == p {
        seen = true
      }
    }
    if !seen {
      primes.push(p)
    }
  }
  // sort primes ascending (insertion sort)
  let mut i = 1
  while i < primes.length() {
    let key = primes[i]
    let mut j = i - 1
    while j >= 0 && primes[j] > key {
      primes[j + 1] = primes[j]
      j = j - 1
    }
    primes[j + 1] = key
    i = i + 1
  }
  for p in primes {
    res.push((p, rat_valuation(r, p)))
  }
  res
}

///|
/// Function field F_2[t]: polynomials as bitmasks (bit i = coefficient of t^i).
/// Irreducible list up to degree 4 for divisor computations.
pub fn ff2_irreducibles() -> Array[(Int32, Int32)] {
  // (bitmask, degree)
  [(2, 1), (3, 1), (7, 2), (11, 3), (13, 3), (19, 4), (25, 4), (31, 4)]
}

///|
/// Degree of an F_2 polynomial (bitmask), -1 for zero.
pub fn ff2_deg(f : Int32) -> Int32 {
  let mut d = -1
  let mut m = f
  while m > 0 {
    d = d + 1
    m = m / 2
  }
  d
}

///|
/// Polynomial multiplication over F_2 (bitmask, no reduction).
pub fn ff2_mul(f : Int32, g : Int32) -> Int32 {
  let mut acc = 0
  let mut b = g
  let mut i = 0
  while b > 0 {
    if b % 2 == 1 {
      acc = acc ^ (f * pow_int(2, i))
    }
    b = b / 2
    i = i + 1
  }
  acc
}

///|
/// Polynomial division with remainder over F_2: returns (quotient, remainder).
pub fn ff2_divmod(f : Int32, g : Int32) -> (Int32, Int32) {
  let dg = ff2_deg(g)
  if dg < 0 {
    abort("ff2_divmod: division by zero polynomial")
  }
  let mut q = 0
  let mut r = f
  while ff2_deg(r) >= dg && r != 0 {
    let shift = ff2_deg(r) - dg
    q = q ^ pow_int(2, shift)
    r = r ^ (g * pow_int(2, shift))
  }
  (q, r)
}

///|
/// Valuation of f at monic irreducible g: largest e with g^e | f.
pub fn ff2_valuation(f : Int32, g : Int32) -> Int32 {
  if f == 0 {
    abort("ff2_valuation: zero polynomial")
  }
  let mut e = 0
  let mut m = f
  let mut more = true
  while more {
    let (_, r) = ff2_divmod(m, g)
    if r == 0 {
      m = ff2_divmod(m, g).0
      e = e + 1
    } else {
      more = false
    }
  }
  e
}

///|
/// Product formula for x = f/g in F_2(t)^×:
/// Σ_v deg(v)·v(x) = 0, summed over all places v of F_2(t) (finite irreducibles
/// dividing f or g, plus the place at infinity with v_∞(x) = deg(g) - deg(f)).
/// Returns the exact integer Σ (must be 0).
pub fn ff2_product_formula(f : Int32, g : Int32) -> Int32 {
  if f == 0 || g == 0 {
    abort("ff2_product_formula: zero numerator or denominator")
  }
  let mut s = 0
  let mut cof_f = f
  let mut cof_g = g
  for (irr, dg) in ff2_irreducibles() {
    let vf = ff2_valuation(f, irr)
    let vg = ff2_valuation(g, irr)
    s = s + dg * (vf - vg)
    let mut i = 0
    while i < vf {
      cof_f = ff2_divmod(cof_f, irr).0
      i = i + 1
    }
    let mut j = 0
    while j < vg {
      cof_g = ff2_divmod(cof_g, irr).0
      j = j + 1
    }
  }
  if cof_f != 1 || cof_g != 1 {
    abort(
      "ff2_product_formula: polynomial has irreducible factor of degree > 4",
    )
  }
  // place at infinity: v_inf = deg(g) - deg(f), deg(infinity) = 1
  let v_inf = ff2_deg(g) - ff2_deg(f)
  s + v_inf
}
