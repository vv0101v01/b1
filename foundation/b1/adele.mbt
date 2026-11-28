///|
/// adele.mbt — 阿代爾環 (adele ring) 與伊代爾群 (idele group)
///
/// A_Q = R × ∏'_p Q_p (restricted product w.r.t. Z_p):
/// almost all finite components lie in Z_p. An adele is stored as
/// (finite components, real component, bound): for primes p > bound the
/// component is understood to lie in Z_p (val ≥ 0).
///
/// Theorem engine:
///   T5 (主阿代爾離散性/乘積公式): 對 r ∈ Q^×, 對角嵌入的 |r|_∞ ∏_p |r|_p = 1
///   T6 (伊代爾範數): 對主伊代爾 x ∈ Q^×, ||x|| = 1
///   T7 (Ẑ^× 結構): (Z/NZ)^× ≅ ∏ (Z/p^e Z)^× (CRT), φ 積性

///|
/// A finite adele of Q: sorted array of (p, PAdic) finite components,
/// the real component, and the bound (components at p > bound lie in Z_p).
pub(all) struct Adele(Array[(Int64, PAdic)], Double, Int64)

///|
/// Lookup finite component at p (missing component = 0 in Q_p).
fn Adele::component(self : Adele, p : Int64) -> PAdic {
  // find the working precision: use any stored component's prec, default 20
  let mut prec = 20
  for (_, pa) in self.0 {
    prec = pa.prec
    break
  }
  for (q, pa) in self.0 {
    if q == p {
      return pa
    }
  }
  PAdic::zero(p, prec)
}

///|
/// The zero adele.
pub fn Adele::zero() -> Adele {
  Adele([], 0.0, 1L)
}

///|
/// Diagonal embedding of a rational r into A_Q.
/// Finite components: v_p(r) with |r|_p; real component: r.
pub fn Adele::from_rat(r : Rat) -> Adele {
  let parts = rat_divisor(r)
  let fin : Array[(Int64, PAdic)] = []
  for (p, _) in parts {
    let pa = PAdic::from_rat(r, p, 20)
    fin.push((p, pa))
  }
  // also record valuations for primes dividing num/den; from_rat handles them
  // bound: largest prime appearing (or 1)
  let mut bound = 1L
  for (p, _) in parts {
    if p > bound {
      bound = p
    }
  }
  Adele(fin, r.to_double(), bound)
}

///|
/// Add two adeles (restricted product preserved: bound = max of bounds).
pub fn Adele::add(self : Adele, other : Adele) -> Adele {
  let fin : Array[(Int64, PAdic)] = []
  let bound = if self.2 > other.2 { self.2 } else { other.2 }
  // collect all primes up to bound appearing in either side
  let pr : Array[Int64] = []
  for (p, _) in self.0 {
    pr.push(p)
  }
  for (p, _) in other.0 {
    let mut seen = false
    for q in pr {
      if q == p {
        seen = true
      }
    }
    if !seen {
      pr.push(p)
    }
  }
  for p in pr {
    if p <= bound {
      let a = self.component(p)
      let b = other.component(p)
      let s = a.add(b)
      fin.push((p, s))
    }
  }
  // sort by p (insertion)
  let mut i = 1
  while i < fin.length() {
    let key = fin[i]
    let mut j = i - 1
    while j >= 0 && fin[j].0 > key.0 {
      fin[j + 1] = fin[j]
      j = j - 1
    }
    fin[j + 1] = key
    i = i + 1
  }
  Adele(fin, self.1 + other.1, bound)
}

///|
/// Idele: an adele with all components nonzero; finite components form a
/// restricted product w.r.t. Z_p^× (units almost everywhere).
pub(all) struct Idele(Array[(Int64, PAdic)], Double, Int64)

///|
/// Diagonal embedding Q^× → J_Q (principal idele).
pub fn Idele::from_rat(r : Rat) -> Idele {
  if r.is_zero() {
    abort("Idele::from_rat: zero")
  }
  let parts = rat_divisor(r)
  let fin : Array[(Int64, PAdic)] = []
  let mut bound = 1L
  for (p, _) in parts {
    let pa = PAdic::from_rat(r, p, 20)
    fin.push((p, pa))
    if p > bound {
      bound = p
    }
  }
  Idele(fin, r.to_double(), bound)
}

///|
/// Idele multiplication (componentwise).
pub fn Idele::mul(self : Idele, other : Idele) -> Idele {
  let fin : Array[(Int64, PAdic)] = []
  let bound = if self.2 > other.2 { self.2 } else { other.2 }
  let pr : Array[Int64] = []
  for (p, _) in self.0 {
    pr.push(p)
  }
  for (p, _) in other.0 {
    let mut seen = false
    for q in pr {
      if q == p {
        seen = true
      }
    }
    if !seen {
      pr.push(p)
    }
  }
  for p in pr {
    let mut a = PAdic::zero(p, 20)
    let mut b = PAdic::zero(p, 20)
    for (q, pa) in self.0 {
      if q == p {
        a = pa
      }
    }
    for (q, pb) in other.0 {
      if q == p {
        b = pb
      }
    }
    // at least one side may have missing component = unit 1? missing = value 1
    // careful: missing component means the rational had no p in divisor ⇒ unit
    let mut av = a
    let mut bv = b
    if a.is_zero() {
      av = PAdic::from_int(1L, p, 20)
    }
    if b.is_zero() {
      bv = PAdic::from_int(1L, p, 20)
    }
    fin.push((p, av.mul(bv)))
  }
  Idele(fin, self.1 * other.1, bound)
}

///|
/// Idele norm ||x|| = |x|_∞ ∏_p |x|_p (finite product since |x|_p = 1 for
/// almost all p). Returns the product as Double.
pub fn Idele::norm(self : Idele) -> Double {
  let mut acc = if self.1 < 0.0 { -self.1 } else { self.1 }
  for (_, pa) in self.0 {
    acc = acc * pa.abs()
  }
  acc
}

///|
/// Verify the product formula on a principal idele exactly in Rat:
/// ||x|| must be 1. Returns the exact product |r|_∞ ∏_p |r|_p as Rat.
pub fn Idele::norm_exact_principal(r : Rat) -> Rat {
  product_formula_rat(r)
}

///|
/// Euler phi function.
pub fn euler_phi(n : Int32) -> Int32 {
  let mut count = 0
  let mut i = 1
  while i <= n {
    if gcd_int(i, n) == 1 {
      count = count + 1
    }
    i = i + 1
  }
  count
}

///|
/// CRT structure check: |(Z/NZ)^×| = ∏_{p^e || N} |(Z/p^e Z)^×|,
/// and |(Z/p^e Z)^×| = p^e - p^{e-1}. Returns true iff both hold.
pub fn crt_unit_structure(n : Int32) -> Bool {
  let phi_n = euler_phi(n)
  let fs = factorize(n.to_int64())
  let mut prod = 1
  for (p64, e) in fs {
    let p = p64.to_int()
    let pe = pow_int(p, e)
    prod = prod * (pe - pe / p)
  }
  phi_n == prod
}

///|
/// Count of unit ideles in the box ∏_{p ≤ B} (Z/pZ)^× with real component in
/// [1, 2): equals ∏_{p ≤ B} (p-1) — the group Ẑ^× ≅ ∏_p Z_p^× truncated.
pub fn zhat_units_truncated(bound : Int32) -> Int32 {
  let mut acc = 1
  for p in primes_upto(bound) {
    acc = acc * (p - 1)
  }
  acc
}
