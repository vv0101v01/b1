///|
/// elliptic.mbt — 一般 Weierstrass 橢圓曲線的群律（在 GF(p^k) 上）
/// General Weierstrass: y² + a1·xy + a3·y = x³ + a2·x² + a4·x + a6
/// (needed for mod-p point counts at p = 2, 3 and for ℓ-torsion).
/// Shared foundation for ℓ-進表示 (31), Frobenius (32), JL (38), 模性 (40).

///|
/// Weierstrass coefficients (a1, a2, a3, a4, a6).
pub(all) struct WCurve(Int32, Int32, Int32, Int32, Int32)

///|
/// A point (x, y) on the curve over GF(p, k); infinity flag.
pub(all) struct ECPoint(Int32, Int32, Bool)

///|
pub fn ECPoint::infinity() -> ECPoint {
  ECPoint(0, 0, true)
}

///|
/// Is x a point on the curve over the given field?
pub fn WCurve::on_curve(self : WCurve, pt : ECPoint, fld : GF) -> Bool {
  if pt.2 {
    return true
  }
  let x = pt.0
  let y = pt.1
  let p = fld.p
  let a1 = (self.0 % p + p) % p
  let a2 = (self.1 % p + p) % p
  let a3 = (self.2 % p + p) % p
  let a4 = (self.3 % p + p) % p
  let a6 = (self.4 % p + p) % p
  let lhs = fld.add(
    fld.add(fld.mul(y, y), fld.mul(fld.mul(a1, x), y)),
    fld.mul(a3, y),
  )
  let rhs = fld.add(
    fld.add(fld.mul(fld.mul(x, x), x), fld.mul(fld.mul(a2, x), x)),
    fld.add(fld.mul(a4, x), a6),
  )
  lhs == rhs
}

///|
/// Negation: −(x, y) = (x, −y − a1x − a3).
pub fn WCurve::neg(self : WCurve, pt : ECPoint, fld : GF) -> ECPoint {
  if pt.2 {
    return pt
  }
  let p = fld.p
  let a1 = (self.0 % p + p) % p
  let a3 = (self.2 % p + p) % p
  let ny = fld.neg(fld.add(fld.add(fld.mul(a1, pt.0), pt.1), fld.mul(a3, 1)))
  ECPoint(pt.0, ny, false)
}

///|
/// Group law (general Weierstrass formulas): addition of two points.
pub fn WCurve::add(
  self : WCurve,
  p1 : ECPoint,
  p2 : ECPoint,
  fld : GF,
) -> ECPoint {
  if p1.2 {
    return p2
  }
  if p2.2 {
    return p1
  }
  let p = fld.p
  let a1 = (self.0 % p + p) % p
  let a2 = (self.1 % p + p) % p
  let a3 = (self.2 % p + p) % p
  let a4 = (self.3 % p + p) % p
  let x1 = p1.0
  let y1 = p1.1
  let x2 = p2.0
  let y2 = p2.1
  // slope
  let lam = if x1 == x2 && y1 == y2 {
    // doubling: λ = (3x² + 2a2x + a4 − a1y) / (2y + a1x + a3)
    let num = fld.add(
      fld.add(fld.mul(fld.mul(3 % p, x1), x1), fld.mul(fld.mul(2 % p, a2), x1)),
      fld.add(fld.mul(a4, 1), fld.neg(fld.mul(a1, y1))),
    )
    let den = fld.add(
      fld.add(fld.mul(2 % p, y1), fld.mul(a1, x1)),
      fld.mul(a3, 1),
    )
    if den == 0 {
      return ECPoint::infinity()
    }
    fld.mul(num, fld.inv(den))
  } else {
    // chord: λ = (y2 − y1) / (x2 − x1)
    let den = fld.sub(x2, x1)
    if den == 0 {
      return ECPoint::infinity()
    }
    fld.mul(fld.sub(y2, y1), fld.inv(den))
  }
  // x3 = λ² + a1λ − a2 − x1 − x2
  let x3 = fld.add(
    fld.add(fld.mul(lam, lam), fld.mul(a1, lam)),
    fld.add(fld.neg(a2), fld.neg(fld.add(x1, x2))),
  )
  // y3 = λ(x1 − x3) − y1 − a1x3 − a3
  let y3 = fld.add(
    fld.mul(lam, fld.sub(x1, x3)),
    fld.add(fld.neg(y1), fld.neg(fld.add(fld.mul(a1, x3), fld.mul(a3, 1)))),
  )
  ECPoint(x3, y3, false)
}

///|
/// Scalar multiplication n·P (double-and-add).
pub fn WCurve::mul(self : WCurve, n : Int32, pt : ECPoint, fld : GF) -> ECPoint {
  let mut acc = ECPoint::infinity()
  let mut base = pt
  let mut e = n
  if e < 0 {
    base = self.neg(base, fld)
    e = -e
  }
  while e > 0 {
    if e % 2 == 1 {
      acc = self.add(acc, base, fld)
    }
    base = self.add(base, base, fld)
    e = e / 2
  }
  acc
}

///|
/// Count points over GF(p, k) by brute force (plus infinity).
pub fn WCurve::count_points(self : WCurve, p : Int32, k : Int32) -> Int32 {
  let fld = GF::make(p, k)
  let q = fld.q()
  if p == 2 {
    // brute force in characteristic 2 (quadratic formula fails)
    let mut count = 1
    let mut x = 0
    while x < q {
      let mut y = 0
      while y < q {
        if self.on_curve(ECPoint(x, y, false), fld) {
          count = count + 1
        }
        y = y + 1
      }
      x = x + 1
    }
    return count
  }
  // O(q) via the quadratic formula in y: y² + B y + C = 0 with
  // B = a1·x + a3, C = −(x³ + a2x² + a4x + a6); #solutions = 1 + χ(disc),
  // disc = B² − 4C = B² + 4·rhs.
  let mut count = 1 // infinity
  let mut x = 0
  while x < q {
    let a1 = (self.0 % p + p) % p
    let a2 = (self.1 % p + p) % p
    let a3 = (self.2 % p + p) % p
    let a4 = (self.3 % p + p) % p
    let a6 = (self.4 % p + p) % p
    let b = fld.add(fld.mul(a1, x), a3)
    let rhs = fld.add(
      fld.add(fld.mul(fld.mul(x, x), x), fld.mul(fld.mul(a2, x), x)),
      fld.add(fld.mul(a4, x), a6),
    )
    let four = fld.add(fld.add(1 % p, 1 % p), fld.add(1 % p, 1 % p))
    let disc = fld.add(fld.mul(b, b), fld.mul(four, rhs))
    let c = fld.chi(disc)
    count = count + 1 + c
    x = x + 1
  }
  count
}

///|
/// Trace of Frobenius a_p = p + 1 − #E(F_p).
pub fn WCurve::trace(self : WCurve, p : Int32) -> Int32 {
  p + 1 - self.count_points(p, 1)
}

///|
/// Singular check via discriminant (general formula), over F_p.
pub fn WCurve::is_nonsingular(self : WCurve, p : Int32) -> Bool {
  let a1 = (self.0 % p + p) % p
  let a2 = (self.1 % p + p) % p
  let a3 = (self.2 % p + p) % p
  let a4 = (self.3 % p + p) % p
  let a6 = (self.4 % p + p) % p
  let b2 = (a1 * a1 + 4 * a2) % p
  let b4 = (2 * a4 + a1 * a3) % p
  let b6 = (a3 * a3 + 4 * a6) % p
  let b8 = (a1 * a1 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4) %
    p
  let disc = (
      (-b2 * b2 * b8 - 8 * b4 * b4 * b4 - 27 * b6 * b6 * 1) % p +
      9 * b2 * b4 * b6
    ) %
    p
  let mut d = disc % p
  if d < 0 {
    d = d + p
  }
  d != 0
}

///|
/// All points of E over GF(p, k) (array; used for torsion search).
pub fn WCurve::all_points(
  self : WCurve,
  p : Int32,
  k : Int32,
) -> Array[ECPoint] {
  let fld = GF::make(p, k)
  let q = fld.q()
  let res : Array[ECPoint] = []
  res.push(ECPoint::infinity())
  let mut x = 0
  while x < q {
    let mut y = 0
    while y < q {
      if self.on_curve(ECPoint(x, y, false), fld) {
        res.push(ECPoint(x, y, false))
      }
      y = y + 1
    }
    x = x + 1
  }
  res
}
