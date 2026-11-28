///|
/// galois.mbt — 有限域 GF(p^k) 的顯式算術
/// Explicit arithmetic in finite fields GF(p^k) = F_p[t]/(f).
/// Elements are encoded as Int: sum_{i<k} c_i p^i with c_i in [0, p).

///|
/// A finite field: prime p, extension degree k, irreducible polynomial coeffs
/// (coeffs[i] = coefficient of t^i, degree k, monic assumed).
pub(all) struct GF {
  p : Int32
  k : Int32
  coeffs : Array[Int32]
}

///|
/// Evaluate poly coeffs at t = x in F_p (Horner).
fn gf_eval_poly(coeffs : Array[Int32], x : Int32, p : Int32) -> Int32 {
  let mut acc = 0
  let mut i = coeffs.length() - 1
  while i >= 0 {
    acc = (acc * x + coeffs[i]) % p
    i = i - 1
  }
  acc
}

///|
/// Whether poly (as coeff array, leading coeff last nonzero) is irreducible over
/// F_p of degree k <= 4: check no root for deg 2/3, plus quadratic factor test
/// for deg 4.
fn gf_poly_irreducible(coeffs : Array[Int32], p : Int32) -> Bool {
  let k = coeffs.length() - 1
  if k <= 1 {
    return true
  }
  // no roots
  let mut x = 0
  while x < p {
    if gf_eval_poly(coeffs, x, p) == 0 {
      return false
    }
    x = x + 1
  }
  if k <= 3 {
    return true
  }
  if k == 4 {
    // test all monic quadratics g: if g | f then f reducible without roots
    let mut a = 0
    while a < p {
      let mut b = 0
      while b < p {
        // divide f by t^2 + a t + b and check remainder zero
        // f = c4 t^4 + c3 t^3 + c2 t^2 + c1 t + c0 (c4 = 1 monic)
        let r : Array[Int32] = []
        let mut i = 0
        while i < 5 {
          r.push(coeffs[i])
          i = i + 1
        }
        // synthetic division: reduce t^(n) = -a t^(n-1) - b t^(n-2) * ...
        let mut deg = 4
        while deg >= 2 {
          let c = r[deg] % p
          if c != 0 {
            r[deg] = 0
            r[deg - 1] = (r[deg - 1] - c * a) % p
            r[deg - 2] = (r[deg - 2] - c * b) % p
          }
          deg = deg - 1
        }
        let r0 = (r[0] % p + p) % p
        let r1 = (r[1] % p + p) % p
        if r0 == 0 && r1 == 0 {
          return false
        }
        b = b + 1
      }
      a = a + 1
    }
    return true
  }
  false
}

///|
/// Construct GF(p^k) by searching an irreducible polynomial (deterministic).
pub fn GF::make(p : Int32, k : Int32) -> GF {
  if k == 1 {
    return GF::{ p, k: 1, coeffs: [0, 1], }
  }
  // enumerate monic polynomials of degree k
  let total = pow_int(p, k)
  let mut idx = 0
  while idx < total {
    let coeffs : Array[Int32] = []
    let mut m = idx
    let mut i = 0
    while i < k {
      coeffs.push(m % p)
      m = m / p
      i = i + 1
    }
    coeffs.push(1) // monic
    if gf_poly_irreducible(coeffs, p) {
      return GF::{ p, k, coeffs, }
    }
    idx = idx + 1
  }
  abort("GF::make: no irreducible polynomial found")
}

///|
/// Number of elements q = p^k.
pub fn GF::q(self : GF) -> Int32 {
  pow_int(self.p, self.k)
}

///|
/// Decode element index into coefficient array.
pub fn GF::decode(self : GF, e : Int32) -> Array[Int32] {
  let res : Array[Int32] = []
  let mut m = e
  let mut i = 0
  while i < self.k {
    res.push(m % self.p)
    m = m / self.p
    i = i + 1
  }
  res
}

///|
/// Encode coefficient array (length k) into element index.
pub fn GF::encode(self : GF, cs : Array[Int32]) -> Int32 {
  let mut acc = 0
  let mut i = self.k - 1
  while i >= 0 {
    let mut c = cs[i] % self.p
    if c < 0 {
      c = c + self.p
    }
    acc = acc * self.p + c
    i = i - 1
  }
  acc
}

///|
/// Field addition of encoded elements.
pub fn GF::add(self : GF, x : Int32, y : Int32) -> Int32 {
  let a = self.decode(x)
  let b = self.decode(y)
  let res : Array[Int32] = []
  let mut i = 0
  while i < self.k {
    res.push((a[i] + b[i]) % self.p)
    i = i + 1
  }
  self.encode(res)
}

///|
/// Field subtraction.
pub fn GF::sub(self : GF, x : Int32, y : Int32) -> Int32 {
  let a = self.decode(x)
  let b = self.decode(y)
  let res : Array[Int32] = []
  let mut i = 0
  while i < self.k {
    let mut c = (a[i] - b[i]) % self.p
    if c < 0 {
      c = c + self.p
    }
    res.push(c)
    i = i + 1
  }
  self.encode(res)
}

///|
/// Field multiplication (polynomial mul reduced by irr).
pub fn GF::mul(self : GF, x : Int32, y : Int32) -> Int32 {
  let a = self.decode(x)
  let b = self.decode(y)
  // product coeffs up to degree 2k-2
  let prod : Array[Int32] = []
  let mut i = 0
  while i < 2 * self.k {
    prod.push(0)
    i = i + 1
  }
  let mut i2 = 0
  while i2 < self.k {
    let mut j = 0
    while j < self.k {
      prod[i2 + j] = (prod[i2 + j] + a[i2] * b[j]) % self.p
      j = j + 1
    }
    i2 = i2 + 1
  }
  // reduce modulo irr: t^k = -sum coeffs[i] t^i
  let mut deg = 2 * self.k - 2
  while deg >= self.k {
    let c = prod[deg]
    if c != 0 {
      let mut i3 = 0
      while i3 < self.k {
        let mut v = (prod[deg - self.k + i3] - c * self.coeffs[i3]) % self.p
        if v < 0 {
          v = v + self.p
        }
        prod[deg - self.k + i3] = v
        i3 = i3 + 1
      }
    }
    deg = deg - 1
  }
  let res : Array[Int32] = []
  let mut i4 = 0
  while i4 < self.k {
    res.push(prod[i4])
    i4 = i4 + 1
  }
  self.encode(res)
}

///|
/// Field negation.
pub fn GF::neg(self : GF, x : Int32) -> Int32 {
  self.sub(0, x)
}

///|
/// Multiplicative inverse via Fermat: x^(q-2). Returns 0 for x = 0.
pub fn GF::inv(self : GF, x : Int32) -> Int32 {
  if x == 0 {
    return 0
  }
  self.pow(x, self.q() - 2)
}

///|
/// Field power x^e (e >= 0).
pub fn GF::pow(self : GF, x : Int32, e : Int32) -> Int32 {
  let mut r = 1 % self.q()
  let mut base = x
  let mut ee = e
  while ee > 0 {
    if ee % 2 == 1 {
      r = self.mul(r, base)
    }
    base = self.mul(base, base)
    ee = ee / 2
  }
  r
}

///|
/// Whether x is a nonzero square (Euler criterion x^((q-1)/2) == 1).
pub fn GF::is_square(self : GF, x : Int32) -> Bool {
  if x == 0 {
    return true
  }
  self.pow(x, (self.q() - 1) / 2) == 1 % self.q()
}

///|
/// Quadratic character chi(x) in {1, -1, 0}.
pub fn GF::chi(self : GF, x : Int32) -> Int32 {
  if x == 0 {
    return 0
  }
  if self.is_square(x) {
    1
  } else {
    -1
  }
}
