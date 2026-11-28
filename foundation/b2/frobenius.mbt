///|
/// frobenius.mbt — 32. 弗羅貝尼烏斯元素 (Frobenius elements)
///
/// (a) Arithmetic Frobenius φ: x ↦ x^q generates Gal(F_{q^n}/F_q) ≅ Z/n;
///     fixed field of φ^k = F_{q^gcd(k,n)}.
/// (b) Frobenius at p in Gal(Q(ζ_n)/Q) ≅ (Z/n)^× is the class p mod n;
///     its order = residue degree of p in Q(ζ_n).
///
/// Theorem engine:
///   T32a (Frobenius 生成元): ord(φ) = n；φ^k 的固定域 = F_{q^{gcd(k,n)}}
///   T32b (軌道-穩定子): φ 作用的軌道長 = n/gcd(k, n)（對 x ∈ F_{q^n}）
///   T32c (分歧類域論): f(p 在 Q(ζ_n)/Q) = ord_n(p)

///|
/// Verify x^{q^k} = x for all x in GF(q, n) iff gcd(k, n) = n... returns the
/// size of the fixed field of φ^k (elements with x^{q^k} = x).
pub fn frobenius_fixed_field_size(p : Int32, n : Int32, k : Int32) -> Int32 {
  let fld = GF::make(p, n)
  let q = fld.q()
  let pk = pow_int(p, k) // φ^k: x ↦ x^{p^k}
  let mut count = 0
  let mut x = 0
  while x < q {
    if fld.pow(x, pk) == x {
      count = count + 1
    }
    x = x + 1
  }
  count
}

///|
/// Order of arithmetic Frobenius (smallest m > 0 with x^{q^m} = x ∀x).
pub fn frobenius_order(p : Int32, n : Int32) -> Int32 {
  let fld = GF::make(p, n)
  let q = fld.q()
  let mut m = 1
  while m <= n {
    let qm = pow_int(p, m)
    let mut all = true
    // check on a generator set: just check all elements (small fields)
    let mut x = 0
    while x < q {
      if fld.pow(x, qm) != x {
        all = false
        x = q
      } else {
        x = x + 1
      }
    }
    if all {
      return m
    }
    m = m + 1
  }
  abort("frobenius_order: not found")
}

///|
/// Multiplicative order of a mod m (gcd(a, m) = 1): smallest k with a^k ≡ 1.
pub fn mult_order(a : Int32, m : Int32) -> Int32 {
  let mut k = 1
  let mut cur = (a % m + m) % m
  while cur != 1 {
    cur = cur * (a % m + m) % m % m
    k = k + 1
    if k > m * m {
      return -1
    }
  }
  k
}

///|
/// Order of p mod n = residue degree of p in Q(ζ_n)/Q (Frobenius = p mod n).
pub fn frobenius_in_cyclotomic(p : Int32, n : Int32) -> Int32 {
  if gcd_int(p, n) != 1 {
    return -1 // ramified
  }
  mult_order(p, n)
}

///|
/// Factorization pattern of p in Q(ζ_n): p splits into g primes of degree f
/// with f = ord_n(p), g = φ(n)/f. Returns (f, g).
pub fn prime_split_cyclotomic(p : Int32, n : Int32) -> (Int32, Int32) {
  let f = frobenius_in_cyclotomic(p, n)
  if f <= 0 {
    (-1, -1)
  } else {
    (f, euler_phi(n) / f)
  }
}

///|
/// Element count check: fixed field of φ^k has q^{gcd(k, n)} elements.
pub fn fixed_field_theorem_ok(p : Int32, n : Int32, k : Int32) -> Bool {
  // Fix(φ^k) = F_{p^{gcd(k, n)}}: size = p^{gcd(k, n)}
  let expected = pow_int(p, gcd_int(k, n))
  frobenius_fixed_field_size(p, n, k) == expected
}
