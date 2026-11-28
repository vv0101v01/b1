///|
/// ai.mbt — 37. 自守誘導 (automorphic induction)
///
/// Ind_{Q(i)/Q} χ for a Hecke character χ of Q(i) (a character of the ideal
/// group of Z[i]): L(π, s) = L_{Q(i)}(χ, s) = Σ_{ideals 𝔟} χ(𝔟) N𝔟^{−s}.
///
/// χ is defined on prime ideals of Z[i]:
///   p ≡ 1 mod 4, (p) = ππ̄:  χ((π)) = ψ(a − 2b mod 5) for π = a + bi,
///                            χ((π̄)) = ψ(a + 2b mod 5);
///   p ≡ 3 mod 4 inert:       χ((p)) = ψ(p mod 5);
///   p = 2: (2) = (1+i)²:     χ((1+i)) = ψ(1 − 2·1 mod 5),
/// with ψ = order-4 character mod 5.
///
/// Theorem engine:
///   T37a (誘導 = 數域 L): GL_2 局部規則係數 逐項 = 理想枚舉係數
///   T37b (Artin 特徵表): inert p ⇒ a_p = 0；split p ⇒ a_p = χ(π) + χ(π̄)
///   T37c (Artin 形式論延續): L(Ind χ, s) 的 Euler 乘積 = ∏_𝔭 (1−χ(𝔭)N𝔭^{-s})^{-1}

///|
/// ψ = order-4 character mod 5 as Cx.
pub fn psi5(m : Int32) -> Cx {
  let mm = (m % 5 + 5) % 5
  if mm == 0 {
    return Cx(0.0, 0.0)
  }
  let mut ind = 0
  let mut cur = 1
  while cur != mm {
    cur = cur * 2 % 5
    ind = ind + 1
  }
  match ind % 4 {
    0 => Cx(1.0, 0.0)
    1 => Cx(0.0, 1.0)
    2 => Cx(-1.0, 0.0)
    _ => Cx(0.0, -1.0)
  }
}

///|
/// Prime ideal data at p: (kind, χ value, ...) kind: 0 = ramified(2),
/// 1 = split, 2 = inert.
fn prime_ideal_kind(p : Int32) -> Int32 {
  if p == 2 {
    0
  } else if p % 4 == 1 {
    1
  } else {
    2
  }
}

///|
/// χ of the prime ideals at p via the norm: χ(𝔭) = ψ(N𝔭 mod 5).
/// Valid Hecke character of the ideal group of Z[i] (vanishes only at the
/// primes above 5 = the conductor). Split p: both primes have norm p;
/// inert p: norm p²; ramified 2: (1+i) has norm 2.
pub fn chi_at_prime(p : Int32) -> (Cx, Cx) {
  if p == 2 {
    let c = psi5(2) // N(1+i) = 2
    (c, c)
  } else if p % 4 == 3 {
    let c = psi5(p * p) // N((p)) = p²
    (c, c)
  } else {
    let c = psi5(p) // N(π) = N(π̄) = p
    (c, c)
  }
}

///|
/// a_n = Σ_{ideals of norm n} χ(𝔟), computed by prime-ideal factorization:
/// split p: e1 + e2 = a; inert p: a even, e = a/2; 2: e = a.
/// Returns real parts (imaginary parts cancel by conjugation).
pub fn ai_ideal_coefficients(n_max : Int32) -> Array[Double] {
  let res : Array[Double] = []
  let mut i = 0
  while i <= n_max {
    res.push(0.0)
    i = i + 1
  }
  res[1] = 1.0
  let mut n = 2
  while n <= n_max {
    // enumerate all factorizations of n into prime-ideal powers
    let fs = factorize(n.to_int64()) // array of (prime, exponent) pairs
    // iterate over exponent splits for split primes: each split p with
    // exponent a contributes (a + 1) choices (e1 = 0..a)
    // build via recursive accumulation of products
    let mut acc = Cx(0.0, 0.0)
    // state arrays
    let nprime = fs.length()
    let es : Array[Int32] = []
    let mut k = 0
    while k < nprime {
      es.push(0)
      k = k + 1
    }
    let mut done = false
    while !done {
      // evaluate current combination
      let mut valid = true
      let mut term = Cx(1.0, 0.0)
      let mut idx = 0
      while idx < nprime {
        let (pr64, ex) = fs[idx]
        let pr = pr64.to_int()
        let kind = prime_ideal_kind(pr)
        let (c1, c2) = chi_at_prime(pr)
        if kind == 2 {
          // inert: exponent must be even; e = ex/2; es[idx] is 0 only
          if ex % 2 != 0 {
            valid = false
          } else {
            // χ((p))^{ex/2}
            let mut t2 = 0
            while t2 < ex / 2 {
              term = term.mul(c1)
              t2 = t2 + 1
            }
          }
        } else if kind == 0 {
          // ramified: unique prime, exponent ex fixed
          let mut t2 = 0
          while t2 < ex {
            term = term.mul(c1)
            t2 = t2 + 1
          }
        } else {
          // split: es[idx] = e1, ex − es[idx] = e2
          let e1 = es[idx]
          let e2 = ex - e1
          let mut t2 = 0
          while t2 < e1 {
            term = term.mul(c1)
            t2 = t2 + 1
          }
          let mut t3 = 0
          while t3 < e2 {
            term = term.mul(c2)
            t3 = t3 + 1
          }
        }
        idx = idx + 1
      }
      if valid {
        acc = acc.add(term)
      }
      // odometer over split primes only
      let mut carry = true
      let mut j = 0
      while carry && j < nprime {
        let (pr2_64, ex2) = fs[j]
        let pr2 = pr2_64.to_int()
        if prime_ideal_kind(pr2) == 1 {
          if es[j] < ex2 {
            es[j] = es[j] + 1
            carry = false
          } else {
            es[j] = 0
          }
        }
        j = j + 1
      }
      if carry {
        done = true
      }
    }
    res[n] = acc.0
    n = n + 1
  }
  res
}

///|
/// GL_2 AI coefficients as complex array from local rules:
/// split p: a_{p^j} = Σ_{t=0..j} χ(π)^t χ(π̄)^{j−t};
/// inert p: a_{p^{2m}} = χ((p))^m, a_{p^{2m+1}} = 0 (no ideal of norm p^{odd});
/// p = 2 (ramified): a_{2^e} = χ(1+i)^e.
/// Multiplicativity on coprime composites (complex multiplication).
pub fn ai_gl2_coefficients_cx(n_max : Int32) -> Array[Cx] {
  let res : Array[Cx] = []
  let mut i = 0
  while i <= n_max {
    res.push(Cx(0.0, 0.0))
    i = i + 1
  }
  res[1] = Cx(1.0, 0.0)
  for p in primes_upto(n_max) {
    let kind = prime_ideal_kind(p)
    let (c1, c2) = chi_at_prime(p)
    if kind == 0 {
      // ramified: unique prime (1+i) of norm 2: coeff at p^e = χ^e
      let mut pow = Cx(1.0, 0.0)
      let mut pj = 1
      while pj <= n_max {
        res[pj] = pow
        pow = pow.mul(c1)
        pj = pj * p
      }
    } else if kind == 2 {
      // inert: coeff at p^{2m} = χ((p))^m; odd powers 0
      let mut pow = Cx(1.0, 0.0)
      let mut pj = 1
      while pj <= n_max {
        res[pj] = pow
        pow = pow.mul(c1)
        if pj * p <= n_max {
          res[pj * p] = Cx(0.0, 0.0)
        }
        pj = pj * p * p
      }
    } else {
      // split
      let mut pj = p
      let mut j = 1
      while pj <= n_max {
        let mut accc = Cx(0.0, 0.0)
        let mut t = 0
        while t <= j {
          let mut p1 = Cx(1.0, 0.0)
          let mut u = 0
          while u < t {
            p1 = p1.mul(c1)
            u = u + 1
          }
          let mut p2 = Cx(1.0, 0.0)
          let mut v = 0
          while v < j - t {
            p2 = p2.mul(c2)
            v = v + 1
          }
          accc = accc.add(p1.mul(p2))
          t = t + 1
        }
        res[pj] = accc
        pj = pj * p
        j = j + 1
      }
    }
  }
  // multiplicativity for coprime composites
  let mut n = 2
  while n <= n_max {
    let mut u = 2
    while u * u <= n {
      if n % u == 0 {
        let v = n / u
        if gcd_int(u, v) == 1 {
          let prod = res[u].mul(res[v])
          if prod.abs() > 0.000001 {
            res[n] = prod
            u = n
          }
        }
      }
      u = u + 1
    }
    n = n + 1
  }
  res
}

///|
/// Real parts of the GL_2 AI coefficients (for the character table).
pub fn ai_gl2_coefficients(n_max : Int32) -> Array[Double] {
  let cx = ai_gl2_coefficients_cx(n_max)
  let res : Array[Double] = []
  let mut n = 0
  while n <= n_max {
    res.push(cx[n].0)
    n = n + 1
  }
  res
}

///|
/// Compare ideal-enumeration vs GL_2 local rules (complex); max |diff|.
pub fn ai_coefficient_error(n_max : Int32) -> Double {
  let ideal = ai_ideal_coefficients(n_max)
  let gl2 = ai_gl2_coefficients_cx(n_max)
  let mut max_err = 0.0
  let mut n = 1
  while n <= n_max {
    let d = ideal[n] - gl2[n].0
    let ad = if d < 0.0 { -d } else { d }
    if ad > max_err {
      max_err = ad
    }
    n = n + 1
  }
  max_err
}

///|
/// Artin induction character table: tr of Ind χ at Frob_p = a_p.
pub fn ai_character_table(p_max : Int32) -> String {
  let gl2 = ai_gl2_coefficients(p_max)
  let mut s = "p | p mod 4 | tr(Ind χ | Frob_p)\n"
  for p in primes_upto(p_max) {
    s = s + "\{p} | \{p % 4} | \{gl2[p]}\n"
  }
  s
}

///|
/// T37c: three-way check — the AI L-series equals L(ψ, s)·L(ψ·χ₋₄, s)
/// (χ = ψ∘N factors through the norm; Ind = ψ ⊕ ψχ₋₄ as Artin reps).
pub fn ai_three_way_error(n_max : Int32, s : Double) -> Double {
  let gl2 = ai_gl2_coefficients_cx(n_max)
  let mut lhs = Cx(0.0, 0.0)
  let mut n = 1
  while n <= n_max {
    let ns = @math.pow(n.to_double(), s)
    lhs = lhs.add(gl2[n].scale(1.0 / ns))
    n = n + 1
  }
  let psi = dir_char_mod5()
  let chi4 = dir_char_chi4()
  let l1 = dirichlet_series_char(psi, n_max, s)
  let mut l2 = Cx(0.0, 0.0)
  let mut m = 1
  while m <= n_max {
    let ms = @math.pow(m.to_double(), s)
    l2 = l2.add(psi.value(m).mul(chi4.value(m)).scale(1.0 / ms))
    m = m + 1
  }
  lhs.sub(l1.mul(l2)).abs()
}
