///|
/// 184. Deeply ramified supercuspidal representations — finite model.
/// (a) conductor exponents of characters of (Z/25)^* w.r.t. the unit
/// filtration U^a = 1 + 5^a: deep = conductor exponent 2;
/// (b) GL(2) criterion on F_{25}^* = Z/24: ψ ≠ ψ^q (non-Galois-invariant)
/// ⟺ supercuspidal induction irreducible; orbits under Galois give
/// (q²−q)/2 = 10 Weil-induced supercuspidals (q = 5).

///|
/// conductor exponent of χ_m on (Z/25)^* (generator 2, order 20):
/// c = min{a : χ_m trivial on U^a}; U⁰ = all, U¹ = 1+5Z (ind = 4Z/20),
/// U² = {1}
pub fn cond25(m : Int32) -> Int32 {
  let mm = (m % 20 + 20) % 20
  if mm == 0 {
    0
  } else if mm % 5 == 0 {
    1
  } else {
    2
  }
}

///|
/// T184a: conductor distribution on (Z/25)^*: counts (c=0,1,2) = (1,3,16);
/// deep characters (c = 2) = 16 = 20 − 4 = #chars nontrivial on U¹.
pub fn deep_conductor_ok() -> Bool {
  let mut c0 = 0
  let mut c1 = 0
  let mut c2 = 0
  for m in 0..<20 {
    let c = cond25(m)
    if c == 0 {
      c0 = c0 + 1
    } else if c == 1 {
      c1 = c1 + 1
    } else {
      c2 = c2 + 1
    }
  }
  c0 == 1 && c1 == 3 && c2 == 16
}

///|
/// T184b: Galois action ψ ↦ ψ^q on chars of F_{25}^* = Z/24: ψ_m^5 = ψ_{5m}:
/// invariant ⟺ 6 | m. Non-invariant count = 20; orbits = 10 = (q²−q)/2.
pub fn supercuspidal_orbits_ok() -> Bool {
  let mut invariant = 0
  let mut noninv = 0
  for m in 0..<24 {
    if 5 * m % 24 == m {
      invariant = invariant + 1
    } else {
      noninv = noninv + 1
    }
  }
  // orbit walk on the NON-invariant set: pair ψ_m with ψ_{5m}
  let seen : Array[Bool] = []
  for _i in 0..<24 {
    seen.push(false)
  }
  let mut orbits = 0
  for m in 0..<24 {
    if !seen[m] {
      seen[m] = true
      let m2 = 5 * m % 24
      seen[m2] = true
      if m % 6 != 0 {
        // non-invariant Galois orbit {m, 5m} = one Weil-induced supercuspidal
        orbits = orbits + 1
      }
    }
  }
  invariant == 4 && noninv == 20 && orbits == 10
}

///|
/// T184c: irreducibility criterion: ψ ≠ ψ^q on the non-invariant set;
/// for every m with 6 ∤ m the induction is irreducible (ψ_m^5 ≠ ψ_m).
pub fn supercuspidal_irred_ok() -> Bool {
  let mut ok = true
  for m in 0..<24 {
    let is_sc = m % 6 != 0
    let noninv = 5 * m % 24 != m
    if is_sc != noninv {
      ok = false
    }
  }
  ok
}

///|
/// T184d: deep ⟺ nontrivial on U¹ = 1+5Z/25 (index 8 generates U¹):
/// χ_m(6) = 2^{8m} ≠ 1 ⟺ 5 ∤ m
pub fn deep_via_unit_ok() -> Bool {
  let mut ok = true
  for m in 0..<20 {
    // 6 = 2^8 mod 25: χ_m(6) = ω^{8m} of order 20: trivial ⟺ 20 | 8m ⟺ 5 | m
    let trivial_on_u1 = 8 * m % 20 == 0
    let not_deep = cond25(m) <= 1
    if trivial_on_u1 != not_deep {
      ok = false
    }
  }
  ok
}

///|
/// 184: deeply ramified supercuspidal package
pub fn supercuspidal_ok() -> Bool {
  deep_conductor_ok() &&
  supercuspidal_orbits_ok() &&
  supercuspidal_irred_ok() &&
  deep_via_unit_ok()
}
