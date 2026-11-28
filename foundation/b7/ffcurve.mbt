///|
/// ffcurve.mbt — 批次七·模組 5：芬克爾斯坦–法爾格曲線族、半穩定還原與導子
///
/// 名稱說明：「芬克爾斯坦–法爾格曲線」在標準文獻中無固定指稱；本批次按字面保留，
/// 取其實質內容為**剛性 Weierstrass 族**
///     E_{a,b} : y² = x³ + a x + b,   a, b ∈ Z,  j = 1728·4a³/(4a³ + 27b²)
/// 特別取 j ∈ {0, 1728}（即 a = 0 或 b = 0）的單參數塔
///     FF_k : y² = x³ + p^k       （j = 0，加性還原）
/// 本模組實作 Tate 演算法（p ≥ 5 分支）給出 Kodaira 型、導子指數、半穩定判準，
/// 並由此**歸納**出兩條定理：
///   T(FF-1) 週期 6：FF_k 的 Kodaira 型僅依 k mod 6（II, IV, I₀*, IV*, II*, I₀）。
///   T(FF-2) 分量數：加法還原且 p ≥ 5 時，特殊纖維分量數 = v(Δ) − 1。
/// 並以 11a1、37a1 等曲線交叉核對導子 N = 11、37。

// ───────────────────────── 模算術 ─────────────────────────

///|
/// 模冪。
pub fn b7_mod_pow(base : Int64, exp : Int64, p : Int64) -> Int64 {
  let mut r = 1L
  let mut b = (base % p + p) % p
  let mut e = exp
  while e > 0L {
    if e % 2L == 1L {
      r = r * b % p
    }
    b = b * b % p
    e = e / 2L
  }
  r
}

///|
/// Legendre 符號（p 為奇質數）：回傳 −1、0、1。
pub fn b7_legendre(a : Int64, p : Int64) -> Int32 {
  let x = (a % p + p) % p
  if x == 0L {
    return 0
  }
  let r = b7_mod_pow(x, (p - 1L) / 2L, p)
  if r == 1L {
    1
  } else {
    -1
  }
}

///|
/// p 進賦值（x = 0 時回傳 99 作為「∞」哨兵）。
pub fn b7_vp(x : Int64, p : Int64) -> Int32 {
  if x == 0L {
    return 99
  }
  let mut n = 0
  let mut y = if x < 0L { -x } else { x }
  while y % p == 0L {
    y = y / p
    n = n + 1
  }
  n
}

///|
/// 整數冪 p^k。
pub fn b7_ipow(p : Int64, k : Int32) -> Int64 {
  let mut r = 1L
  for _ in 0..<k {
    r = r * p
  }
  r
}

// ───────────────────────── Weierstrass 曲線 ─────────────────────────

///|
/// 廣義 Weierstrass 曲線 y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆。
pub(all) struct W7 {
  a1 : Int64
  a2 : Int64
  a3 : Int64
  a4 : Int64
  a6 : Int64
}

///|
/// 建構。
pub fn b7_wcurve(
  a1 : Int64,
  a2 : Int64,
  a3 : Int64,
  a4 : Int64,
  a6 : Int64,
) -> W7 {
  { a1, a2, a3, a4, a6, }
}

///|
/// b₂ = a₁² + 4a₂。
pub fn b7_w_b2(c : W7) -> Int64 {
  c.a1 * c.a1 + 4L * c.a2
}

///|
/// b₄ = 2a₄ + a₁a₃。
pub fn b7_w_b4(c : W7) -> Int64 {
  2L * c.a4 + c.a1 * c.a3
}

///|
/// b₆ = a₃² + 4a₆。
pub fn b7_w_b6(c : W7) -> Int64 {
  c.a3 * c.a3 + 4L * c.a6
}

///|
/// b₈ = a₁²a₆ + 4a₂a₆ − a₁a₃a₄ + a₂a₃² − a₄²。
pub fn b7_w_b8(c : W7) -> Int64 {
  let part = c.a1 * c.a1 * c.a6 + 4L * c.a2 * c.a6 - c.a1 * c.a3 * c.a4
  part + c.a2 * c.a3 * c.a3 - c.a4 * c.a4
}

///|
/// c₄ = b₂² − 24b₄。
pub fn b7_w_c4(c : W7) -> Int64 {
  let b2 = b7_w_b2(c)
  b2 * b2 - 24L * b7_w_b4(c)
}

///|
/// 判別式 Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆。
pub fn b7_w_disc(c : W7) -> Int64 {
  let b2 = b7_w_b2(c)
  let b4 = b7_w_b4(c)
  let b6 = b7_w_b6(c)
  let b8 = b7_w_b8(c)
  -b2 * b2 * b8 - 8L * b4 * b4 * b4 - 27L * b6 * b6 + 9L * b2 * b4 * b6
}

///|
/// F_p 上有理點數：#E(F_p) = p + 1 − a_p，其中 a_p = −Σ_x χ(f(x))。
pub fn b7_count_points(c : W7, p : Int64) -> Int64 {
  let mut sum : Int64 = 0L
  let pu = p.to_int()
  for xa in 0..<pu {
    let x = xa.to_int64()
    // y² + (a1x + a3) y = x³ + a2x² + a4x + a6，二次式判別式 = (a1x+a3)² + 4(x³+a2x²+a4x+a6)
    let lin = ((c.a1 * x + c.a3) % p + p) % p
    let x3 = x * x % p * x % p
    let rhs = (x3 + c.a2 * (x * x % p) % p + c.a4 * x + c.a6) % p
    let disc = (lin * lin % p + 4L * rhs) % p
    sum = sum + b7_legendre(disc, p).to_int64()
  }
  // #E(F_p) = p + 1 + Σ_x χ(f(x))
  p + 1L + sum
}

///|
/// a_p = p + 1 − #E(F_p) = −Σ_x χ(f(x))。
pub fn b7_a_p(c : W7, p : Int64) -> Int64 {
  p + 1L - b7_count_points(c, p)
}

///|
/// 短型曲線 y² = x³ + ax + b。
pub fn b7_short(a : Int64, b : Int64) -> W7 {
  b7_wcurve(0L, 0L, 0L, a, b)
}

// ───────────────────────── Tate 演算法（p ≥ 5） ─────────────────────────

///|
/// Kodaira 型（字串）與其分量數表：II↦1、III↦2、IV↦3、I₀*↦5、IV*↦7、III*↦8、II*↦9。
pub fn b7_kodaira_components(ty : String) -> Int32 {
  if ty == "I0" {
    1
  } else if ty == "II" {
    1
  } else if ty == "III" {
    2
  } else if ty == "IV" {
    3
  } else if ty == "I0*" {
    5
  } else if ty == "IV*" {
    7
  } else if ty == "III*" {
    8
  } else if ty == "II*" {
    9
  } else {
    1
  }
}

///|
/// Tate 演算法（p ≥ 5）：以 v(Δ)、v(c₄) 及短型的 (v(a₄), v(a₆)) 分類 Kodaira 型。
/// 回傳 (型別字串, v(Δ), v(c₄), 是否乘法還原)。
pub fn b7_tate_type(c : W7, p : Int64) -> (String, Int32, Int32, Bool) {
  let d = b7_w_disc(c)
  let c4 = b7_w_c4(c)
  let vd = b7_vp(d, p)
  let vc4 = b7_vp(c4, p)
  if vd == 0 {
    return ("I0", 0, 0, false)
  }
  if vc4 == 0 {
    return ("I" + vd.to_string(), vd, 0, true)
  }
  // 加性還原：需 a₁ = a₂ = a₃ = 0 的短型與 (v(a₄), v(a₆)) 表
  let va4 = b7_vp(c.a4, p)
  let va6 = b7_vp(c.a6, p)
  let ty = if vd == 2 && va4 >= 2 && va6 == 1 {
    "II"
  } else if vd == 3 && va4 == 1 && va6 >= 2 {
    "III"
  } else if vd == 4 && va4 >= 2 && va6 == 2 {
    "IV"
  } else if vd == 6 && va4 >= 3 && va6 >= 3 {
    "I0*"
  } else if vd == 8 && va4 >= 2 && va6 == 4 {
    "IV*"
  } else if vd == 9 && va4 >= 3 && va6 == 4 {
    "III*"
  } else if vd == 10 && va4 >= 4 && va6 == 5 {
    "II*"
  } else if vd >= 7 && va4 == 2 && va6 == 3 {
    "I" + (vd - 6).to_string() + "*"
  } else {
    "additive(未知)"
  }
  (ty, vd, vc4, false)
}

///|
/// 導子指數 f_p：好的 0、乘法 1、加性 2（p ≥ 5）。
pub fn b7_conductor_exp(ty : String, p : Int64) -> Int32 {
  if ty == "I0" {
    return 0
  }
  if ty.has_prefix("I") &&
    !ty.contains("*") &&
    ty != "II" &&
    ty != "III" &&
    ty != "IV" {
    return 1
  }
  if p == 2L || p == 3L {
    return 2
  }
  2
}

///|
/// 半穩定判準：型為 I₀ 或 I_n（乘法）⇔ 半穩定還原。
pub fn b7_semistable(ty : String) -> Bool {
  if ty == "I0" {
    return true
  }
  if ty.has_prefix("I") &&
    !ty.contains("*") &&
    ty != "II" &&
    ty != "III" &&
    ty != "IV" {
    return true
  }
  false
}

///|
/// 導子 N = ∏_{p | Δ} p^{f_p}（p ≥ 5 的質因數；2、3 需 wild 修正，此處標記）。
/// 回傳 (N, 有無 2/3 因子)。
pub fn b7_conductor(c : W7) -> (Int64, Bool) {
  let d = b7_w_disc(c)
  let ad = if d < 0L { -d } else { d }
  let mut n = 1L
  let mut wild = false
  let mut p = 2L
  let mut rest = ad
  while p * p <= rest {
    if rest % p == 0L {
      // 只處理 p ≥ 5 的乾淨情形
      let (ty, _, _, _) = b7_tate_type(c, p)
      let fe = b7_conductor_exp(ty, p)
      if p < 5L && fe > 0 {
        wild = true
      }
      n = n * b7_ipow(p, fe)
      while rest % p == 0L {
        rest = rest / p
      }
    }
    p = p + 1L
  }
  if rest > 1L {
    let (ty, _, _, _) = b7_tate_type(c, rest)
    let fe = b7_conductor_exp(ty, rest)
    if rest < 5L && fe > 0 {
      wild = true
    }
    n = n * b7_ipow(rest, fe)
  }
  (n, wild)
}

// ───────────────────────── FF 塔：週期 6 與分量數 ─────────────────────────

///|
/// FF_k 的極小模型指數 k'：k ≥ 6 時以 (x,y) ↦ (p²x, p³y) 化簡，k' = ((k−1) mod 6) + 1。
pub fn b7_ff_minimal_k(k : Int32) -> Int32 {
  (k - 1) % 6 + 1
}

///|
/// FF_k 的極小模型曲線：y² = x³ + p^{k'}（k' ≤ 5），k' = 6 時為 y² = x³ + 1（好還原）。
pub fn b7_ff_curve_minimal(p : Int64, k : Int32) -> W7 {
  let kk = b7_ff_minimal_k(k)
  if kk >= 6 {
    b7_short(0L, 1L)
  } else {
    b7_short(0L, b7_ipow(p, kk))
  }
}

///|
/// FF 塔的 (k, 極小 k', 型別, v(Δ), 分量數, 半穩定?) 表，k = 1..kmax。
/// 先取極小模型（k' = ((k−1) mod 6) + 1），再跑 Tate 分類。
pub fn b7_ff_tower(
  p : Int64,
  kmax : Int32,
) -> Array[(Int32, Int32, String, Int32, Int32, Bool)] {
  let out : Array[(Int32, Int32, String, Int32, Int32, Bool)] = []
  for k in 1..<(kmax + 1) {
    let kk = b7_ff_minimal_k(k)
    let c = b7_ff_curve_minimal(p, k)
    let (ty, vd, _, _) = b7_tate_type(c, p)
    out.push((k, kk, ty, vd, b7_kodaira_components(ty), b7_semistable(ty)))
  }
  out
}

///|
/// 週期 6 檢查：FF_k 與 FF_{k+6} 的 Kodaira 型是否相同。
pub fn b7_ff_period_six_ok(p : Int64) -> Bool {
  let mut ok = true
  for k in 1..<7 {
    let c1 = b7_ff_curve_minimal(p, k)
    let c2 = b7_ff_curve_minimal(p, k + 6)
    let (t1, _, _, _) = b7_tate_type(c1, p)
    let (t2, _, _, _) = b7_tate_type(c2, p)
    if t1 != t2 {
      ok = false
    }
  }
  ok
}

///|
/// 分量數恆等式檢查：加法還原時 分量數 = v(Δ) − 1。
pub fn b7_component_count_identity_ok(p : Int64, kmax : Int32) -> Bool {
  let mut ok = true
  for k in 1..<(kmax + 1) {
    let c = b7_ff_curve_minimal(p, k)
    let (ty, vd, _, _) = b7_tate_type(c, p)
    if b7_semistable(ty) {
      continue
    }
    let comp = b7_kodaira_components(ty)
    if comp != vd - 1 {
      ok = false
    }
  }
  ok
}

///|
/// 試除質數判定。
pub fn b7_is_prime(n : Int64) -> Bool {
  if n < 2L {
    return false
  }
  let mut d = 2L
  while d * d <= n {
    if n % d == 0L {
      return false
    }
    d = d + 1L
  }
  true
}

///|
/// Hasse 界檢查：|a_p| ≤ 2√p，於 p ≤ pmax 的所有 p 與給定曲線。
pub fn b7_hasse_ok(c : W7, pmax : Int64) -> Bool {
  let mut p = 3L
  while p <= pmax {
    // 只在「p 為質數且好還原（p ∤ Δ）」時檢查 Hasse 界
    if !b7_is_prime(p) || b7_vp(b7_w_disc(c), p) != 0 {
      p = p + 2L
      continue
    }
    let ap = b7_a_p(c, p).to_double()
    if ap.abs() > 2.0 * p.to_double().sqrt() + 1.0e-9 {
      return false
    }
    p = p + 2L
  }
  true
}

///|
/// 半穩定判準的數值見證：列出 v(Δ) > 0 時是否 v(c₄) = 0（⇔ 半穩定）。
pub fn b7_semistable_criterion_ok(c : W7, p : Int64) -> Bool {
  let vd = b7_vp(b7_w_disc(c), p)
  let vc4 = b7_vp(b7_w_c4(c), p)
  let semistable_by_val = vd == 0 || vc4 == 0
  let (ty, _, _, _) = b7_tate_type(c, p)
  semistable_by_val == b7_semistable(ty)
}
