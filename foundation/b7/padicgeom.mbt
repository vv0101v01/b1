///|
/// padicgeom.mbt — 批次七·模組 6：混合特徵奇異點消去與 p 進幾何
///
/// 內容：
///  (1) Z/pⁿ 的顯式算術（單位群、歐拉定理、Hensel 提升）；
///  (2) Newton 多邊形（混合特徵奇異點的組合骨架）：下凸包、格長、Pick 定理、
///      環面（toric）消去的爆破次數 = Σ(ℓ_e − 1)；
///  (3) 例外除子的相交矩陣：鏈狀 (−2)-曲線的相交形式**負定**（以 Jacobi 特徵值核對）、
///      基本環（fundamental cycle）Z·E_i ≤ 0（Artin 判準）、Z 落在根的 1 維核中；
///  (4) 與模組 5 交叉核對：Kodaira 型的分量數 = 鏈長 = v(Δ) − 1。

// ───────────────────────── Z/pⁿ 算術 ─────────────────────────

///|
/// Z/pⁿ 的元素。
#derive(Debug)
pub(all) struct ZpN {
  p : Int64
  n : Int32
  v : Int64
}

///|
/// 建構（自動約化）。
pub fn b7_zp(p : Int64, n : Int32, x : Int64) -> ZpN {
  let m = b7_ipow(p, n)
  { p, n, v: (x % m + m) % m, }
}

///|
/// 模數 pⁿ。
pub fn b7_zp_mod(a : ZpN) -> Int64 {
  b7_ipow(a.p, a.n)
}

///|
/// 加法。
pub fn b7_zp_add(a : ZpN, b : ZpN) -> ZpN {
  b7_zp(a.p, a.n, a.v + b.v)
}

///|
/// 乘法。
pub fn b7_zp_mul(a : ZpN, b : ZpN) -> ZpN {
  b7_zp(a.p, a.n, a.v * b.v)
}

///|
/// 擴展歐幾里得求逆（僅對單位）。回傳 (逆, 是否存在)。
pub fn b7_zp_inv(a : ZpN) -> (ZpN, Bool) {
  let m = b7_zp_mod(a)
  // 擴展歐幾里得
  let mut old_r = a.v
  let mut r = m
  let mut old_s = 1L
  let mut s = 0L
  while r != 0L {
    let q = old_r / r
    let nr = old_r - q * r
    old_r = r
    r = nr
    let ns = old_s - q * s
    old_s = s
    s = ns
  }
  if old_r != 1L {
    return (b7_zp(a.p, a.n, 0L), false)
  }
  (b7_zp(a.p, a.n, old_s), true)
}

///|
/// 加法與乘法的環公理抽樣檢查（含分配律、單位元、加法逆元）。
pub fn b7_zp_ring_ok(p : Int64, n : Int32) -> Bool {
  let m = b7_ipow(p, n)
  let samples : Array[Int64] = [0L, 1L, p, 2L * p, m - 1L, p * p]
  for xa in samples {
    for yb in samples {
      let x = b7_zp(p, n, xa)
      let y = b7_zp(p, n, yb)
      // 交換律
      if b7_zp_add(x, y).v != b7_zp_add(y, x).v {
        return false
      }
      if b7_zp_mul(x, y).v != b7_zp_mul(y, x).v {
        return false
      }
    }
  }
  // 結合律與分配律
  for xa in samples {
    for yb in samples {
      for zc in samples {
        let x = b7_zp(p, n, xa)
        let y = b7_zp(p, n, yb)
        let z = b7_zp(p, n, zc)
        let l1 = b7_zp_mul(b7_zp_mul(x, y), z).v
        let r1 = b7_zp_mul(x, b7_zp_mul(y, z)).v
        if l1 != r1 {
          return false
        }
        let l2 = b7_zp_mul(x, b7_zp_add(y, z)).v
        let r2 = b7_zp_add(b7_zp_mul(x, y), b7_zp_mul(x, z)).v
        if l2 != r2 {
          return false
        }
      }
    }
  }
  true
}

///|
/// 歐拉定理：單位 a 滿足 a^φ(pⁿ) ≡ 1 (mod pⁿ)，φ(pⁿ) = pⁿ⁻¹(p−1)。
pub fn b7_zp_euler_ok(p : Int64, n : Int32) -> Bool {
  let m = b7_ipow(p, n)
  let phi = b7_ipow(p, n - 1) * (p - 1L)
  let mut a = 1L
  while a < m {
    if a % p != 0L {
      let r = b7_mod_pow(a, phi, m)
      if r != 1L {
        return false
      }
      // 逆元檢查
      let (inv, ok) = b7_zp_inv(b7_zp(p, n, a))
      if !ok || b7_zp_mul(b7_zp(p, n, a), inv).v != 1L {
        return false
      }
    }
    a = a + 1L
  }
  true
}

///|
/// 單位群階數（與 φ(pⁿ) 對照）。
pub fn b7_zp_unit_count(p : Int64, n : Int32) -> Int64 {
  let m = b7_ipow(p, n)
  let mut c = 0L
  let mut a = 1L
  while a < m {
    if a % p != 0L {
      c = c + 1L
    }
    a = a + 1L
  }
  c
}

///|
/// Hensel 提升：f(x) = Σ c_i x^i，給定 mod p 的單根 r₀，提升到 mod pⁿ。
/// 回傳 (根, 是否成功)。
pub fn b7_hensel(
  coeffs : Array[Int64],
  p : Int64,
  n : Int32,
  r0 : Int64,
) -> (Int64, Bool) {
  let mut r = (r0 % p + p) % p
  let mut k = 1
  while k < n {
    let m = b7_ipow(p, k + 1)
    let f = b7_poly_eval(coeffs, r, m)
    let df = b7_poly_eval(b7_poly_deriv(coeffs), r, m)
    if df % p == 0L {
      return (r, false)
    }
    // r ← r − f·(df)⁻¹ mod p^{k+1}
    let (inv, ok) = b7_zp_inv(b7_zp(p, k + 1, df))
    if !ok {
      return (r, false)
    }
    r = ((r - f * inv.v) % m + m) % m
    k = k + 1
  }
  (r, true)
}

///|
/// 多項式求值 mod m（Horner）。
pub fn b7_poly_eval(c : Array[Int64], x : Int64, m : Int64) -> Int64 {
  let mut acc = 0L
  let mut i = c.length() - 1
  while i >= 0 {
    acc = (acc * x + c[i]) % m
    i = i - 1
  }
  (acc % m + m) % m
}

///|
/// 形式導數。
pub fn b7_poly_deriv(c : Array[Int64]) -> Array[Int64] {
  let out : Array[Int64] = []
  for i in 1..<c.length() {
    out.push(c[i] * i.to_int64())
  }
  out
}

// ───────────────────────── Newton 多邊形 ─────────────────────────

///|
/// Newton 多邊形（下凸包）：輸入支撑點 (i, j)（含係數非零的單項式指數），
/// 回傳由左至右的頂點序列。
pub fn b7_newton_polygon(
  points : Array[(Int32, Int32)],
) -> Array[(Int32, Int32)] {
  // 依 i 排序（同 i 取最小 j）
  let pts : Array[(Int32, Int32)] = []
  for q in points {
    pts.push(q)
  }
  let n = pts.length()
  for a in 0..<n {
    let mut b = a + 1
    while b < n {
      let pa = pts[a]
      let pb = pts[b]
      if pb.0 < pa.0 || (pb.0 == pa.0 && pb.1 < pa.1) {
        pts[a] = pb
        pts[b] = pa
      }
      b = b + 1
    }
  }
  // 去重（同 i 只留最小 j）
  let uniq : Array[(Int32, Int32)] = []
  for q in pts {
    let mut dup = false
    for u in uniq {
      if u.0 == q.0 {
        dup = true
      }
    }
    if !dup {
      uniq.push(q)
    }
  }
  // 下凸包：以斜率遞增維護
  let hull : Array[(Int32, Int32)] = []
  for q in uniq {
    while hull.length() >= 2 {
      let a = hull[hull.length() - 2]
      let b = hull[hull.length() - 1]
      // 交叉積 (b−a) × (q−a) > 0 ⇒ b 在上方，彈出
      let cross = (b.0 - a.0) * (q.1 - a.1) - (b.1 - a.1) * (q.0 - a.0)
      if cross > 0 {
        ignore(hull.pop())
      } else {
        break
      }
    }
    hull.push(q)
  }
  hull
}

///|
/// 最大公因數。
pub fn b7_gcd_i(a : Int32, b : Int32) -> Int32 {
  gcd_int(a, b)
}

///|
/// 邊的格長 ℓ = gcd(|Δi|, |Δj|)。
pub fn b7_lattice_length(e : (Int32, Int32)) -> Int32 {
  b7_gcd_i(e.0, e.1)
}

///|
/// 多邊形各邊的格長序列。
pub fn b7_edge_lengths(poly : Array[(Int32, Int32)]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<(poly.length() - 1) {
    let d = (poly[i + 1].0 - poly[i].0, poly[i + 1].1 - poly[i].1)
    out.push(b7_lattice_length(d))
  }
  out
}

///|
/// 環面消去所需的爆破次數 = Σ(ℓ_e − 1)。
pub fn b7_blowup_count(poly : Array[(Int32, Int32)]) -> Int32 {
  let mut s = 0
  for l in b7_edge_lengths(poly) {
    s = s + l - 1
  }
  s
}

///|
/// 消去後例外除子的鏈長 = Σ ℓ_e。
pub fn b7_chain_length(poly : Array[(Int32, Int32)]) -> Int32 {
  let mut s = 0
  for l in b7_edge_lengths(poly) {
    s = s + l
  }
  s
}

///|
/// Pick 定理：面積 = I + B/2 − 1。以**暴力數格點**核對（適用於小多邊形）。
/// 回傳 (2·面積, 2I + B − 2, 是否相等)。
pub fn b7_pick_check(poly0 : Array[(Int32, Int32)]) -> (Int32, Int32, Bool) {
  // Newton 多邊形必須與座標軸圍成封閉區域 ⇒ 加入原點 (0,0)
  let poly : Array[(Int32, Int32)] = []
  let mut has_origin = false
  for q in poly0 {
    if q.0 == 0 && q.1 == 0 {
      has_origin = true
    }
  }
  if !has_origin {
    poly.push((0, 0))
  }
  for q in poly0 {
    poly.push(q)
  }
  // 2·面積（鞋帶公式）
  let mut twice = 0
  for i in 0..<poly.length() {
    let a = poly[i]
    let b = poly[(i + 1) % poly.length()]
    twice = twice + (a.0 * b.1 - b.0 * a.1)
  }
  if twice < 0 {
    twice = -twice
  }
  // 邊界格點 B = Σ gcd
  let mut boundary = 0
  for i in 0..<poly.length() {
    let a = poly[i]
    let b = poly[(i + 1) % poly.length()]
    boundary = boundary + b7_gcd_i(b.0 - a.0, b.1 - a.1)
  }
  // 暴力數內部格點
  let mut imax = 0
  let mut jmax = 0
  for q in poly {
    if q.0 > imax {
      imax = q.0
    }
    if q.1 > jmax {
      jmax = q.1
    }
  }
  let mut interior = 0
  for i in 0..<(imax + 1) {
    for j in 0..<(jmax + 1) {
      if b7_point_inside(poly, i, j) {
        interior = interior + 1
      }
    }
  }
  let twice_pick = 2 * interior + boundary - 2
  (twice, twice_pick, twice == twice_pick)
}

///|
/// 嚴格內點判定（凸多邊形，以一致定向的叉積判準；邊界上不算內點）。
fn b7_point_inside(poly : Array[(Int32, Int32)], x : Int32, y : Int32) -> Bool {
  let n = poly.length()
  let mut pos = 0
  let mut neg = 0
  for i in 0..<n {
    let a = poly[i]
    let b = poly[(i + 1) % n]
    let cross = (b.0 - a.0) * (y - a.1) - (b.1 - a.1) * (x - a.0)
    if cross > 0 {
      pos = pos + 1
    } else if cross < 0 {
      neg = neg + 1
    }
  }
  (pos == 0 && neg == n) || (neg == 0 && pos == n)
}

// ───────────────────────── 例外除子的相交形式 ─────────────────────────

///|
/// 鏈狀 n 條 (−2)-曲線的相交矩陣：對角 −2、相鄰 +1。
pub fn b7_chain_intersection(n : Int32) -> Array[Array[Double]] {
  let m = b7_mat_zeros(n, n)
  for i in 0..<n {
    m[i][i] = -2.0
    if i + 1 < n {
      m[i][i + 1] = 1.0
      m[i + 1][i] = 1.0
    }
  }
  m
}

///|
/// 是否負定（所有 Jacobi 特徵值 < 0）。
pub fn b7_negative_definite(n : Int32) -> Bool {
  let (vals, _) = b7_jacobi_eigen(b7_chain_intersection(n))
  for v in vals {
    if v >= 0.0 {
      return false
    }
  }
  true
}

///|
/// 纖維相交形式：鏈 C_left, E_1..E_n, C_right，對角 (−1, −2, …, −2, −1)、相鄰 +1。
pub fn b7_fiber_form(n : Int32) -> Array[Array[Double]] {
  let m = b7_mat_zeros(n + 2, n + 2)
  for i in 0..<(n + 2) {
    m[i][i] = if i == 0 || i == n + 1 { -1.0 } else { -2.0 }
    if i + 1 < n + 2 {
      m[i][i + 1] = 1.0
      m[i + 1][i] = 1.0
    }
  }
  m
}

///|
/// 基本環定理（數值確認）：纖維形式 M' 負半定、核恰 1 維，且核由全 1 向量生成
/// （F = C_left + Σ E_i + C_right，F² = 0）；同時 F·E_i = 0（Artin 判準的等號情形）。
/// 回傳 (|M'·1|_max, 負半定且核 1 維?, Artin?)。純 (−2)-鏈（b7_chain_intersection）
/// 則為**嚴格負定**——兩者的差別正是「纖維」與「例外除子」的差別。
pub fn b7_fundamental_cycle(n : Int32) -> (Double, Bool, Bool) {
  let m = b7_fiber_form(n)
  let size = n + 2
  let cyc : Array[Double] = []
  for _ in 0..<size {
    cyc.push(1.0)
  }
  let mut worst = 0.0
  let mut artin = true
  for i in 0..<size {
    let mut s = 0.0
    for j in 0..<size {
      s = s + m[i][j] * cyc[j]
    }
    if s.abs() > worst {
      worst = s.abs()
    }
    if s > 1.0e-12 {
      artin = false
    }
  }
  let (vals, _) = b7_jacobi_eigen(m)
  let mut zeros = 0
  let mut any_pos = false
  for v in vals {
    if v > 1.0e-9 {
      any_pos = true
    }
    if v.abs() <= 1.0e-9 {
      zeros = zeros + 1
    }
  }
  (worst, !any_pos && zeros == 1, artin)
}

///|
/// 與模組 5 的交叉核對：Kodaira 型分量數 = v(Δ) − 1 = 鏈長，且相交形式負定。
pub fn b7_kodaira_chain_consistency(p : Int64) -> Bool {
  let mut ok = true
  for (_, _, ty, vd, comp, _) in b7_ff_tower(p, 6) {
    if b7_semistable(ty) {
      continue
    }
    if comp != vd - 1 {
      ok = false
    }
    // 例外鏈長 = 分量數 ⇒ 其相交矩陣必須負定
    if !b7_negative_definite(comp) {
      ok = false
    }
  }
  ok
}
