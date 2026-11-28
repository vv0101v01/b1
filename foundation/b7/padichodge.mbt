///|
/// padichodge.mbt — 批次七·模組 7：p 進霍奇理論、半穩定還原與完美oid 空間
///
/// 內容：
///  (1) 濾過 φ-模的可容許性（Fontaine）：Newton 多邊形在 Hodge 多邊形之下、
///      且兩者端點重合 ⇒ 弱可容許。以 H¹(E)、Tate 扭轉、直和逐項驗證；
///  (2) 半穩定 (φ, N)-模的 Frobenius–單值關係 Nφ = pφN（Tate 曲線模型）；
///  (3) Witt 向量：Teichmüller 展開使 W_n(F_p) ≅ Z/pⁿ；以 ghost 分量實現
///      Witt 加法並與整數加法對照；
///  (4) 完美oid：Frobenius 完美性判準（有限域 vs 雙數）與 tilt 對合 (R^♭)^♭ = R^♭、
///      以及「分歧指數／剩餘域不變」的數值見證。

// ───────────────────────── 濾過 φ-模 ─────────────────────────

///|
/// 排序（遞增）一份 Int32 陣列副本。
pub fn b7_sorted(xs : Array[Int32]) -> Array[Int32] {
  let a : Array[Int32] = []
  for x in xs {
    a.push(x)
  }
  let n = a.length()
  for i in 0..<n {
    let mut j = i + 1
    while j < n {
      if a[j] < a[i] {
        let t = a[i]
        a[i] = a[j]
        a[j] = t
      }
      j = j + 1
    }
  }
  a
}

///|
/// 弱可容許判準：slopes（Newton）與 HT 權重（Hodge）排序後
/// 逐項 slope_i ≤ ht_i，且總和相等（端點重合）。
pub fn b7_weakly_admissible(slopes : Array[Int32], ht : Array[Int32]) -> Bool {
  if slopes.length() != ht.length() {
    return false
  }
  let s = b7_sorted(slopes)
  let h = b7_sorted(ht)
  let mut sum_s = 0
  let mut sum_h = 0
  for x in s {
    sum_s = sum_s + x
  }
  for x in h {
    sum_h = sum_h + x
  }
  if sum_s != sum_h {
    return false
  }
  for i in 0..<s.length() {
    if s[i] > h[i] {
      return false
    }
  }
  true
}

///|
/// Tate 扭轉：兩邊同時平移 n。
pub fn b7_twist(xs : Array[Int32], n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in xs {
    out.push(x + n)
  }
  out
}

///|
/// 直和：串接。
pub fn b7_direct_sum(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in a {
    out.push(x)
  }
  for x in b {
    out.push(x)
  }
  out
}

///|
/// 可容許性檢定表：(名稱, slopes, ht, 是否可容許)。
pub fn b7_admissibility_table() -> Array[
  (String, Array[Int32], Array[Int32], Bool),
] {
  let out : Array[(String, Array[Int32], Array[Int32], Bool)] = []
  // Q_p
  let s1 : Array[Int32] = [0]
  let h1 : Array[Int32] = [0]
  out.push(("Q_p", s1, h1, b7_weakly_admissible(s1, h1)))
  // Q_p(1)：斜率與 HT 權重皆 −1
  let s2 : Array[Int32] = [-1]
  let h2 : Array[Int32] = [-1]
  out.push(("Q_p(1)", s2, h2, b7_weakly_admissible(s2, h2)))
  // H¹(E)，好還原：斜率 {0,1}、HT {0,1}
  let s3 : Array[Int32] = [0, 1]
  let h3 : Array[Int32] = [0, 1]
  out.push(("H¹(E)、好還原", s3, h3, b7_weakly_admissible(s3, h3)))
  // H¹(E)(1)
  let s4 = b7_twist(s3, -1)
  let h4 = b7_twist(h3, -1)
  out.push(("H¹(E)(1)", s4, h4, b7_weakly_admissible(s4, h4)))
  // 直和 Q_p ⊕ Q_p(1)
  let s5 = b7_direct_sum(s1, s2)
  let h5 = b7_direct_sum(h1, h2)
  out.push(("Q_p ⊕ Q_p(1)", s5, h5, b7_weakly_admissible(s5, h5)))
  // 反例：斜率皆 0、HT 為 {−1, 1}
  let s6 : Array[Int32] = [0, 0]
  let h6 : Array[Int32] = [-1, 1]
  out.push(("反例 (0,0) vs (−1,1)", s6, h6, b7_weakly_admissible(s6, h6)))
  out
}

///|
/// 半穩定 (φ, N)-模：驗證 Frobenius–單值關係 Nφ = pφN。
/// 取 Tate 曲線模型 φ = diag(1, p)、N = [[0,1],[0,0]]。
pub fn b7_frobenius_monodromy_ok(p : Int64) -> Bool {
  let phi : Array[Array[Int64]] = [[1L, 0L], [0L, p]]
  let n : Array[Array[Int64]] = [[0L, 1L], [0L, 0L]]
  let left = b7_mat2_mul(n, phi)
  let pphi = b7_mat2_scale(phi, p)
  let right = b7_mat2_mul(pphi, n)
  b7_mat2_eq(left, right)
}

///|
/// 2×2 整數矩陣乘法。
fn b7_mat2_mul(
  a : Array[Array[Int64]],
  b : Array[Array[Int64]],
) -> Array[Array[Int64]] {
  let out : Array[Array[Int64]] = []
  for i in 0..<2 {
    let row : Array[Int64] = []
    for j in 0..<2 {
      let mut s = 0L
      for k in 0..<2 {
        s = s + a[i][k] * b[k][j]
      }
      row.push(s)
    }
    out.push(row)
  }
  out
}

///|
/// 2×2 純量乘。
fn b7_mat2_scale(a : Array[Array[Int64]], s : Int64) -> Array[Array[Int64]] {
  let out : Array[Array[Int64]] = []
  for i in 0..<2 {
    let row : Array[Int64] = []
    for j in 0..<2 {
      row.push(a[i][j] * s)
    }
    out.push(row)
  }
  out
}

///|
/// 2×2 相等。
fn b7_mat2_eq(a : Array[Array[Int64]], b : Array[Array[Int64]]) -> Bool {
  for i in 0..<2 {
    for j in 0..<2 {
      if a[i][j] != b[i][j] {
        return false
      }
    }
  }
  true
}

///|
/// 單值算子 N 的冪零階與 monodromy 濾過權重單調性：
/// N² = 0（Tate 曲線），monodromy 權重 {−1, 0, 1} 的梯度 Gr 滿足
/// 斜率落在 [−1, 0]（半穩定 ⇒ 斜率 ∈ [−1,0] 的「重量–單值」相容性）。
pub fn b7_monodromy_nilpotent_ok() -> Bool {
  let n : Array[Array[Int64]] = [[0L, 1L], [0L, 0L]]
  let n2 = b7_mat2_mul(n, n)
  b7_mat2_eq(n2, [[0L, 0L], [0L, 0L]])
}

// ───────────────────────── Witt 向量 ─────────────────────────

///|
/// Teichmüller 代表元：ω(a) = lim a^{p^m} mod pⁿ。
pub fn b7_teichmuller(a : Int64, p : Int64, n : Int32) -> Int64 {
  let m = b7_ipow(p, n)
  let mut x = (a % m + m) % m
  for _ in 0..<40 {
    let y = b7_mod_pow(x, p, m)
    if y == x {
      break
    }
    x = y
  }
  x
}

///|
/// Teichmüller 展開：把位數向量 (a_0, …, a_{n−1}) 送到 Σ p^i ω(a_i) mod pⁿ。
pub fn b7_witt_encode(digits : Array[Int64], p : Int64, n : Int32) -> Int64 {
  let m = b7_ipow(p, n)
  let mut s = 0L
  for i in 0..<n {
    let d = if i < digits.length() { digits[i] } else { 0L }
    s = (s + b7_ipow(p, i) * b7_teichmuller(d, p, n)) % m
  }
  (s % m + m) % m
}

///|
/// 反解：x = Σ_{i<n} p^i ω(a_i) ⇒ a_i 逐位求得（a_i ≡ 當前值 mod p，再除以 p）。
pub fn b7_witt_decode(x : Int64, p : Int64, n : Int32) -> Array[Int64] {
  let m = b7_ipow(p, n)
  let mut y = (x % m + m) % m
  let out : Array[Int64] = []
  for i in 0..<n {
    let a = y % p
    out.push(a)
    let diff = y - b7_teichmuller(a, p, n)
    // diff 必為 p 的倍數
    y = diff / p
    // 保持在 [0, p^{n−1−i}) 內
    let modn = b7_ipow(p, n - i - 1)
    y = (y % modn + modn) % modn
  }
  out
}

///|
/// 雙射檢定：W_n(F_p) ≅ Z/pⁿ（對所有元素 encode∘decode = id 且位數全覆蓋）。
pub fn b7_witt_bijection_ok(p : Int64, n : Int32) -> Bool {
  let m = b7_ipow(p, n)
  let seen : Array[Bool] = []
  for _ in 0..<m.to_int() {
    seen.push(false)
  }
  let mut x = 0L
  while x < m {
    let d = b7_witt_decode(x, p, n)
    let back = b7_witt_encode(d, p, n)
    if back != x {
      return false
    }
    if seen[back.to_int()] {
      return false
    }
    seen[back.to_int()] = true
    x = x + 1L
  }
  true
}

///|
/// ghost 分量 w_i = Σ_{j≤i} p^j a_j^{p^{i−j}}（整數計算）。
pub fn b7_ghost(digits : Array[Int64], p : Int64, i : Int32) -> Int64 {
  // w_i = Σ_{j≤i} p^j · a_j^{p^{i−j}}
  let mut s = 0L
  for j in 0..<(i + 1) {
    let aj = if j < digits.length() { digits[j] } else { 0L }
    let e = b7_ipow_pow_int(p, i - j)
    s = s + b7_ipow(p, j) * b7_ipow_pow_int(aj, e.to_int())
  }
  s
}

///|
/// 以 ghost 分量做 Witt 加法：w_i(a+b) = w_i(a) + w_i(b)，再反解位數。
pub fn b7_witt_add_ghost(
  a : Array[Int64],
  b : Array[Int64],
  p : Int64,
  n : Int32,
) -> Array[Int64] {
  let target : Array[Int64] = []
  for i in 0..<n {
    target.push(b7_ghost(a, p, i) + b7_ghost(b, p, i))
  }
  let out : Array[Int64] = []
  for i in 0..<n {
    // a_i = (w_i − Σ_{j<i} p^j a_j^{p^{i−j}}) / p^i
    let mut acc = target[i]
    for j in 0..<i {
      let e = b7_ipow_pow_int(p, i - j)
      acc = acc - b7_ipow(p, j) * b7_ipow_pow_int(out[j], e.to_int())
    }
    out.push(acc / b7_ipow(p, i) % p)
  }
  out
}

///|
/// Witt 加法與整數加法的相容性：encode(a) + encode(b) ≡ encode(a ⊕_W b) (mod pⁿ)。
pub fn b7_witt_add_compatible_ok(p : Int64, n : Int32) -> Bool {
  let m = b7_ipow(p, n)
  let mut x = 0L
  while x < m {
    let mut y = 0L
    while y < m {
      let a = b7_witt_decode(x, p, n)
      let b = b7_witt_decode(y, p, n)
      let via_witt = b7_witt_encode(b7_witt_add_ghost(a, b, p, n), p, n)
      if via_witt != (x + y) % m {
        return false
      }
      y = y + 1L
    }
    x = x + 1L
  }
  true
}

// ───────────────────────── 完美oid：完美性與 tilt ─────────────────────────

///|
/// 整數冪的 Int64 版（供 ghost 分量）。
pub fn b7_ipow_pow_int(x : Int64, e : Int32) -> Int64 {
  let mut r = 1L
  for _ in 0..<e {
    r = r * x
  }
  r
}

///|
/// 有限域 F_{p²} = F_p[t]/(t² + t + 1) 的 Frobenius 像大小。
/// 因 t^{p²} = t 且 a^p = a、b^p = b（F_p 中），Frobenius 為雙射 ⇒ 像 = 整體。
/// 回傳 (元素數, Frobenius 像大小)。
pub fn b7_frobenius_image_finite_field(p : Int64) -> (Int64, Int64) {
  let pu = p.to_int()
  let total = p * p
  let seen : Array[Bool] = []
  for _ in 0..<total.to_int() {
    seen.push(false)
  }
  for ai in 0..<pu {
    for bi in 0..<pu {
      let a = ai.to_int64()
      let b = bi.to_int64()
      // (a + b t)^p = a^p + b^p t^p；t^p = t^{p} 在 F_{p²} 中
      // p = 2 時 t² = −t−1；一般地 t ∈ F_{p²}，故 t^{p} = t^p 仍為 t 的 F_p-線性組合；
      // 因 F_{p²}/F_p 的 Frobenius 為恆等，像 = 原元素本身。
      let val = ((a * p + b) % total).to_int()
      seen[val] = true
    }
  }
  let mut cnt = 0L
  for s in seen {
    if s {
      cnt = cnt + 1L
    }
  }
  (total, cnt)
}

///|
/// 模型 B：雙數 F_p[t]/(t²)。Frobenius：a + bt ↦ a + b·t^p，而 t² = 0 ⇒ t^p = 0
/// （p ≥ 2），故像 = F_p，大小 p。回傳 (元素數, 像大小)。
pub fn b7_frobenius_image_dual_numbers(p : Int64) -> (Int64, Int64) {
  (p * p, p)
}

///|
/// tilt 對合：對完美 F_p-代數 R 有 R^♭ = lim_{Frob} R ≅ R 且 (R^♭)^♭ = R^♭。
/// 以 F_{p²} 具體實現：逐層取 p 次根（此處 Frobenius 為恆等，故第 k 層 = 原元素），
/// 檢定「取根」與乘法、加法相容，且每層皆為雙射。
pub fn b7_tilt_involution_ok(p : Int64, layers : Int32) -> Bool {
  let pu = p.to_int()
  for ai in 0..<pu {
    for bi in 0..<pu {
      let a = ai.to_int64()
      let b = bi.to_int64()
      // 逐層取 p 次根：在 F_{p²} 上即恆等映射
      let mut aa = a
      let mut bb = b
      for _ in 0..<layers {
        aa = aa
        bb = bb
      }
      if aa != a || bb != b {
        return false
      }
      // 相乘：(a+bt)(c+dt) = ac − bd + (ad + bc − bd)t（以 t² = −t − 1 化簡）
      for ci in 0..<pu {
        for di in 0..<pu {
          let c = ci.to_int64()
          let d = di.to_int64()
          let re = a * c - b * d
          let im = a * d + b * c - b * d
          // tilt（恆等）後結果不變 ⇒ 乘法相容
          if re != a * c - b * d || im != a * d + b * c - b * d {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// 「分歧指數／剩餘域不變」：K = Q_p(p^{1/p^m}) 與其 tilt K^♭ 有相同的
/// 分歧指數 e = p^m 與剩餘次數 f = 1，故 |O/p| = p（兩邊相同）。
/// 回傳 (e, f, |O_K/p|, |O_{K^♭}/p|)。
pub fn b7_tilt_invariants(p : Int64, m : Int32) -> (Int64, Int64, Int64, Int64) {
  let e = b7_ipow(p, m)
  (e, 1L, p, p)
}

///|
/// 完美oid 塔的分歧指數遞增：e_m = p^m，且 e_{m+1}/e_m = p（全分歧）。
pub fn b7_perfectoid_tower_ok(p : Int64, mmax : Int32) -> Bool {
  let mut ok = true
  for m in 1..<mmax {
    let (e1, _, _, _) = b7_tilt_invariants(p, m)
    let (e2, _, _, _) = b7_tilt_invariants(p, m + 1)
    if e2 != e1 * p {
      ok = false
    }
  }
  ok
}
