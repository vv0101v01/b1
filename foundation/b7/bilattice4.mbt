///|
/// bilattice4.mbt — 批次七·模組 1：B₄ 四值邏輯雙格（Belnap FOUR bilattice）
///
/// 元素以 (pos, neg) 雙位元編碼：pos = 「有真證據」，neg = 「有假證據」
///   Nn = (0,0) 無資訊、Tt = (1,0) 真、Ff = (0,1) 假、Both = (1,1) 矛盾
/// 編碼 = pos + 2·neg，即 Nn=0, Tt=1, Ff=2, Both=3。
///
/// 兩個偏序：
///   真序 (truth order)      x ≤t y  ⟺  pos x ≤ pos y 且 neg x ≥ neg y
///        （底 Ff，頂 Tt，Nn/Both 為不可比的中間層 —— 經典菱形）
///   知識序 (knowledge order) x ≤k y  ⟺  pos x ≤ pos y 且 neg x ≤ neg y
///        （底 Nn，頂 Both，Tt/Ff 不可比）
///
/// 格運算（由 Belnap 真值表直接推得）：
///   ∧t = (pos:AND, neg:OR),  ∨t = (pos:OR, neg:AND)
///   ∧k = (AND, AND),         ∨k = (OR,  OR)   ← 即位元 AND / OR
///   否定 ¬：(pos,neg) ↦ (neg,pos)              ← 反轉 ≤t、保持 ≤k
///   合流 −：(pos,neg) ↦ (¬neg,¬pos)            ← Nn↔Both 互換
///
/// 本模組的計算機任務：不假設任何雙格定理，用**完全枚舉**把它們量出來。

///|
/// 四值：Nn（neither）、Tt（true）、Ff（false）、Both（both）。
#derive(Debug, Eq, Hash)
pub enum L4 {
  Nn
  Tt
  Ff
  Both
}

///|
/// 全部元素（固定順序 = 編碼 0,1,2,3）。
pub fn b7_all4() -> Array[L4] {
  [Nn, Tt, Ff, Both]
}

///|
/// 編碼 0..3（pos 為低位、neg 為高位）。
pub fn b7_code(v : L4) -> Int32 {
  match v {
    Nn => 0
    Tt => 1
    Ff => 2
    Both => 3
  }
}

///|
/// 由編碼還原元素。
pub fn b7_of_code(c : Int32) -> L4 {
  match c {
    0 => Nn
    1 => Tt
    2 => Ff
    _ => Both
  }
}

///|
/// pos 位元（有真證據）。
pub fn b7_pos(v : L4) -> Bool {
  b7_code(v) % 2 == 1
}

///|
/// neg 位元（有假證據）。
pub fn b7_neg(v : L4) -> Bool {
  b7_code(v) / 2 == 1
}

///|
/// 建構：由 (pos, neg) 兩個布林。
pub fn b7_mk(p : Bool, n : Bool) -> L4 {
  b7_of_code((if p { 1 } else { 0 }) + (if n { 2 } else { 0 }))
}

///|
/// 真序 x ≤t y。
pub fn b7_le_t(x : L4, y : L4) -> Bool {
  let px = b7_pos(x)
  let py = b7_pos(y)
  let nx = b7_neg(x)
  let ny = b7_neg(y)
  let p_ok = if py { true } else { !px } // px ≤ py
  let n_ok = if nx { true } else { !ny } // nx ≥ ny
  p_ok && n_ok
}

///|
/// 知識序 x ≤k y。
pub fn b7_le_k(x : L4, y : L4) -> Bool {
  let px = b7_pos(x)
  let py = b7_pos(y)
  let nx = b7_neg(x)
  let ny = b7_neg(y)
  let p_ok = if py { true } else { !px }
  let n_ok = if ny { true } else { !nx }
  p_ok && n_ok
}

///|
/// 真序 meet ∧t（合取）。
pub fn b7_meet_t(x : L4, y : L4) -> L4 {
  b7_mk(b7_pos(x) && b7_pos(y), b7_neg(x) || b7_neg(y))
}

///|
/// 真序 join ∨t（析取）。
pub fn b7_join_t(x : L4, y : L4) -> L4 {
  b7_mk(b7_pos(x) || b7_pos(y), b7_neg(x) && b7_neg(y))
}

///|
/// 知識序 meet ∧k（共識 consensus）。
pub fn b7_meet_k(x : L4, y : L4) -> L4 {
  b7_mk(b7_pos(x) && b7_pos(y), b7_neg(x) && b7_neg(y))
}

///|
/// 知識序 join ∨k（輕信 gullibility）。
pub fn b7_join_k(x : L4, y : L4) -> L4 {
  b7_mk(b7_pos(x) || b7_pos(y), b7_neg(x) || b7_neg(y))
}

///|
/// 否定 ¬：交換真/假見證（反轉真序、保持知識序）。
pub fn b7_not(x : L4) -> L4 {
  b7_mk(b7_neg(x), b7_pos(x))
}

///|
/// 合流 −（conflation）：Nn ↔ Both，Tt/Ff 不動。
pub fn b7_conflate(x : L4) -> L4 {
  b7_mk(!b7_neg(x), !b7_pos(x))
}

///|
/// 材料蘊含 p → q := ¬p ∨t q（Belnap 的實質蘊含）。
pub fn b7_impl(x : L4, y : L4) -> L4 {
  b7_join_t(b7_not(x), y)
}

///|
/// 指派集合（designated）：{Tt, Both} —— 「至少為真」。
pub fn b7_designated(x : L4) -> Bool {
  b7_pos(x)
}

// ───────────────────────── 公理完全枚舉 ─────────────────────────

///|
/// 交換律：∧t, ∨t, ∧k, ∨k 共 4 × 16 = 64 次檢驗。
pub fn b7_commutative_ok() -> Bool {
  let xs = b7_all4()
  for x in xs {
    for y in xs {
      if b7_meet_t(x, y) != b7_meet_t(y, x) {
        return false
      }
      if b7_join_t(x, y) != b7_join_t(y, x) {
        return false
      }
      if b7_meet_k(x, y) != b7_meet_k(y, x) {
        return false
      }
      if b7_join_k(x, y) != b7_join_k(y, x) {
        return false
      }
    }
  }
  true
}

///|
/// 冪等律：4 × 4 次。
pub fn b7_idempotent_ok() -> Bool {
  for x in b7_all4() {
    if b7_meet_t(x, x) != x || b7_join_t(x, x) != x {
      return false
    }
    if b7_meet_k(x, x) != x || b7_join_k(x, x) != x {
      return false
    }
  }
  true
}

///|
/// 吸收律：4 ops × 16 pairs × 2 方向。
pub fn b7_absorption_ok() -> Bool {
  let xs = b7_all4()
  for x in xs {
    for y in xs {
      if b7_meet_t(x, b7_join_t(x, y)) != x {
        return false
      }
      if b7_join_t(x, b7_meet_t(x, y)) != x {
        return false
      }
      if b7_meet_k(x, b7_join_k(x, y)) != x {
        return false
      }
      if b7_join_k(x, b7_meet_k(x, y)) != x {
        return false
      }
    }
  }
  true
}

///|
/// 結合律：4 ops × 64 triples。
pub fn b7_associative_ok() -> Bool {
  let xs = b7_all4()
  for x in xs {
    for y in xs {
      for z in xs {
        if b7_meet_t(b7_meet_t(x, y), z) != b7_meet_t(x, b7_meet_t(y, z)) {
          return false
        }
        if b7_join_t(b7_join_t(x, y), z) != b7_join_t(x, b7_join_t(y, z)) {
          return false
        }
        if b7_meet_k(b7_meet_k(x, y), z) != b7_meet_k(x, b7_meet_k(y, z)) {
          return false
        }
        if b7_join_k(b7_join_k(x, y), z) != b7_join_k(x, b7_join_k(y, z)) {
          return false
        }
      }
    }
  }
  true
}

///|
/// 分配律（兩格各 16 triples × 2 方向 = 128 次）。
pub fn b7_distributive_ok() -> Bool {
  let xs = b7_all4()
  for x in xs {
    for y in xs {
      for z in xs {
        let a = b7_meet_t(x, b7_join_t(y, z))
        let b = b7_join_t(b7_meet_t(x, y), b7_meet_t(x, z))
        if a != b {
          return false
        }
        let c = b7_join_t(x, b7_meet_t(y, z))
        let d = b7_meet_t(b7_join_t(x, y), b7_join_t(x, z))
        if c != d {
          return false
        }
        let e = b7_meet_k(x, b7_join_k(y, z))
        let f = b7_join_k(b7_meet_k(x, y), b7_meet_k(x, z))
        if e != f {
          return false
        }
        let g = b7_join_k(x, b7_meet_k(y, z))
        let h = b7_meet_k(b7_join_k(x, y), b7_join_k(x, z))
        if g != h {
          return false
        }
      }
    }
  }
  true
}

///|
/// 格的序一致性：x ≤t y ⟺ x∧t y = x ⟺ x∨t y = y（4×4 全檢）。
pub fn b7_order_consistent_ok() -> Bool {
  let xs = b7_all4()
  for x in xs {
    for y in xs {
      let lt = b7_le_t(x, y)
      if lt != (b7_meet_t(x, y) == x) {
        return false
      }
      if lt != (b7_join_t(x, y) == y) {
        return false
      }
      let lk = b7_le_k(x, y)
      if lk != (b7_meet_k(x, y) == x) {
        return false
      }
      if lk != (b7_join_k(x, y) == y) {
        return false
      }
    }
  }
  true
}

///|
/// 交錯性（interlacing）：若 x ≤k y，則真格運算對 z 仍 ≤k 單調；反之亦然。
/// 2 方向 × 4 運算 × 64 triples。
pub fn b7_interlacing_ok() -> Bool {
  let xs = b7_all4()
  for x in xs {
    for y in xs {
      for z in xs {
        if b7_le_k(x, y) {
          if !b7_le_k(b7_meet_t(x, z), b7_meet_t(y, z)) {
            return false
          }
          if !b7_le_k(b7_join_t(x, z), b7_join_t(y, z)) {
            return false
          }
        }
        if b7_le_t(x, y) {
          if !b7_le_t(b7_meet_k(x, z), b7_meet_k(y, z)) {
            return false
          }
          if !b7_le_t(b7_join_k(x, z), b7_join_k(y, z)) {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// De Morgan 型對偶性：¬ 是真格 (≤t) 的反自同構、知識格 (≤k) 的自同構。
/// 2 × 16 + 2 × 16 = 64 次檢驗；注意知識格的兩個運算**不**互換。
pub fn b7_demorgan_ok() -> Bool {
  let xs = b7_all4()
  for x in xs {
    for y in xs {
      if b7_not(b7_meet_t(x, y)) != b7_join_t(b7_not(x), b7_not(y)) {
        return false
      }
      if b7_not(b7_join_t(x, y)) != b7_meet_t(b7_not(x), b7_not(y)) {
        return false
      }
      if b7_not(b7_meet_k(x, y)) != b7_meet_k(b7_not(x), b7_not(y)) {
        return false
      }
      if b7_not(b7_join_k(x, y)) != b7_join_k(b7_not(x), b7_not(y)) {
        return false
      }
    }
  }
  true
}

///|
/// ¬ 是反序對合：x ≤t y ⟺ ¬y ≤t ¬x；且 x ≤k y ⟺ ¬x ≤k ¬y；¬¬x = x。
pub fn b7_negation_antitone_ok() -> Bool {
  let xs = b7_all4()
  for x in xs {
    if b7_not(b7_not(x)) != x {
      return false
    }
    for y in xs {
      if b7_le_t(x, y) != b7_le_t(b7_not(y), b7_not(x)) {
        return false
      }
      if b7_le_k(x, y) != b7_le_k(b7_not(x), b7_not(y)) {
        return false
      }
    }
  }
  true
}

///|
/// 合流 − 的對偶性：它是真格 (≤t) 的自同構、知識格 (≤k) 的反自同構。
pub fn b7_conflation_ok() -> Bool {
  let xs = b7_all4()
  for x in xs {
    if b7_conflate(b7_conflate(x)) != x {
      return false
    }
    for y in xs {
      // 真格：保 ∧t、∨t
      if b7_conflate(b7_meet_t(x, y)) !=
        b7_meet_t(b7_conflate(x), b7_conflate(y)) {
        return false
      }
      if b7_conflate(b7_join_t(x, y)) !=
        b7_join_t(b7_conflate(x), b7_conflate(y)) {
        return false
      }
      // 知識格：換 ∧k ↔ ∨k
      if b7_conflate(b7_meet_k(x, y)) !=
        b7_join_k(b7_conflate(x), b7_conflate(y)) {
        return false
      }
      if b7_conflate(b7_join_k(x, y)) !=
        b7_meet_k(b7_conflate(x), b7_conflate(y)) {
        return false
      }
    }
  }
  true
}

///|
/// 雙格自同構的完全枚舉：4⁴ = 256 個候選映射，逐一檢查是否為雙格同構。
/// 回傳自同構的個數，並以 `^` 輸出群階（應為 4 = |Z/2 × Z/2|）。
pub fn b7_count_bilattice_automorphisms() -> Int32 {
  let mut count = 0
  for c0 in 0..<4 {
    for c1 in 0..<4 {
      for c2 in 0..<4 {
        for c3 in 0..<4 {
          let img = [b7_of_code(c0), b7_of_code(c1)]
          let img2 = [b7_of_code(c2), b7_of_code(c3)]
          // 必須是雙射
          let seen = [false, false, false, false]
          let full = [img[0], img[1], img2[0], img2[1]]
          let mut bijective = true
          for v in full {
            let idx = b7_code(v)
            if seen[idx] {
              bijective = false
            }
            seen[idx] = true
          }
          if !bijective {
            continue
          }
          if b7_is_bilattice_hom(full) {
            count = count + 1
          }
        }
      }
    }
  }
  count
}

///|
/// f : 4 元素表（f(i) = 表[i]）是否同時保 ∧t,∨t,∧k,∨k（雙格同態）。
fn b7_is_bilattice_hom(tbl : Array[L4]) -> Bool {
  let xs = b7_all4()
  for x in xs {
    for y in xs {
      let ix = b7_code(x)
      let iy = b7_code(y)
      let fx = tbl[ix]
      let fy = tbl[iy]
      if tbl[b7_code(b7_meet_t(x, y))] != b7_meet_t(fx, fy) {
        return false
      }
      if tbl[b7_code(b7_join_t(x, y))] != b7_join_t(fx, fy) {
        return false
      }
      if tbl[b7_code(b7_meet_k(x, y))] != b7_meet_k(fx, fy) {
        return false
      }
      if tbl[b7_code(b7_join_k(x, y))] != b7_join_k(fx, fy) {
        return false
      }
    }
  }
  true
}

///|
/// 4 元素上所有格結構的完全枚舉：meet 表由交換律（6 個自由對）與冪等律（對角固定）
/// 決定，故候選數 = 4⁶ = 4096。逐一檢查格公理與分配律，並以 24 個置換正規化去重。
/// 回傳 (同構類個數, 其中菱形的個數, 鏈的個數)。
pub fn b7_enumerate_four_element_lattices() -> (Int32, Int32, Int32) {
  let canon : Array[String] = []
  let mut diamonds = 0
  let mut chains = 0
  let pairs = [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]]
  for code in 0..<4096 {
    let m : Array[Int32] = [0, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 3, 3, 3, 3, 3]
    let mut rest = code
    for k in 0..<6 {
      let v = rest % 4
      rest = rest / 4
      let a = pairs[k][0]
      let b = pairs[k][1]
      m[a * 4 + b] = v
      m[b * 4 + a] = v
    }
    if !b7_lattice_axioms(m) {
      continue
    }
    let key = b7_lattice_canon(m)
    let mut dup = false
    for s in canon {
      if s == key {
        dup = true
      }
    }
    if dup {
      continue
    }
    canon.push(key)
    if b7_lattice_is_diamond(m) {
      diamonds = diamonds + 1
    } else {
      chains = chains + 1
    }
  }
  (canon.length(), diamonds, chains)
}

///|
/// meet 表 m（16 格）是否構成有限格：交（meet）為結合、吸收，且 join 可由 meet 導出。
fn b7_lattice_axioms(m : Array[Int32]) -> Bool {
  for i in 0..<4 {
    if m[i * 4 + i] != i {
      return false
    }
  }
  // 結合律
  for a in 0..<4 {
    for b in 0..<4 {
      for c in 0..<4 {
        if m[m[a * 4 + b] * 4 + c] != m[a * 4 + m[b * 4 + c]] {
          return false
        }
      }
    }
  }
  // 吸收：需存在 join。在有限格中 a∨b = 所有 z 滿足 z∧a=a ∧ z∧b=b 的「meet-最小」者
  for a in 0..<4 {
    for b in 0..<4 {
      let mut found = -1
      for z in 0..<4 {
        if m[z * 4 + a] == a && m[z * 4 + b] == b {
          if found < 0 {
            found = z
          } else if m[z * 4 + found] == z {
            // z ≤ found ⇒ 取更小者
            found = z
          }
        }
      }
      if found < 0 {
        return false
      }
      // 最小上界必須唯一
      for z in 0..<4 {
        if m[z * 4 + a] == a && m[z * 4 + b] == b {
          if m[z * 4 + found] != found {
            return false
          }
        }
      }
    }
  }
  // 分配律：a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)
  for a in 0..<4 {
    for b in 0..<4 {
      for c in 0..<4 {
        let jbc = b7_lattice_join(m, b, c)
        let lhs = m[a * 4 + jbc]
        let jl = b7_lattice_join(m, m[a * 4 + b], m[a * 4 + c])
        if lhs != jl {
          return false
        }
      }
    }
  }
  true
}

///|
/// 由 meet 表導出 join：a∨b = 滿足 z∧a=a、z∧b=b 的 meet-最小 z。
fn b7_lattice_join(m : Array[Int32], a : Int32, b : Int32) -> Int32 {
  let mut found = 0
  for z in 0..<4 {
    if m[z * 4 + a] == a && m[z * 4 + b] == b {
      if m[z * 4 + found] == z || m[found * 4 + a] != a {
        found = z
      }
    }
  }
  // 以「z ≤ found」判準重掃一遍以確保最小
  for z in 0..<4 {
    if m[z * 4 + a] == a && m[z * 4 + b] == b {
      if m[z * 4 + found] == z {
        found = z
      }
    }
  }
  found
}

///|
/// 這張 meet 表是否為 4 元素菱形（= 2×2 布林格：底、頂、兩個不可比中間元）。
pub fn b7_lattice_is_diamond(m : Array[Int32]) -> Bool {
  let mut bottoms = 0
  let mut tops = 0
  for a in 0..<4 {
    let mut is_bot = true
    let mut is_top = true
    for b in 0..<4 {
      if m[a * 4 + b] != a {
        is_bot = false
      }
      if m[a * 4 + b] != b {
        is_top = false
      }
    }
    if is_bot {
      bottoms = bottoms + 1
    }
    if is_top {
      tops = tops + 1
    }
  }
  if bottoms != 1 || tops != 1 {
    return false
  }
  let mid : Array[Int32] = []
  for a in 0..<4 {
    let mut is_bot = true
    let mut is_top = true
    for b in 0..<4 {
      if m[a * 4 + b] != a {
        is_bot = false
      }
      if m[a * 4 + b] != b {
        is_top = false
      }
    }
    if !is_bot && !is_top {
      mid.push(a)
    }
  }
  if mid.length() != 2 {
    return false
  }
  // 不可比：兩者的 meet 皆為底且 join 皆為頂
  let bot = b7_lattice_bot(m)
  let top = b7_lattice_top(m)
  m[mid[0] * 4 + mid[1]] == bot && b7_lattice_join(m, mid[0], mid[1]) == top
}

///|
/// 格的底元素。
fn b7_lattice_bot(m : Array[Int32]) -> Int32 {
  for a in 0..<4 {
    let mut ok = true
    for b in 0..<4 {
      if m[a * 4 + b] != a {
        ok = false
      }
    }
    if ok {
      return a
    }
  }
  0
}

///|
/// 格的頂元素。
fn b7_lattice_top(m : Array[Int32]) -> Int32 {
  for a in 0..<4 {
    let mut ok = true
    for b in 0..<4 {
      if m[a * 4 + b] != b {
        ok = false
      }
    }
    if ok {
      return a
    }
  }
  0
}

///|
/// 以「所有 4! 排列拉回後取字典序最小」的方式正規化格表。
fn b7_lattice_canon(m : Array[Int32]) -> String {
  let perms = [
    [0, 1, 2, 3],
    [0, 1, 3, 2],
    [0, 2, 1, 3],
    [0, 2, 3, 1],
    [0, 3, 1, 2],
    [0, 3, 2, 1],
    [1, 0, 2, 3],
    [1, 0, 3, 2],
    [1, 2, 0, 3],
    [1, 2, 3, 0],
    [1, 3, 0, 2],
    [1, 3, 2, 0],
    [2, 0, 1, 3],
    [2, 0, 3, 1],
    [2, 1, 0, 3],
    [2, 1, 3, 0],
    [2, 3, 0, 1],
    [2, 3, 1, 0],
    [3, 0, 1, 2],
    [3, 0, 2, 1],
    [3, 1, 0, 2],
    [3, 1, 2, 0],
    [3, 2, 0, 1],
    [3, 2, 1, 0],
  ]
  let mut best = ""
  let mut first = true
  for p in perms {
    // 拉回：new[a][b] = p[m[p⁻¹(a)][p⁻¹(b)]]
    let inv : Array[Int32] = [0, 0, 0, 0]
    for i in 0..<4 {
      inv[p[i]] = i
    }
    let mut s = ""
    for a in 0..<4 {
      for b in 0..<4 {
        let v = p[m[inv[a] * 4 + inv[b]]]
        s = s + v.to_string()
      }
    }
    if first || s < best {
      best = s
      first = false
    }
  }
  best
}

// ───────────────────────── 四值邏輯的元定理 ─────────────────────────

///|
/// 爆炸原理（ex falso）檢查：是否存在指派使 p∧¬p 被指定為真而 q 不被指定。
/// 若存在，則 B₄ 對實質蘊含**不容忍爆炸**（paraconsistent）。
pub fn b7_explosion_fails() -> Bool {
  let xs = b7_all4()
  for p in xs {
    for q in xs {
      let contradiction = b7_meet_t(p, b7_not(p))
      if b7_designated(contradiction) && !b7_designated(q) {
        return true
      }
    }
  }
  false
}

///|
/// 排中律 p∨¬p 是否為重言式（對所有指派皆被指定）。
pub fn b7_excluded_middle_tautology() -> Bool {
  for p in b7_all4() {
    if !b7_designated(b7_join_t(p, b7_not(p))) {
      return false
    }
  }
  true
}

///|
/// 實質蘊含下的 modus ponens：p 與 p→q 皆被指定 ⇒ q 被指定？
pub fn b7_modus_ponens_valid() -> Bool {
  let xs = b7_all4()
  for p in xs {
    for q in xs {
      if b7_designated(p) && b7_designated(b7_impl(p, q)) && !b7_designated(q) {
        return false
      }
    }
  }
  true
}

///|
/// 使 MP 失敗的具體反例（p, q），供報告引用。回傳 (p, q) 或 (Nn, Nn) 表示無反例。
pub fn b7_mp_counterexample() -> (L4, L4) {
  let xs = b7_all4()
  for p in xs {
    for q in xs {
      if b7_designated(p) && b7_designated(b7_impl(p, q)) && !b7_designated(q) {
        return (p, q)
      }
    }
  }
  (Nn, Nn)
}

///|
/// 重言式計數的下界：對單變數公式集合 {p, ¬p, p∧p, p∨p, p∧¬p, p∨¬p, ¬¬p, −p, ...}
/// 直接枚舉所有 4 元素上的**保真序單調**一元函數個數，以及其中「恆被指定」的個數。
pub fn b7_unary_monotone_stats() -> (Int32, Int32) {
  let mut monotone = 0
  let mut always_designated = 0
  for c0 in 0..<4 {
    for c1 in 0..<4 {
      for c2 in 0..<4 {
        for c3 in 0..<4 {
          let tbl = [
            b7_of_code(c0),
            b7_of_code(c1),
            b7_of_code(c2),
            b7_of_code(c3),
          ]
          let mut ok = true
          for x in b7_all4() {
            for y in b7_all4() {
              if b7_le_t(x, y) && !b7_le_t(tbl[b7_code(x)], tbl[b7_code(y)]) {
                ok = false
              }
            }
          }
          if ok {
            monotone = monotone + 1
            let mut all_des = true
            for x in b7_all4() {
              if !b7_designated(tbl[b7_code(x)]) {
                all_des = false
              }
            }
            if all_des {
              always_designated = always_designated + 1
            }
          }
        }
      }
    }
  }
  (monotone, always_designated)
}

///|
/// B₄^k 的組合量：總元素 4^k、無矛盾元素 3^k、完全一致 2^k、真值密度。
/// 以整數冪回傳 (4^k, 3^k, 2^k)。
pub fn b7_product_counts(k : Int32) -> (Int64, Int64, Int64) {
  let mut a = 1L
  let mut b = 1L
  let mut c = 1L
  for _ in 0..<k {
    a = a * 4L
    b = b * 3L
    c = c * 2L
  }
  (a, b, c)
}

///|
/// 雙格同態 B₄ → B₂ 的核/像結構計數（用於 T207 的「古典崩塌」）。
/// 回傳 (同態數, 其中滿射個數)。
pub fn b7_b2_hom_surjective_count() -> (Int32, Int32) {
  let mut count = 0
  let mut surj = 0
  for mask in 0..<16 {
    let tbl = [
      if mask % 2 == 1 {
        Tt
      } else {
        Nn
      },
      if mask / 2 % 2 == 1 {
        Tt
      } else {
        Nn
      },
      if mask / 4 % 2 == 1 {
        Tt
      } else {
        Nn
      },
      if mask / 8 % 2 == 1 {
        Tt
      } else {
        Nn
      },
    ]
    if b7_is_bilattice_hom(tbl) {
      count = count + 1
      let mut has_true = false
      let mut has_false = false
      for v in tbl {
        if v == Tt {
          has_true = true
        } else {
          has_false = true
        }
      }
      if has_true && has_false {
        surj = surj + 1
      }
    }
  }
  (count, surj)
}

///|
/// 雙格對稱群 V：使 {∧t,∨t} 與 {∧k,∨k} 各自（可互換地）保持的置換，完全枚舉行舉。
/// 回傳個數（應為 4 = |Z/2 × Z/2|：id、¬、−、¬−）。
pub fn b7_count_bilattice_symmetries() -> Int32 {
  let mut count = 0
  for c0 in 0..<4 {
    for c1 in 0..<4 {
      for c2 in 0..<4 {
        for c3 in 0..<4 {
          let tbl = [
            b7_of_code(c0),
            b7_of_code(c1),
            b7_of_code(c2),
            b7_of_code(c3),
          ]
          if b7_is_bilattice_symmetry(tbl) {
            count = count + 1
          }
        }
      }
    }
  }
  count
}

///|
/// f 是否把真格的運算對 {∧t,∨t} 送到自身、知識格的運算對 {∧k,∨k} 送到自身
/// （允許每一對內部互換）。
pub fn b7_is_bilattice_symmetry(tbl : Array[L4]) -> Bool {
  if !b7_is_bijective_table(tbl) {
    return false
  }
  let truth = b7_preserves_pair(tbl, true) || b7_swaps_pair(tbl, true)
  let know = b7_preserves_pair(tbl, false) || b7_swaps_pair(tbl, false)
  truth && know
}

///|
/// 表是否為雙射。
fn b7_is_bijective_table(tbl : Array[L4]) -> Bool {
  let seen = [false, false, false, false]
  for v in tbl {
    let idx = b7_code(v)
    if seen[idx] {
      return false
    }
    seen[idx] = true
  }
  true
}

///|
/// f(x ∧ y) = f(x) ∧ f(y) 且 f(x ∨ y) = f(x) ∨ f(y)。
fn b7_preserves_pair(tbl : Array[L4], truth : Bool) -> Bool {
  for x in b7_all4() {
    for y in b7_all4() {
      let fx = tbl[b7_code(x)]
      let fy = tbl[b7_code(y)]
      if tbl[b7_code(b7_apply(x, y, truth, true))] !=
        b7_apply(fx, fy, truth, true) {
        return false
      }
      if tbl[b7_code(b7_apply(x, y, truth, false))] !=
        b7_apply(fx, fy, truth, false) {
        return false
      }
    }
  }
  true
}

///|
/// f(x ∧ y) = f(x) ∨ f(y) 且 f(x ∨ y) = f(x) ∧ f(y)（兩個運算互換）。
fn b7_swaps_pair(tbl : Array[L4], truth : Bool) -> Bool {
  for x in b7_all4() {
    for y in b7_all4() {
      let fx = tbl[b7_code(x)]
      let fy = tbl[b7_code(y)]
      if tbl[b7_code(b7_apply(x, y, truth, true))] !=
        b7_apply(fx, fy, truth, false) {
        return false
      }
      if tbl[b7_code(b7_apply(x, y, truth, false))] !=
        b7_apply(fx, fy, truth, true) {
        return false
      }
    }
  }
  true
}

///|
/// 依 (真序?, meet?) 施對應的格運算。
fn b7_apply(x : L4, y : L4, truth : Bool, meet : Bool) -> L4 {
  if truth {
    if meet {
      b7_meet_t(x, y)
    } else {
      b7_join_t(x, y)
    }
  } else if meet {
    b7_meet_k(x, y)
  } else {
    b7_join_k(x, y)
  }
}
