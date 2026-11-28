///|
/// haw11.mbt — 批次十一·模組 1：豪斯多夫拓撲斯、緊拓撲斯
///
/// 空間拓撲斯 Sh(X) 的豪斯多夫性 ⟺ X 豪斯多夫 ⟺ 對角 Δ ⊂ X×X 為閉。
/// 兩條計算路線獨立實作：
///   (a) 點分離：任兩相異點有互不相交的鄰域；
///   (b) 對角閉：以積空間的基矩形族計算 Δ 的閉包，檢查 cl(Δ) = Δ。
/// 緊性：以「覆蓋的極小子覆蓋上界」量化（有限站上恆有限，但上界非平凡）。

// ───────────────────────── 點分離 ─────────────────────────

///|
/// 兩點是否可由不相交的開集分離。
fn b11_sep_pair(t : B9Top, p : Int32, q : Int32) -> Bool {
  for i in 0..<t.opens.length() {
    for j in 0..<t.opens.length() {
      if t.opens[i][p] && t.opens[j][q] && b9_top_inter(t, i, j) < 0 {
        return true
      }
    }
  }
  // 交集存在但為空的情形（站不含空集，故 b9_top_inter 可能回 -1 或空集編號）
  for i in 0..<t.opens.length() {
    for j in 0..<t.opens.length() {
      if t.opens[i][p] && t.opens[j][q] {
        let k = b9_top_inter(t, i, j)
        if k < 0 || b9_pop(t.opens[k]) == 0 {
          return true
        }
      }
    }
  }
  false
}

///|
/// 點分離：所有相異點對皆可被不相交開集分離（= T₂）。
pub fn b11_pts_separated(t : B9Top) -> Bool {
  for p in 0..<t.npt {
    for q in 0..<t.npt {
      if p < q && !b11_sep_pair(t, p, q) {
        return false
      }
    }
  }
  true
}

// ───────────────────────── 對角閉 ─────────────────────────

///|
/// 對角 Δ ⊂ X×X 的閉性：以積空間的基矩形 U×V 計算 Δ 的閉包。
/// Δ 閉 ⟺ 補集 X²∖Δ 可寫成基矩形之聯集。
pub fn b11_diag_closed(t : B9Top) -> Bool {
  let n = t.npt
  // 補集需要覆蓋的點對（p ≠ q）
  let covered : Array[Bool] = []
  for _ in 0..<(n * n) {
    covered.push(false)
  }
  for i in 0..<t.opens.length() {
    for j in 0..<t.opens.length() {
      let k = b9_top_inter(t, i, j)
      let empty = k < 0 || b9_pop(t.opens[k]) == 0
      if empty {
        // 矩形 U×V 與 Δ 不交 ⇒ 可納入補集的覆蓋
        for p in 0..<n {
          for q in 0..<n {
            if t.opens[i][p] && t.opens[j][q] {
              covered[p * n + q] = true
            }
          }
        }
      }
    }
  }
  for p in 0..<n {
    for q in 0..<n {
      if p != q && !covered[p * n + q] {
        return false
      }
    }
  }
  true
}

///|
/// 豪斯多夫拓撲斯：點分離與對角閉同時成立（兩條獨立路線）。
pub fn b11_hausdorff(t : B9Top) -> (Bool, Bool) {
  (b11_pts_separated(t), b11_diag_closed(t))
}

///|
/// 閉點的個數（拓撲斯的「點」）。
pub fn b11_closed_pts(t : B9Top) -> Int32 {
  let mut c = 0
  for p in 0..<t.npt {
    // {p} 閉 ⟺ X∖{p} 是開集
    let comp : Array[Bool] = []
    for q in 0..<t.npt {
      comp.push(q != p)
    }
    if b9_top_find(t, comp) >= 0 {
      c = c + 1
    }
  }
  c
}

// ───────────────────────── 緊性 ─────────────────────────

///|
/// 覆蓋的極小子覆蓋大小：對開集族取極小覆蓋子族的最小基數；非覆蓋族回 -1。
pub fn b11_min_subcover(t : B9Top, fam : Array[Int32]) -> Int32 {
  let top = t.npt
  let base : Array[Bool] = []
  for _ in 0..<top {
    base.push(true)
  }
  let mut cov = false
  for m in fam {
    let o = t.opens[m]
    for p in 0..<top {
      if o[p] {
        base[p] = false
      }
    }
  }
  for p in 0..<top {
    if base[p] {
      return -1
    }
  }
  cov = true
  let _ = cov
  // 暴力搜尋最小子族
  let k = fam.length()
  let mut best = k
  for mask in 0..<b8_pow_int(2, k) {
    let mut cnt = 0
    let acc : Array[Bool] = []
    for _ in 0..<top {
      acc.push(false)
    }
    for i in 0..<k {
      if ((mask >> i) & 1) == 1 {
        cnt = cnt + 1
        let o = t.opens[fam[i]]
        for p in 0..<top {
          if o[p] {
            acc[p] = true
          }
        }
      }
    }
    if cnt < best {
      let mut all = true
      for p in 0..<top {
        if !acc[p] {
          all = false
        }
      }
      if all {
        best = cnt
      }
    }
  }
  best
}

///|
/// 全部覆蓋族（開集子集族，含空族）與其極小子覆蓋大小統計。
/// 回傳 (覆蓋族數, 極小子覆蓋上界, 極小子覆蓋為 1 的族數)。
pub fn b11_cover_stats(t : B9Top) -> (Int32, Int32, Int32) {
  let n = t.opens.length()
  let top = t.npt
  let mut covers = 0
  let mut worst = 0
  let mut trivial = 0
  for mask in 0..<b8_pow_int(2, n) {
    let acc : Array[Bool] = []
    for _ in 0..<top {
      acc.push(false)
    }
    let fam : Array[Int32] = []
    for i in 0..<n {
      if ((mask >> i) & 1) == 1 {
        fam.push(i)
        for p in 0..<top {
          if t.opens[i][p] {
            acc[p] = true
          }
        }
      }
    }
    let mut all = true
    for p in 0..<top {
      if !acc[p] {
        all = false
      }
    }
    if all {
      covers = covers + 1
      let m = b11_min_subcover(t, fam)
      if m > worst {
        worst = m
      }
      if m == 1 {
        trivial = trivial + 1
      }
    }
  }
  (covers, worst, trivial)
}

///|
/// 緊拓撲斯：終對象被有限族覆蓋的極小子覆蓋有上界（有限站恆真，此處給出上界值）。
pub fn b11_compact(t : B9Top) -> (Bool, Int32) {
  let (covers, worst, _) = b11_cover_stats(t)
  (covers > 0 && worst <= t.npt, worst)
}
