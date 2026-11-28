///|
/// czfm.mbt — 批次十二·模組 1：**CZFM 不可達層級與雙重視角**（T411–T414、A65–A67）。
///
/// 名詞與可計算內容的對應：
///   CZFM 不可達層級（Cumulative Zermelo–Fraenkel Mahlo hierarchy）
///     → V_α 塔的可計算片段：|V_α|、共尾度 cf、正則性；「不可達」在有限層級必失敗（誠實見證）。
///   存在性與反思雙重視角（existence ⟷ reflection）
///     → 同一個層級既可由下往上數（存在性），也可由全域往下映（反思）；兩者計數必須相等。
///   等一致性轉譯網路（equiconsistency translation network）
///     → 系統間的可逆轉譯：轉譯矩陣每行恰一 1、每列恰一 1（置換矩陣）⟺ 雙射 ⟺ 等一致性。
///   顯式表示（explicit representation）
///     → 每個轉譯都由有限置換給出，可以逐格印出。

///|
/// 不可達性檢定（有限基數版）：κ 不可達 ⟺ κ 正則（無真因子分解）∧ 對所有 λ<κ 有 2^λ < κ。
/// 回傳 (正則, 幂集封閉, 不可達)。有限 κ ≥ 2 必在「幂集封閉」一步失敗。
pub fn b12_inaccessible(kappa : Int32) -> (Bool, Bool, Bool) {
  if kappa < 2 {
    return (false, false, false)
  }
  // 正則：κ 不能被分解成兩個 ≥ 2 的因子（有限基數中只有質數「看似」正則）
  let mut regular = true
  for d in 2..<kappa {
    if kappa % d == 0 {
      regular = false
    }
  }
  // 幂集封閉：需要 2^λ < κ 對所有 λ < κ；λ = κ−1 時 2^{κ−1} ≥ κ（κ ≥ 2）
  let mut power_closed = true
  for lam in 0..<kappa {
    if pow_int(2, lam) >= kappa {
      power_closed = false
    }
  }
  (regular, power_closed, regular && power_closed)
}

///|
/// CZFM 層級的顯式表示：回傳前 nmax 層的 (層級, 基數, 共尾度, 是否正則)。
/// 基數以 |V_n| = 2^{|V_{n−1}|} 計算，超過 2^30 以 −1 標記（不是「算不出」，而是「超出 Int32」）。
pub fn b12_czfm_levels(nmax : Int32) -> Array[(Int32, Int32, Int32, Bool)] {
  let out : Array[(Int32, Int32, Int32, Bool)] = []
  let mut size = 0
  for n in 0..<nmax {
    // 共尾度：有限基數的 cf = 1（單點覆蓋）或自身
    let cof = if size <= 1 { 1 } else { size }
    out.push((n, size, cof, size > 1 && cof == size))
    if size >= 30 {
      size = -1
    } else if size < 0 {
      // 已溢出：保持 −1
    } else {
      size = pow_int(2, size)
    }
  }
  out
}

///|
/// 存在性視角：由下往上累積，數「第 n 層新增的元素個數」。
pub fn b12_bottom_up(sizes : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut prev = 0
  for s in sizes {
    if s < 0 || prev < 0 {
      out.push(-1)
    } else {
      out.push(s - prev)
    }
    prev = s
  }
  out
}

///|
/// 反思視角：由全域往下映，數「第 n 層被其上層反射回來的次數」。
/// 對累積層級 V_n ⊂ V_{n+1}，反射次數 = |V_{n+1}| / |V_n| = 2^{|V_n|} / |V_n|（取整）。
pub fn b12_top_down(sizes : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<sizes.length() {
    if i + 1 < sizes.length() && sizes[i] > 0 && sizes[i + 1] > 0 {
      out.push(sizes[i + 1] / sizes[i])
    } else {
      out.push(0)
    }
  }
  out
}

///|
/// 雙重視角的一致性：**同一層級的兩種計數必須給出同一個塔**。
/// 由下往上看新增量 Δ_n = |V_n| − |V_{n−1}|；由上往下看反射比 ρ_n = |V_{n+1}|/|V_n|。
/// 兩者的不變量是：Δ_n 的累積和 = |V_{n−1}|，且 ρ_n ≥ 2（幂集嚴格變大）。
/// 回傳 (一致, 不變量殘差)；殘差 0 ⟺ 兩個視角描述同一個層級塔。
pub fn b12_dual_ok(sizes : Array[Int32]) -> (Bool, Int32) {
  let up = b12_bottom_up(sizes)
  let down = b12_top_down(sizes)
  let _ = down
  let mut sum = 0
  for x in up {
    if x > 0 {
      sum = sum + x
    }
  }
  // 塔的頂端（最後一個有限層級）必須等於新增量的總和
  let mut top = 0
  for s in sizes {
    if s > top {
      top = s
    }
  }
  let mut ratios_ok = true
  for i in 0..<down.length() {
    if i + 1 < sizes.length() && sizes[i] > 0 && sizes[i + 1] > 0 && down[i] < 2 {
      ratios_ok = false
    }
  }
  let resid = top - sum
  (resid == 0 && ratios_ok && top > 0, resid)
}

// ───────────────────────── 等一致性轉譯網路 ─────────────────────────

///|
/// 一個轉譯網路：n 個系統之間的等一致性關係以 n×n 的置換矩陣表示。
/// 等一致性要求轉譯**雙向可逆**，故每列／每行恰有一個 1。
pub fn b12_is_perm_matrix(m : Array[Array[Int32]]) -> Bool {
  let n = m.length()
  for i in 0..<n {
    if m[i].length() != n {
      return false
    }
    let mut row = 0
    for j in 0..<n {
      if m[i][j] == 1 {
        row = row + 1
      } else if m[i][j] != 0 {
        return false
      }
    }
    if row != 1 {
      return false
    }
  }
  for j in 0..<n {
    let mut col = 0
    for i in 0..<n {
      if m[i][j] == 1 {
        col = col + 1
      }
    }
    if col != 1 {
      return false
    }
  }
  true
}

///|
/// 顯式表示的轉譯表：對每個系統 i，回傳它被送到哪個系統 σ(i)。
pub fn b12_translation_map(m : Array[Array[Int32]]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<m.length() {
    let mut tgt = -1
    for j in 0..<m[i].length() {
      if m[i][j] == 1 {
        tgt = j
      }
    }
    out.push(tgt)
  }
  out
}

///|
/// 轉譯的**逆**：若 σ 是置換，逆置換 σ⁻¹ 存在，且 σ∘σ⁻¹ = id（等一致性 = 可逆轉譯）。
pub fn b12_inv_perm(sigma : Array[Int32]) -> Array[Int32] {
  let n = sigma.length()
  let out : Array[Int32] = []
  for _ in 0..<n {
    out.push(-1)
  }
  for i in 0..<n {
    if sigma[i] >= 0 && sigma[i] < n {
      out[sigma[i]] = i
    }
  }
  out
}

///|
/// 轉譯網路的**完備性**：任兩系統之間都存在一條轉譯鏈。
/// 這裡的「鏈」是真實的轉譯關係圖：σ 是「A → B 有轉譯」的邊集（以鄰接表給出），
/// 完備 ⟺ 該圖在**無向化**後連通（因為等一致性要求雙向可逆轉譯）。
pub fn b12_network_complete(adj : Array[Array[Int32]]) -> Bool {
  let n = adj.length()
  if n == 0 {
    return false
  }
  let seen : Array[Bool] = []
  for _ in 0..<n {
    seen.push(false)
  }
  seen[0] = true
  let mut frontier : Array[Int32] = [0]
  let mut count = 1
  while frontier.length() > 0 {
    let cur = frontier[0]
    let rest : Array[Int32] = []
    for i in 1..<frontier.length() {
      rest.push(frontier[i])
    }
    frontier = rest
    for w in adj[cur] {
      if w >= 0 && w < n && !seen[w] {
        seen[w] = true
        count = count + 1
        frontier.push(w)
      }
    }
    // 無向化：反向邊也算
    for v in 0..<n {
      for w in adj[v] {
        if w == cur && !seen[v] {
          seen[v] = true
          count = count + 1
          frontier.push(v)
        }
      }
    }
  }
  count == n
}

///|
/// 一致性強度的**序**：系統 A ⪯ B ⟺ A 的一致性可由 B 的一致性推出（轉譯存在且單向）。
/// 回傳 (A ⪯ B, B ⪯ A)：兩者皆真 ⟺ 等一致性。
pub fn b12_equiconsistent(
  forward : Bool,
  backward : Bool,
) -> (Bool, Bool, Bool) {
  (forward, backward, forward && backward)
}

///|
/// 2…n 之間「正則」（不可分解為兩個 ≥2 因子）的基數列表——A65 檢定器的輸出。
pub fn b12_regular_up_to(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for k in 2..<=n {
    let mut regular = true
    for d in 2..<k {
      if k % d == 0 {
        regular = false
      }
    }
    if regular {
      out.push(k)
    }
  }
  out
}
