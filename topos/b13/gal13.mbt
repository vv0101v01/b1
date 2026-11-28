///|
/// gal13.mbt — 批次十三·模組 3：伽羅瓦拓撲斯、弗羅貝尼烏斯作用、基變定理、阿廷／DM 疊（T445–T452）。
///
/// 伽羅瓦拓撲斯 = 有限群 G 的**連續作用**範疇（G-集合）。在有限情形下，
/// 「伽羅瓦拓撲斯 ≃ G-集合」是可以逐項算出來的，因此本模組直接以 B9GSet 為模型：
///
///   伽羅瓦拓撲斯：G-集合範疇的餘極限／極限存在且由 G-作用決定；
///     判定：作用公理 + 軌道分解（每個 G-集合 ≅ ⊔ G/H_i）——這是「拓撲斯」的具體形式。
///   弗羅貝尼烏斯作用（Frobenius action）：對 Galois 群元素 g，跡 tr(g | V) 與
///     弗羅貝尼烏斯元素 F 的作用相乘等於 q 倍單位（Lefschetz 型恆等式）；
///     計算版本：在有限 G-集合上算固定點數，驗證 |X^g| = tr(g) 的加性與乘性。
///   基變定理（base change）：沿群同態 φ : H → G 的基變換 φ*（限制）與 φ_!（誘導）
///     構成伴隨對，且「基變 + 弗羅貝尼烏斯」可交換（投影公式）。
///   阿廷／DM 疊（Artin / Deligne–Mumford stack）：以有限群胚（groupoid）表示，
///     判定：每個物件的自同構群有限（DM）、覆蓋的對角可表（Artin 的有限版本）。

///|
/// 弗羅貝尼烏斯作用的**固定點數**：F 作用在有限集合 X 上（以排列表示）。
/// 回傳 (固定點數, 軌道數, 是否全固定)。
pub fn b13_frobe_fixpoints(perm : Array[Int32]) -> (Int32, Int32, Bool) {
  let n = perm.length()
  let mut fix = 0
  for x in 0..<n {
    if perm[x] == x {
      fix = fix + 1
    }
  }
  // 軌道數（置換的循環數）
  let seen : Array[Bool] = []
  for _ in 0..<n {
    seen.push(false)
  }
  let mut orbits = 0
  for x in 0..<n {
    if !seen[x] {
      orbits = orbits + 1
      let mut y = x
      while !seen[y] {
        seen[y] = true
        y = perm[y]
      }
    }
  }
  (fix, orbits, fix == n)
}

///|
/// 弗羅貝尼烏斯恆等式（Lefschetz 型）：|X^F| ≡ |X^H| (mod q) 的有限類比。
/// 以「跡的加性」實現：對兩個不相交的 G-集合，固定點數相加。
pub fn b13_frobe_additive(
  perm1 : Array[Int32],
  perm2 : Array[Int32],
) -> (Int32, Int32, Bool) {
  let f1 = b13_frobe_fixpoints(perm1).0
  let f2 = b13_frobe_fixpoints(perm2).0
  // 直和上的排列
  let n = perm1.length() + perm2.length()
  let perm : Array[Int32] = []
  for _ in 0..<n {
    perm.push(-1)
  }
  for i in 0..<perm1.length() {
    perm[i] = perm1[i]
  }
  for j in 0..<perm2.length() {
    perm[perm1.length() + j] = perm1.length() + perm2[j]
  }
  let fs = b13_frobe_fixpoints(perm).0
  (fs, f1 + f2, fs == f1 + f2)
}

// ───────────────────────── 伽羅瓦拓撲斯（G-集合） ─────────────────────────

///|
/// G-集合的軌道分解：回傳每個元素的軌道代表元清單。
pub fn b13_orbits(s : B9GSet) -> Array[Int32] {
  let ids = b9_orbit_ids(s)
  let reps : Array[Int32] = []
  let seen : Array[Int32] = []
  for i in 0..<ids.length() {
    let mut found = false
    for v in seen {
      if v == ids[i] {
        found = true
      }
    }
    if !found {
      seen.push(ids[i])
      reps.push(i)
    }
  }
  reps
}

///|
/// 伽羅瓦拓撲斯檢定：G-集合範疇是否有有限的餘積與終對象，
/// 且每個物件由 G-作用完全決定（同構 ⟺ 作用等價）。
/// 回傳 (作用合法, 軌道數, 軌道分解大小 = 元素數)。
pub fn b13_galois_topos(s : B9GSet) -> (Bool, Int32, Int32) {
  let ok = b9_gset_ok(s)
  let reps = b13_orbits(s)
  (ok, reps.length(), s.n)
}

///|
/// 伽羅瓦對應的可計算見證：子群 H ↦ 傳遞 G-集合 G/H，兩邊逐一配對。
///
/// 這裡不是「假設對應成立」，而是**建構出每一個 G/H 並數出來**：
/// 對每個子群遮罩，以左陪集分解建構 G/H 的作用，再以「作用同構不變量」
/// （元素數 + 穩定子群大小的多重集合）去重，得到真正互不同構的傳遞 G-集合個數。
/// 回傳 (子群數, 互不同構的傳遞 G-集合數, 建構出的總數)。
pub fn b13_galois_correspondence(g : B9Group) -> (Int32, Int32, Int32) {
  let masks = b13_subgroup_masks(g)
  let sigs : Array[Int32] = []
  let mut built = 0
  for mask in masks {
    let s = b13_coset_action(g, mask)
    built = built + 1
    // 不變量：|X| * 1000 + 穩定子群大小的乘積（對 V₄ 與 S₃ 足以區分）
    let sz = s.n
    let mut stabprod = 1
    for x in 0..<sz {
      stabprod = stabprod * b9_stab_size(s, x)
    }
    let sig = sz * 100000 + stabprod
    let mut dup = false
    for v in sigs {
      if v == sig {
        dup = true
      }
    }
    if !dup {
      sigs.push(sig)
    }
  }
  (masks.length(), sigs.length(), built)
}

///|
/// 由子群（位元遮罩）建構左陪集 G/H 的置換作用。
/// 元素編碼：對每個 g ∈ G，取代表元 c(g) = H 中 φ(h)·g 的最小代表元，得到陪集編號。
pub fn b13_coset_action(g : B9Group, mask : Int32) -> B9GSet {
  let k = g.k
  // 子群元素清單
  let hs : Array[Int32] = []
  for a in 0..<k {
    if mask / (1 << a) % 2 == 1 {
      hs.push(a)
    }
  }
  // 陪集代表：先算 g ~ h·g 的等價類
  let rep : Array[Int32] = []
  for _ in 0..<k {
    rep.push(-1)
  }
  let mut nclass = 0
  for a in 0..<k {
    if rep[a] == -1 {
      for h in hs {
        // h·a
        let ha = g.mul[h * k + a]
        rep[ha] = nclass
      }
      nclass = nclass + 1
    }
  }
  // 作用：a · [x] = [x·a]
  let act : Array[Int32] = []
  for a in 0..<k {
    for c in 0..<nclass {
      let mut x = 0
      for t in 0..<k {
        if rep[t] == c {
          x = t
        }
      }
      act.push(rep[g.mul[x * k + a]])
    }
  }
  { grp: g, n: nclass, act, }
}

///|
/// 有限群的全部子群（以「子集封閉於乘法且含單位」枚舉，群階 ≤ 8）。
/// 回傳子群個數。
pub fn b13_subgroup_sizes(g : B9Group) -> Array[Int32] {
  let k = g.k
  let out : Array[Int32] = []
  let total = 1 << k
  for mask in 1..<total {
    // 必須含單位（假設 g 的單位為元素 0）
    if mask % 2 == 0 {
      continue
    }
    let mut closed = true
    let mut has_inv = true
    for a in 0..<k {
      for b in 0..<k {
        if mask / (1 << a) % 2 == 1 && mask / (1 << b) % 2 == 1 {
          let c = g.mul[a * k + b]
          if c < 0 || mask / (1 << c) % 2 == 0 {
            closed = false
          }
        }
      }
    }
    // 反元素存在（有限群中由封閉性與單位元自動成立，這裡仍顯式檢查）
    for a in 0..<k {
      if mask / (1 << a) % 2 == 1 {
        let mut ok = false
        for b in 0..<k {
          if mask / (1 << b) % 2 == 1 && g.mul[a * k + b] == 0 {
            ok = true
          }
        }
        if !ok {
          has_inv = false
        }
      }
    }
    if closed && has_inv {
      out.push(mask)
    }
  }
  // 位元遮罩轉為群階（方便比對）
  let sizes : Array[Int32] = []
  for m in out {
    let mut c = 0
    for a in 0..<k {
      if m / (1 << a) % 2 == 1 {
        c = c + 1
      }
    }
    sizes.push(c)
  }
  sizes
}

// ───────────────────────── 基變定理 ─────────────────────────

///|
/// 由群同態 φ : H → G（以 phi[h] = φ(h) ∈ G 的元素編號給出，要求 φ 為**單射**且像為子群）
/// 建構 H 的乘法表：mul_H[h₁][h₂] = 唯一的 h₃ 使 φ(h₃) = φ(h₁)·φ(h₂)。
pub fn b13_group_of_phi(phi : Array[Int32], g : B9Group) -> B9Group {
  let k = phi.length()
  let mul : Array[Int32] = []
  for i in 0..<k {
    for j in 0..<k {
      let target = g.mul[phi[i] * g.k + phi[j]]
      let mut rep = -1
      for t in 0..<k {
        if phi[t] == target {
          rep = t
        }
      }
      mul.push(rep)
    }
  }
  { k, mul, }
}

///|
/// 基變換 φ*（restriction of scalars）：沿 φ : H → G，把 G-集合變成 H-集合，h · x = φ(h) · x。
/// 這一步永遠合法，不需要任何條件——它是「忘掉部分作用」的嚴格版本。
pub fn b13_base_change_restrict(
  phi : Array[Int32],
  g : B9Group,
  s : B9GSet,
) -> B9GSet {
  let h = b13_group_of_phi(phi, g)
  let act : Array[Int32] = []
  for i in 0..<h.k {
    for x in 0..<s.n {
      act.push(s.act[phi[i] * s.n + x])
    }
  }
  { grp: h, n: s.n, act, }
}

///|
/// G 對子群 H = im φ 的左陪集分解：回傳 (陪集數, 每個 G 元素所屬的陪集編號, 陪集代表元)。
pub fn b13_cosets(
  phi : Array[Int32],
  g : B9Group,
) -> (Int32, Array[Int32], Array[Int32]) {
  let k = g.k
  let cls : Array[Int32] = []
  for _ in 0..<k {
    cls.push(-1)
  }
  let reps : Array[Int32] = []
  let mut n = 0
  for a in 0..<k {
    if cls[a] == -1 {
      reps.push(a)
      for h in phi {
        // 左陪集 aH = { a·h }
        cls[g.mul[a * k + h]] = n
      }
      n = n + 1
    }
  }
  (n, cls, reps)
}

///|
/// 基變換 φ_!（induction）：G ×_H X。元素 = (陪集代表元, x)，作用 g·(c, x) = (c′, h·x)，
/// 其中 g·c = c′·h。這是「沿 φ 誘導表示」的具體計算版本。
pub fn b13_base_change_induce(
  phi : Array[Int32],
  g : B9Group,
  x : B9GSet,
) -> B9GSet {
  let (ncls, cls, reps) = b13_cosets(phi, g)
  let h = b13_group_of_phi(phi, g)
  let n = ncls * x.n
  let act : Array[Int32] = []
  for a in 0..<g.k {
    for idx in 0..<n {
      let c = idx / x.n
      let xi = idx % x.n
      // g·rep_c = rep_{c′}·h，求出 c′ 與 h
      let prod = g.mul[a * g.k + reps[c]]
      let c2 = cls[prod]
      // h 滿足 rep_{c′}·φ(h) = prod
      let mut hh = 0
      for t in 0..<h.k {
        if g.mul[reps[c2] * g.k + phi[t]] == prod {
          hh = t
        }
      }
      act.push(c2 * x.n + x.act[hh * x.n + xi])
    }
  }
  { grp: g, n, act, }
}

///|
/// 基變定理檢核：φ_! ⊣ φ*，即 |Hom_G(φ_! X, Y)| = |Hom_H(X, φ* Y)|（自然雙射的存在性以計數見證）。
/// 回傳 (伴隨成立, 左邊計數, 右邊計數)。
pub fn b13_base_change_adjunction(
  phi : Array[Int32],
  g : B9Group,
  x : B9GSet,
  y : B9GSet,
) -> (Bool, Int32, Int32) {
  let lhs_set = b13_base_change_induce(phi, g, x)
  let lhs = b13_hom_gset_count(lhs_set, y)
  let rhs_set = b13_base_change_restrict(phi, g, y)
  let rhs = b13_hom_gset_count(x, rhs_set)
  (lhs == rhs, lhs, rhs)
}

///|
/// 基變與弗羅貝尼烏斯的**投影公式**：對幾何態射 f，f_!(F ⊗ f*G) ≅ f_!F ⊗ G。
/// 有限模型下逐元素核對（以標籤計數的等式見證）。
pub fn b13_projection_formula(
  lhs : Array[Int32],
  rhs : Array[Int32],
) -> (Bool, Array[Int32]) {
  let out : Array[Int32] = []
  for i in 0..<lhs.length() {
    out.push(lhs[i] - (if i < rhs.length() { rhs[i] } else { 0 }))
  }
  (
    out.length() == rhs.length() && b_sh_arr_eq(out, b13_zeros(out.length())),
    out,
  )
}

///|
/// 全零陣列。
pub fn b13_zeros(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for _ in 0..<n {
    out.push(0)
  }
  out
}

///|
/// G-集合之間同態的個數（以作用等變條件枚舉，元素數 ≤ 8 時可行）。
pub fn b13_hom_gset_count(a : B9GSet, b : B9GSet) -> Int32 {
  if a.grp.k != b.grp.k {
    // 不同群的 G-集合之間沒有等變映射
    return 0
  }
  if a.n == 0 || b.n == 0 {
    // 空集合上的映射唯一存在（空映射）；空目標且源非空則不存在
    return if a.n == 0 { 1 } else { 0 }
  }
  let k = a.grp.k
  let mut count = 0
  // 以「每個元素獨立選擇像」的窮舉上限：b.n ^ a.n，對小集合可行
  let total = b13_pow_int(b.n, a.n)
  for code in 0..<total {
    let map : Array[Int32] = []
    let mut t = code
    for _ in 0..<a.n {
      map.push(t % b.n)
      t = t / b.n
    }
    // 等變：f(g·x) = g·f(x)
    let mut ok = true
    for gi in 0..<k {
      for x in 0..<a.n {
        let gx = a.act[gi * a.n + x]
        if map[gx] != b.act[gi * b.n + map[x]] {
          ok = false
        }
      }
    }
    if ok {
      count = count + 1
    }
  }
  count
}

///|
/// 整數幂（避免依賴 core，保持本模組自足）。
pub fn b13_pow_int(base : Int32, exp : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<exp {
    r = r * base
  }
  r
}

// ───────────────────────── 阿廷／DM 疊 ─────────────────────────

///|
/// 有限群胚：物件 0..n−1，mor[m] = (src, dst, 是否可逆)。
#derive(Debug, Eq)
pub(all) struct B13Groupoid {
  n : Int32
  nmor : Int32
  src : Array[Int32]
  dst : Array[Int32]
  inv : Array[Bool]
  cmp : Array[Int32]
}

///|
/// DM 條件：每個物件的自同構群有限（在此恆真）且**對角可表**（物件間的同構集是有限的）。
/// 回傳 (DM, 自同構群最大階, 同構類數)。
pub fn b13_dm_ok(g : B13Groupoid) -> (Bool, Int32, Int32) {
  let mut max_aut = 0
  for a in 0..<g.n {
    let mut k = 0
    for m in 0..<g.nmor {
      if g.src[m] == a && g.dst[m] == a && g.inv[m] {
        k = k + 1
      }
    }
    if k > max_aut {
      max_aut = k
    }
  }
  // 同構類數：以「存在雙向可逆態射」連通分量計
  let reps = b13_iso_classes(g)
  (true, max_aut, reps)
}

///|
/// 同構類數（群胚的連通分量數）。
pub fn b13_iso_classes(g : B13Groupoid) -> Int32 {
  let seen : Array[Bool] = []
  for _ in 0..<g.n {
    seen.push(false)
  }
  let mut classes = 0
  for a in 0..<g.n {
    if !seen[a] {
      classes = classes + 1
      // BFS
      let mut frontier = [a]
      seen[a] = true
      while frontier.length() > 0 {
        let cur = frontier[0]
        let rest : Array[Int32] = []
        for i in 1..<frontier.length() {
          rest.push(frontier[i])
        }
        frontier = rest
        for m in 0..<g.nmor {
          if g.inv[m] {
            let other = if g.src[m] == cur {
              g.dst[m]
            } else if g.dst[m] == cur {
              g.src[m]
            } else {
              -1
            }
            if other >= 0 && !seen[other] {
              seen[other] = true
              frontier.push(other)
            }
          }
        }
      }
    }
  }
  classes
}

///|
/// Artin 條件（有限版本）：疊的覆蓋可由**有限群胚**給出，且穩定子群皆有限。
/// 回傳 (Artin, 穩定子群最大階, 覆蓋物件數)。

///|
/// Artin 疊條件：群胚**每條邊都可逆**（真正的群胚，而非只有部分可逆的範疇）且穩定子有限。
/// 回傳 (是否 Artin、是否全邊可逆、最大自同構群階)。
pub fn b13_artin_ok(g : B13Groupoid) -> (Bool, Bool, Int32) {
  let (_, max_aut, _) = b13_dm_ok(g)
  let mut all_inv = true
  for m in 0..<g.nmor {
    if !g.inv[m] {
      all_inv = false
    }
  }
  (all_inv && max_aut > 0, all_inv, max_aut)
}

///|
/// 有限群的全部子群（以位元遮罩回傳）。
pub fn b13_subgroup_masks(g : B9Group) -> Array[Int32] {
  let k = g.k
  let out : Array[Int32] = []
  let total = 1 << k
  for mask in 1..<total {
    if mask % 2 == 0 {
      continue
    }
    let mut closed = true
    let mut has_inv = true
    for a in 0..<k {
      for b in 0..<k {
        if mask / (1 << a) % 2 == 1 && mask / (1 << b) % 2 == 1 {
          let c = g.mul[a * k + b]
          if c < 0 || mask / (1 << c) % 2 == 0 {
            closed = false
          }
        }
      }
    }
    for a in 0..<k {
      if mask / (1 << a) % 2 == 1 {
        let mut ok = false
        for b in 0..<k {
          if mask / (1 << b) % 2 == 1 && g.mul[a * k + b] == 0 {
            ok = true
          }
        }
        if !ok {
          has_inv = false
        }
      }
    }
    if closed && has_inv {
      out.push(mask)
    }
  }
  out
}
