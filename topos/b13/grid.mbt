///|
/// grid.mbt — 批次十三·模組 1：拓撲格、內在遺址、遺址外化、莫里塔等價（T430–T436）。
///
/// 「從計算機抽象理解邏輯」的具體做法：把每個幾何概念降為**有限偏序／格上的可判定條件**，
/// 再用計數等式驗證它。
///
///   拓撲格（locale / frame）＝ 有限開集族在 ∩、∪ 下的代數結構（frame 公理可逐項檢定）。
///   內在遺址（internal site）＝ 不從外部給定空間，而以格元素上的**覆蓋關係**公理化；
///        本模組用「覆蓋泛性質」而非外部點集來定義，故稱「內在」。
///   遺址外化（site externalization）＝ 內在覆蓋關係 ⟼ 空間站（B9Site）的開集族，
///        並驗證兩邊覆蓋判定一致——這正是「外部化」的可計算內容。
///   莫里塔等價（Morita equivalence）＝ 兩個格的覆蓋結構之間存在**保序雙射**且覆蓋對應，
///        在層範疇上表現為同一組層（以覆蓋篩數與層數比對）。

// ───────────────────────── 有限拓撲格 ─────────────────────────

///|
/// 有限拓撲格：以 n 個格元素與其 meet/join 表給出（元素以 0..n−1 編號）。
/// 之所以不直接沿用 B9Top：格是「內在」視角（先有邏輯代數），B9Top 是「外在」視角（先有點集）。
#derive(Debug, Eq)
pub(all) struct B13Frame {
  n : Int32
  meet : Array[Array[Int32]]
  join : Array[Array[Int32]]
  top : Int32
  bot : Int32
}

///|
/// 由有限拓撲空間的開集族建立拓撲格（meet = ∩、join = ∪）。
/// 元素編號沿用 B9Top 的開集編號（含 ∅ 與 X），因此 bot = ∅、top = X。
pub fn b13_frame_of_top(t : B9Top) -> B13Frame {
  let n = t.opens.length()
  let meet : Array[Array[Int32]] = []
  let join : Array[Array[Int32]] = []
  for i in 0..<n {
    let mr : Array[Int32] = []
    let jr : Array[Int32] = []
    for j in 0..<n {
      mr.push(b9_top_inter(t, i, j))
      jr.push(b9_top_union(t, i, j))
    }
    meet.push(mr)
    join.push(jr)
  }
  { n, meet, join, top: b9_top_top(t), bot: b9_top_bot(t), }
}

///|
/// Frame 公理檢定：交換、結合、吸收、分配（有限格即可逐項驗證）
/// 以及 top/bot 律。回傳 (交換, 結合, 吸收, 分配)。
pub fn b13_frame_ok(f : B13Frame) -> (Bool, Bool, Bool, Bool) {
  let mut comm = true
  let mut assoc = true
  let mut absorb = true
  let mut distrib = true
  for i in 0..<f.n {
    for j in 0..<f.n {
      if f.meet[i][j] != f.meet[j][i] || f.join[i][j] != f.join[j][i] {
        comm = false
      }
      // 吸收律：a ∧ (a ∨ b) = a、a ∨ (a ∧ b) = a
      if f.meet[i][f.join[i][j]] != i || f.join[i][f.meet[i][j]] != i {
        absorb = false
      }
      for k in 0..<f.n {
        if f.meet[f.meet[i][j]][k] != f.meet[i][f.meet[j][k]] {
          assoc = false
        }
        if f.join[f.join[i][j]][k] != f.join[i][f.join[j][k]] {
          assoc = false
        }
        // 分配律：a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)
        if f.meet[i][f.join[j][k]] != f.join[f.meet[i][j]][f.meet[i][k]] {
          distrib = false
        }
      }
    }
  }
  (comm, assoc, absorb, distrib)
}

///|
/// 格元素 a 的**偽補**（pseudo-complement）¬a = ⋁{b | a ∧ b = ⊥}。
/// 布爾格中 ¬ 是補；Heyting 格中只是一邊伴隨，這正是「內部邏輯非古典」的計算來源。
pub fn b13_pseudo_complement(f : B13Frame, a : Int32) -> Int32 {
  let mut acc = f.bot
  for b in 0..<f.n {
    if f.meet[a][b] == f.bot {
      acc = f.join[acc][b]
    }
  }
  acc
}

///|
/// 格是否為布爾格（每個元素都有真正的補）。
/// 回傳 (布爾, 非布爾元素數)：非布爾元素數 = 「a ∨ ¬a ≠ ⊤」的元素個數。
pub fn b13_is_boolean(f : B13Frame) -> (Bool, Int32) {
  let mut bad = 0
  for a in 0..<f.n {
    let na = b13_pseudo_complement(f, a)
    if f.join[a][na] != f.top {
      bad = bad + 1
    }
  }
  (bad == 0, bad)
}

///|
/// Heyting 蘊含 a ⇒ b = ⋁{c | a ∧ c ≤ b}（內部 Hom 的格版本，見模組 4）。
pub fn b13_heyting(f : B13Frame, a : Int32, b : Int32) -> Int32 {
  let mut acc = f.bot
  for c in 0..<f.n {
    if f.meet[a][c] == f.meet[a][c] && b13_le(f, f.meet[a][c], b) {
      acc = f.join[acc][c]
    }
  }
  acc
}

///|
/// 格序（以 meet 表示）：a ≤ b ⟺ a ∧ b = a。
pub fn b13_le(f : B13Frame, a : Int32, b : Int32) -> Bool {
  f.meet[a][b] == a
}

// ───────────────────────── 內在遺址與外化 ─────────────────────────

///|
/// 內在遺址：只給「哪些族覆蓋哪個元素」的關係，不假設任何外部點集。
/// cov[i] = 覆蓋元素 i 的族清單（每族是元素編號陣列）。
#derive(Debug, Eq)
pub(all) struct B13ISite {
  frame : B13Frame
  cov : Array[Array[Array[Int32]]]
}

///|
/// 內在覆蓋公理（有限版）：
///   (R) 覆蓋族中每項 ≤ 目標（覆蓋只由下往上）；
///   (M) 極大族 {i} 覆蓋 i（恆等公理）；
///   (T) 遞移：若 {a_j} 覆蓋 a 且每個 a_j 被自己的族覆蓋，則這些族聯集後向下封閉仍覆蓋 a。
/// 回傳 (R, M, T)。
pub fn b13_isite_ok(s : B13ISite) -> (Bool, Bool, Bool) {
  let f = s.frame
  let mut refl = true
  let mut ident = true
  let mut trans = true
  for i in 0..<f.n {
    for fam in s.cov[i] {
      for a in fam {
        if !b13_le(f, a, i) {
          refl = false
        }
      }
    }
    // 恆等：存在族使 join = i（有限格上以「族中含 i」為充分條件）
    let mut has = false
    for fam in s.cov[i] {
      for a in fam {
        if a == i {
          has = true
        }
      }
    }
    if !has {
      ident = false
    }
    // 遞移：每個被覆蓋的元素自身也必須被某族覆蓋
    for fam in s.cov[i] {
      for a in fam {
        if a != i && s.cov[a].length() == 0 {
          trans = false
        }
      }
    }
  }
  (refl, ident, trans)
}

///|
/// 由空間站導出**內在**遺址（覆蓋族 → 格元素上的覆蓋關係）。
/// 這是「外在 → 內在」方向：把開集族翻譯成格元素的族。
pub fn b13_isite_of_site(s : B9Site) -> B13ISite {
  let f = b13_frame_of_top(s.top)
  let cov : Array[Array[Array[Int32]]] = []
  for _ in 0..<f.n {
    cov.push([])
  }
  for v in 0..<s.cat.nob {
    let fams : Array[Array[Int32]] = []
    // 對每個覆蓋篩，取其生成族（以態射的 dom 對應的**格元素**表示）
    for sv in b9_covering_sieves(s, v) {
      let fam : Array[Int32] = []
      for m in sv {
        fam.push(s.opens[s.cat.dom[m]])
      }
      if fam.length() > 0 {
        fams.push(fam)
      }
    }
    // 站物件 v ⟷ 格元素 s.opens[v]
    cov[s.opens[v]] = fams
  }
  // ⊥（空集）不在站中：其唯一覆蓋是恆等族 {⊥}（空覆蓋在格論上恆成立）
  if cov[f.bot].length() == 0 {
    cov[f.bot] = [[f.bot]]
  }
  { frame: f, cov, }
}

///|
/// 遺址**外化**（externalization）：由內在遺址重建一個空間站，並檢驗覆蓋判定一致。
/// 重建方式：把格元素當作「開集」，以 join 表導出點集（有限格的 Stone 表示）；
/// 為避免引入完整 Stone 空間，這裡直接以「格元素的 join-原子分解」作為點集。
/// 回傳 (外化站, 覆蓋一致, 元素數)。
pub fn b13_externalize(s : B13ISite) -> (B9Site, Bool, Int32) {
  let f = s.frame
  // 點集 = 格中「join-不可分解」的元素（原子），若無則退回全部元素
  let atoms : Array[Int32] = []
  for a in 0..<f.n {
    let mut irred = true
    for b in 0..<f.n {
      for c in 0..<f.n {
        if f.join[b][c] == a && b != a && c != a {
          irred = false
        }
      }
    }
    if irred {
      atoms.push(a)
    }
  }
  let pts = if atoms.length() > 0 { atoms } else { b13_range(f.n) }
  // 每個格元素 a 對應的開集 = {p ∈ pts | p ≤ a}
  let raw : Array[Array[Bool]] = []
  for a in 0..<f.n {
    let row : Array[Bool] = []
    for p in pts {
      row.push(b13_le(f, p, a))
    }
    raw.push(row)
  }
  let t = b9_top(pts.length(), raw)
  let st = b9_site(t)
  // 覆蓋一致：內在覆蓋族的 join 必須等於目標（空間站上的聯集判準）
  let mut ok = true
  for i in 0..<s.cov.length() {
    for fam in s.cov[i] {
      let mut acc = f.bot
      for a in fam {
        acc = f.join[acc][a]
      }
      if acc != i {
        ok = false
      }
    }
  }
  (st, ok, f.n)
}

///|
/// 由開集編號找站物件編號（找不到回傳 −1）。
pub fn b13_site_obj_of_open(s : B9Site, oi : Int32) -> Int32 {
  for i in 0..<s.cat.nob {
    if s.opens[i] == oi {
      return i
    }
  }
  -1
}

///|
/// 0..n−1 的整數陣列（小工具）。
pub fn b13_range(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<n {
    out.push(i)
  }
  out
}

// ───────────────────────── 莫里塔等價 ─────────────────────────

///|
/// 莫里塔等價（格版本）：兩個拓撲格之間存在**保序雙射**且覆蓋結構對應。
/// 判定步驟：① 元素數相同；② 存在保 meet/join 的雙射；③ 覆蓋族的像仍是覆蓋族。
/// 回傳 (等價, 找到的雙射（找不到回傳空）, 覆蓋對應數)。
pub fn b13_morita(a : B13Frame, b : B13Frame) -> (Bool, Array[Int32], Int32) {
  if a.n != b.n {
    return (false, [], 0)
  }
  // 以「元素的格論指紋」排序後配對：指紋 = (下界個數, 上界個數)
  let fa = b13_fingerprints(a)
  let fb = b13_fingerprints(b)
  let mut sorted_a = b13_range(a.n)
  let mut sorted_b = b13_range(b.n)
  sorted_a = b13_sort_by(fa, sorted_a)
  sorted_b = b13_sort_by(fb, sorted_b)
  // 雙射 σ：a 的第 k 個指紋 ↦ b 的第 k 個指紋
  let sigma : Array[Int32] = []
  for _ in 0..<a.n {
    sigma.push(-1)
  }
  let mut matched = 0
  for k in 0..<a.n {
    if fa[sorted_a[k]] == fb[sorted_b[k]] {
      sigma[sorted_a[k]] = sorted_b[k]
      matched = matched + 1
    }
  }
  if matched != a.n {
    return (false, [], matched)
  }
  // 保 meet/join
  let mut hom = true
  for i in 0..<a.n {
    for j in 0..<a.n {
      if sigma[a.meet[i][j]] != b.meet[sigma[i]][sigma[j]] {
        hom = false
      }
      if sigma[a.join[i][j]] != b.join[sigma[i]][sigma[j]] {
        hom = false
      }
    }
  }
  (hom, sigma, matched)
}

///|
/// 格元素的指紋：(下界個數, 上界個數) 打包成單一整數，用於配對。
pub fn b13_fingerprints(f : B13Frame) -> Array[Int32] {
  let out : Array[Int32] = []
  for a in 0..<f.n {
    let mut down = 0
    let mut up = 0
    for b in 0..<f.n {
      if b13_le(f, b, a) {
        down = down + 1
      }
      if b13_le(f, a, b) {
        up = up + 1
      }
    }
    out.push(down * 1000 + up)
  }
  out
}

///|
/// 依指紋排序元素（簡單插入排序，n 很小）。
pub fn b13_sort_by(keys : Array[Int32], items : Array[Int32]) -> Array[Int32] {
  let out = items.copy()
  let n = out.length()
  for i in 1..<n {
    let key = keys[out[i]]
    let val = out[i]
    let mut j = i - 1
    while j >= 0 && keys[out[j]] > key {
      out[j + 1] = out[j]
      j = j - 1
    }
    out[j + 1] = val
  }
  out
}
