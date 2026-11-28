///|
/// kpm.mbt — 批次十二·模組 3：**KPM 標記、弱馬洛記號與多層塌縮**（T419–T422、A71–A73）。
///
/// 名詞對應：
///   KPM 標記（Kripke–Platek + Mahlo）：以「容許序數」為載體的證明論標記。
///     → 可計算版本：容許判定 α 是否封閉於 Σ₁ 函數（有限層級必失敗，誠實見證）。
///   弱馬洛記號（weak Mahlo notation）：以「Π₃-反射」標記的序數記號系統。
///     → 可計算版本：記號系統 (ord, kind, level) 的比較與唯一性檢核。
///   多層塌縮函數（multi-layer collapsing）：把高層記號塌回可數層的 ψ 函數。
///     → 可計算版本：ψ 的遞歸定義＋塌縮不動點計數。
///   n-馬洛／ω-馬洛：以「其下馬洛數的個數」分級的強度階梯。
///     → 可計算版本：強度階梯的計數與單調性。
///   Σ_n-正確（Σ_n-correct）：模型與真實層級對 Σ_n 句子的判定一致。
///     → 可計算版本：對前 n 層做 Σ_n 真值表比對，計數一致項。

// ───────────────────────── KPM 標記 ─────────────────────────

///|
/// 容許序數判定（有限版）：α 容許 ⟺ α 是極限序數 ∧ 封閉於 Σ₁ 可定義函數。
/// 有限序數（以 Int32 表示）只有 0 是極限，而 0 不含任何元素 ⇒ 無有限容許序數。
/// 回傳 (極限, Σ₁ 封閉, 容許)。
pub fn b12_admissible(alpha : Int32) -> (Bool, Bool, Bool) {
  if alpha <= 0 {
    return (false, false, false)
  }
  // 有限序數皆有前驅 ⇒ 非極限
  (false, false, false)
}

///|
/// KPM 標記：以 (alpha, kp_level, mahlo_level) 三元組表示一個證明論標記，
/// 回傳是否為**良形成**（well-formed）的標記：層級皆非負且 kp ≤ mahlo。
pub fn b12_kpm_mark(
  alpha : Int32,
  kp_level : Int32,
  mahlo_level : Int32,
) -> Bool {
  alpha >= 0 && kp_level >= 0 && mahlo_level >= 0 && kp_level <= mahlo_level
}

///|
/// 標記的字典序比較（標記系統的「序」必須是全序且與強度一致）。
pub fn b12_kpm_cmp(
  a : (Int32, Int32, Int32),
  b : (Int32, Int32, Int32),
) -> Int32 {
  if a.0 != b.0 {
    return if a.0 < b.0 { -1 } else { 1 }
  }
  if a.1 != b.1 {
    return if a.1 < b.1 { -1 } else { 1 }
  }
  if a.2 != b.2 {
    return if a.2 < b.2 { -1 } else { 1 }
  }
  0
}

// ───────────────────────── 弱馬洛記號 ─────────────────────────

///|
/// 弱馬洛記號系統：以「Π₃-反射」標記的 (base, reflect_index)。
/// 回傳 (良形成, 記號值 = base·ω + reflect_index 的有限近似)。
pub fn b12_weak_mahlo_notation(
  base : Int32,
  reflect_index : Int32,
) -> (Bool, Int32) {
  let ok = base >= 0 && reflect_index >= 0
  (ok, base * 8 + reflect_index)
}

///|
/// 記號系統的**唯一性**：不同 (base, index) 必須給出不同記號值（單射）。
pub fn b12_notation_injective(pairs : Array[(Int32, Int32)]) -> Bool {
  let vals : Array[Int32] = []
  for (b, i) in pairs {
    vals.push(b12_weak_mahlo_notation(b, i).1)
  }
  for i in 0..<vals.length() {
    for j in (i + 1)..<vals.length() {
      if vals[i] == vals[j] {
        return false
      }
    }
  }
  true
}

// ───────────────────────── 多層塌縮 ─────────────────────────

///|
/// 多層塌縮函數 ψ：把第 k 層的記號塌到第 k−1 層。
/// 定義：ψ_k(0) = 弱馬洛記號值；ψ_k(n+1) = ψ_k(n) 的最小不動點（以 +1 迭代逼近）。
/// 回傳塌縮後的序列（長度 steps）。
pub fn b12_collapse(level : Int32, base : Int32, steps : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut cur = b12_weak_mahlo_notation(base, level).1
  for _ in 0..<steps {
    out.push(cur)
    // 塌縮一步：取「其下不動點」的計數（此處以 level 遞減的 2 的幂量化）
    if level <= 0 {
      // 第 0 層的塌縮是「共尾度」：有限序數上為恆等 ⇒ 整段序列不動（真不動點）
    } else {
      cur = cur + pow_int(2, level)
    }
  }
  out
}

///|
/// 塌縮的**不動點計數**：ψ 在 [0, n) 上的不動點個數（cur == collapsed(cur) 的項）。
pub fn b12_collapse_fixpoints(
  level : Int32,
  base : Int32,
  steps : Int32,
) -> Int32 {
  let seq = b12_collapse(level, base, steps)
  let mut n = 0
  for i in 0..<seq.length() {
    if i + 1 < seq.length() && seq[i] == seq[i + 1] {
      n = n + 1
    }
  }
  n
}

// ───────────────────────── 馬洛強度階梯 ─────────────────────────

///|
/// n-馬洛：κ 是 n-馬洛 ⟺ κ 是其下的 (n−1)-馬洛基數的駐集極限。
/// 0-馬洛 = 不可達，1-馬洛 = 馬洛。
/// 回傳 (良形成, 該級要求其下「較低級」的個數)。
pub fn b12_n_mahlo(n : Int32) -> (Bool, Int32) {
  if n < 0 {
    return (false, 0)
  }
  (true, n)
}

///|
/// ω-馬洛：對所有 n < ω 都是 n-馬洛。
/// 回傳 (是否 ω-馬洛的模型, 檢查的級數)：模型以「階梯是否覆蓋所有有限級」判定。
pub fn b12_omega_mahlo(strength_ladder : Array[Int32]) -> (Bool, Int32) {
  let mut ok = strength_ladder.length() > 0
  let mut n = 0
  for s in strength_ladder {
    if s < n {
      ok = false
    }
    n = n + 1
  }
  (ok, n)
}

///|
/// 強度階梯的計數：第 k 級要求在 κ 之下有 k 個較低級別的駐集。
pub fn b12_strength_ladder(kmax : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for k in 0..<kmax {
    out.push(k)
  }
  out
}

// ───────────────────────── Σ_n-正確 ─────────────────────────

///|
/// Σ_n-正確：模型 M 與真實層級 V 對所有 Σ_n 句子判定相同。
/// 可計算版本：真值表以「級 → 該級 Σ_n 句子的真值(0/1)」給出（Array[Array[Int32]]）。
/// 要求：第 1…n−1 級逐項全等；第 n 級只要求**同真值**（不要求 Π_{n+1}）。
/// 回傳 (一致, 前 n 級一致項數, 第 n 級的差異數)。
pub fn b12_sigma_n_correct(
  model : Array[Array[Int32]],
  real : Array[Array[Int32]],
  n : Int32,
) -> (Bool, Int32, Int32) {
  let up_to = if n < model.length() { n } else { model.length() }
  if up_to <= 0 {
    return (false, 0, 0)
  }
  let mut agree = 0
  for i in 0..<up_to {
    if i < real.length() && b12_sigma_same(model[i], real[i]) {
      agree = agree + 1
    }
  }
  // 第 n 級（0-based 的 n−1 級）以下的每一級都必須逐項相同
  let (same_level, diff) = if n - 1 < model.length() && n - 1 < real.length() {
    let s = b12_sigma_agree(model[n - 1], real[n - 1])
    (s.0, s.1)
  } else {
    (false, 0)
  }
  // 若第 n 級已經失配，就把該級的差異數一併回報（不再重覆計入 agree）
  let agree2 = if agree == up_to && !same_level { agree - 1 } else { agree }
  (agree == up_to && same_level, agree2, diff)
}

///|
/// 逐項相等（級內真值表）。
pub fn b12_sigma_same(a : Array[Int32], b : Array[Int32]) -> Bool {
  @common.b_sh_arr_eq(a, b)
}

///|
/// 同一級內的差異計數（含長度差）。
pub fn b12_sigma_agree(a : Array[Int32], b : Array[Int32]) -> (Bool, Int32) {
  let k = if a.length() < b.length() { a.length() } else { b.length() }
  let mut diff = 0
  for i in 0..<k {
    if a[i] != b[i] {
      diff = diff + 1
    }
  }
  diff = diff +
    (if a.length() > b.length() {
      a.length() - b.length()
    } else {
      b.length() - a.length()
    })
  (diff == 0 && k > 0, diff)
}

///|
/// 列維綱領 Λ（Levy hierarchy / Lévy absoluteness program）：
/// 對 Σ₁ 句子，絕對性（absoluteness）成立 ⟺ 轉移到遞移模型時真值不變。
/// 可計算版本：對給定的 Σ₁ 見證表，檢查每個見證都被遞移模型保留。
/// 回傳 (絕對, 保留的見證數, 遺失的見證數)。
pub fn b12_levy_lambda(
  witnesses : Array[Int32],
  model_members : Array[Int32],
) -> (Bool, Int32, Int32) {
  let mut kept = 0
  let mut lost = 0
  for w in witnesses {
    let mut found = false
    for m in model_members {
      if m == w {
        found = true
      }
    }
    if found {
      kept = kept + 1
    } else {
      lost = lost + 1
    }
  }
  (lost == 0 && witnesses.length() > 0, kept, lost)
}

///|
/// Σ₁-可定義的無界閉集（Σ₁-definable unbounded closed set, 記 CU）：
/// 在序數上，C 無界閉 ⟺ 無界（∀α ∃β>α, β∈C）∧ 對極限取封閉。
/// 可計算版本：以有限片段 [0, n) 檢查「無界」與「極限封閉」兩條。
/// 回傳 (無界, 極限封閉, CU 成立)。
pub fn b12_club_set(members : Array[Bool]) -> (Bool, Bool, Bool) {
  let n = members.length()
  if n == 0 {
    return (false, false, false)
  }
  // 無界：最後一段必須有成員（有限截斷下的「無界」= 尾部非空）
  let mut unbounded = false
  for i in 0..<n {
    if members[i] {
      unbounded = true
    }
  }
  // 極限封閉：若所有 < i 的項都在 C 中，則 i 也在 C 中
  let mut closed = true
  for i in 1..<n {
    let mut all_prev = true
    for j in 0..<i {
      if !members[j] {
        all_prev = false
      }
    }
    if all_prev && !members[i] {
      closed = false
    }
  }
  (unbounded, closed, unbounded && closed)
}

///|
/// Σ₁-可定義的無界閉集的**生成器**：從種子集合出發，反覆加入極限點，直到不動點。
/// 回傳最終集合（長度固定為 n）。
pub fn b12_club_closure(seed : Array[Bool]) -> Array[Bool] {
  let n = seed.length()
  let out : Array[Bool] = []
  for i in 0..<n {
    out.push(seed[i])
  }
  let mut changed = true
  while changed {
    changed = false
    for i in 1..<n {
      let mut all_prev = true
      for j in 0..<i {
        if !out[j] {
          all_prev = false
        }
      }
      if all_prev && !out[i] {
        out[i] = true
        changed = true
      }
    }
  }
  out
}
