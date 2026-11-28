# 慣例與注意事項（補充 AGENTS.md）

## 格式化

`moon fmt` 會把字串內 ≤ 2 個字元的 CJK 文字縮到下一行。因此：

1. 修改 `reports/*.mbt` 後，**先跑 `moon fmt`** 再 `moon fmt --check`，不要手動追格式。
2. `moon.pkg` 與 `zz_deps.mbt` 一律交給 `moon run cmd/tools --target native -- deps`
   重算（舊的 Python 腳本已刪除）。改完 `moon.pkg` 後記得跑 `moon fmt`：工具寫出的
   排版不保證等於 fmt 的斷行規則，但 `deps --check` 是**語義比較**，不會因此誤報。

## 已知地雷（皆已踩過）

- `b9_comp_count(s, obj)` 吃的是**站物件索引**，不是開集索引；開集索引需先經
  `b13_site_obj_of_open` 換算，否則 wasm 會 `unreachable`。
- `b9_components` 假定 `s.opens` 的映射對每個開集都存在；若用 `b9_top` 以原始開集
  清單重建空間，站物件索引可能不連續。
- `B9Top` 沒有 `Eq`/`Debug`，含 `B9Top` 欄位的 struct 不能 `#derive`。
- 測試中的 `inspect(x, content="…")` 需要 `Show`；`Array[Int32]` 請改用
  `@common.b_sh_arr_i32(x)`（格式為 `[1, 2, 3]`，逗號後有空格）。
- 同一套件的多個檔案共用一個 `zz_deps.mbt`；`using` 只能在該檔出現一次。
- 只在 `test` 區塊使用的跨套件名稱要寫 `@alias.name`，否則 `unused_value`。
- **`b14_f2_zero(rows, cols)` 的參數序是 (列, 行)**：`diffs` 必須寫
  `f2_zero(dims[q+1], dims[q])`；寫反會讓每個鏈複形維數全錯，且 `cx_ok` 仍可能回 true。
- **0 列矩陣的列數不可由 `m[0]` 推得**：凡核／Hom／截斷涉及 0 列，一律用
  `b14_f2_kernel_n(m, ncols)` 或顯式傳 ncols，否則 wasm `unreachable`。
- **`b14_cx_ok` 的乘積範圍是 `0 ..< n-2`**（`d^q ∘ d^{q+1}`），寫成 `n-1` 必定越界。
- **`b14_f2_mul` 的 inner 以 `a[0].length()` 為準**；Čech 複形會產生「有列但空列」的
  矩陣，用 `b.length()` 當 inner 會越界。
- **Smith 標準形要再做相鄰 gcd/lcm 歸一**：只做對角化會把 diag(2,3) 誤報成 [2,3]，
  真值是 [1,6]（ℤ/2⊕ℤ/3 ≅ ℤ/6）。
- **`b14_cx_shift` 是截斷式平移，不是懸掛**：要驗「Σ 為等價 / χ(ΣC) = −χ(C)」
  得用 `b14_cx_susp`（真懸掛，長度 +1）。
- **`b14_cx` 的度約定含底部 0 維**：`dims[0]` 是 −1 度，`diffs[q]` 是 q−1 → q。做映射錐／懸掛前
  必須先把鏈映射底部補一個 0 度零塊（`b15.b15_map_susp`），否則 `f.blocks[0]` 落到索引 −1
  而**靜默丟失**：程式不報錯，只是答案錯。LES 與 Euler 恆等式要在「懸掛座標」上驗。
- **`b14_cx_ok` 的 δ² 乘積順序**：舊版寫 `d^q · d^{q+1}`（應為 `d^{q+1} · d^q`）；兩度複形上
  這個檢查本來是空的，只有 3 成員以上的覆蓋才暴露。批次十五已修正並在 3／4 成員覆蓋上真檢定。
- **Čech 覆蓋依賴性不是 bug**：圓環覆蓋 `[13,14]` 給 `H* = [1,1]` 正是 S¹ 的真同調；
  「錯誤」只出現在退化覆蓋（`{2}∪X` 給 `[1,0]`）。寫報告時別把正確答案記成失敗證據。
- **`b15_qs_finite_check` 的子集數是 `2^npts`**（不是 `npts+1`）；位址用 `t % nsub` 解碼。
- `reports/report15.mbt` 內勿用 `fn`／`hn`／`cn`／`sn2` 當變數名（保留字或未使用警告），
  一律 `fnum`／`hnum`／`cnum`／`_`；多行字串拼接每個分支都要以 `)` 收尾並在最後補 `,`。
