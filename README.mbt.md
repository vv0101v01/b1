# arena/langlands

**以 MoonBit 實作的「數學結構 → 定理 → 演算法」計算引擎。**

本專案不「陳述」定理，而是把每一條定理降為**可執行的整數／有理數等式**：程式跑完若無 `[FAIL]`，
定理即獲得計算見證；同時誠實標明哪些部分屬「框架假設」（超出有限模型、由文獻保證）。

- 十五個批次、**T1–T497**（批次十三撤下 T449–T454 六條，現存 491 條）、**A1–A105** 條衍生演算法
- 每個批次都有可執行報告：`moon run cmd/main` 逐條輸出 `[PASS]` / `[FAIL]`
- `moon test`：**236 / 236**（含各批白盒測試）
- `moon check --deny-warn` 與 `moon fmt --check` 皆乾淨（CI 把關）
- **倉庫零 Python**：依賴管路、死碼稽核、去重偵測全由 MoonBit 工具 `cmd/tools` 完成（見 `docs/DEBT.md`）
- 死碼 0、逐字重複的函式體 0（`moon run cmd/tools --target native -- audit|dups`）

## 快速開始

```bash
# 安裝 MoonBit 工具鏈
curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash
export PATH="$HOME/.moon/bin:$PATH"

moon check --deny-warn   # 靜態檢查（警告即錯誤）
moon test                # 全部白盒／黑盒測試
moon run cmd/main        # 印出批次一至十四的完整實驗報告
```

## 批次總覽

| 批次 | 主題 | 定理 | 演算法 | 報告 PASS |
|---|---|---|---|---|
| 一 | 整體域 → 局部域 → 阿代爾環 → 伊代爾群 → 志村簇 → 旗簇／仿射格拉斯曼 → 主叢模疊 → 希欽纖維化 → 自守形式 → 自守表示 | T1–T59 | A1–A3 | 見 `docs/reports/REPORT_output.txt` |
| 二 | ℓ-進表示 → Frobenius → 阿廷 L → 自守 L → 函子性 → 基變換 → 自守誘導 → Jacquet–Langlands → 塞塔對應 → 模性定理 | T60–T119 | A4–A7 | `docs/reports/REPORT2_output.txt` |
| 三 | 朗蘭茲 C-群 → 代數自守表示 → 動機伽羅瓦群 → 霍奇–泰特分解 → 德拉姆／半穩定表示 → 完備化上同調 → 卡-朔消滅 → 局部-整體相容性 → 拉福格參數化 | T120–T160 | A8–A12 | `docs/reports/REPORT3_output.txt` |
| 四 | 算術鏡像對稱、Hasse 原理、Motivic L-函數、p-進 Hodge、潛在模性 | T161–T186 | A13–A18 | `docs/reports/REPORT4_output.txt` |
| 五 | 深層代數幾何與算術統計 | T187–T213 | A19–A23 | `docs/reports/REPORT5_output.txt` |
| 六 | 代數與算術結構 | T214–T239 | A24–A28 | `docs/reports/REPORT6_output.txt` |
| 七 | 相對朗蘭茲、p-進幾何、四維拓撲、synergetics | T214–T239 之後續 | A29–A38 | **PASS = 75**（`docs/reports/REPORT7_output.txt`） |
| 八 | 點函子／評估函子 → 拉回沿函子合成 → 餘極限與層化 → 格羅滕迪克宇宙 → 莫里塔等價 → 綜合高階範疇論 → 資訊瓶頸 | T240–T293 | A29–A38 | **PASS = 64，FAIL = 0**（`docs/reports/REPORT8_output.txt`） |
| 九 | 平展拓撲斯 → 預拓撲 → 遺址／篩 → 層化 → 柄／足夠多點 → 幾何態射 → 子拓撲斯 → 群作用拓撲斯 → 層上同調 → 吉羅定理 → 小生成集／有效等價關係 → 分類拓撲斯 | T294–T348 | A39–A48 | **PASS = 65，FAIL = 0**（`docs/reports/REPORT9_output.txt`） |
| 十 | 勒雷譜序列／高階直像 → ∞-遺址／高階吉羅公理 → 拓撲斯基本群／射影有限基本群 | T349–T380 | A49–A56 | **PASS = 51，FAIL = 0**（`docs/reports/REPORT10_output.txt`） |
| 十一 | 豪斯多夫／緊拓撲斯 → 局部／平展／連通幾何態射 → 依賴乘積／六運算 → 導出範疇／反常層／ℓ-進層 → cdh／非交換拓撲斯 | T381–T410 | A57–A64 | **PASS = 49，FAIL = 0**（`docs/reports/REPORT11_output.txt`） |
| 十二 | CZFM 不可達層級 → 存在性／反思雙視角 → 等一致性轉譯網路 → 哥德爾編碼 (T-IN)(L-IN) → 函數提取矛盾 → KPM／弱馬洛／多層塌縮 → n-馬洛・ω-馬洛 → Σ_n-正確／列維綱領 Λ／CU → **全域公理審計（LCT・Mahlo・LC）** | T411–T429 | A65–A75 | **PASS = 30，FAIL = 0**（`docs/reports/REPORT12_output.txt`） |
| 十三 | 拓撲格 → 內在遺址／外化／莫里塔等價 → 擬分離／局部閉合／纖維拓撲斯／平展下降 → 伽羅瓦拓撲斯／Frobenius／基變／Artin・DM 疊 → n-拓撲斯／截斷／凝聚 (∞,1)-拓撲斯／譜層 → 幾何順序／正則順序／內部張量積／內部 Hom／扭子 | T430–T448、T455–T461 | A76–A85 | **PASS = 37，FAIL = 0**（`docs/reports/REPORT13_output.txt`） |
| 十四 | 剛性拓撲／可容許覆蓋／譜空間／有限型拓撲／斯科特拓撲 → 左正合全子範疇／史崔特刻畫／2-單子性／可近範疇／正則範疇 → 反常 t-結構／中介擴張／相交上同調／格羅滕迪克對偶 → 𝔸¹-同倫不變性／動機上同調／函子幾何／下降資料 → 高階吉羅定理／∞-層化／有效群oid／穩定化／點空間 | T462–T484 | A86–A95 | **PASS = 33，FAIL = 0**（`docs/reports/REPORT14_output.txt`） |

每批的定理全集（含見證、反面見證計數、誠實性聲明）見 `THEOREMS*.md`。

## 程式結構

依角色分成套件（每個目錄一個 `moon.pkg`）；根目錄只剩入口與文件，不再平鋪上百個 `*.mbt`：

```
core/        純數學核心（整數／模算術、有限體）           core
common/      跨批次共用小工具                             common
foundation/  批次一至八：b1 … b8                          foundation/b1 … b8
topos/       批次九至十五：b9、b10、b11、b13、b14、b15         topos/b9 … b15
axioms/      全域公理（LCT／Mahlo／LC）與其自洽性審計         axioms
reports/     十五批可執行報告 + 白盒測試（*_wbtest.mbt）   reports
cmd/main/    可執行入口，依序印出十五批報告                cmd/main
cmd/tools/   維護工具（MoonBit）：deps／qualify／audit／dups／stats
docs/        theorems/（定理全集）、reports/（報告輸出快照）
```

- 依賴方向單向無環：`core → common → foundation/b* → topos/b* → axioms → reports → cmd/main`。
- 跨套件名稱集中寫在每套件的 `zz_deps.mbt`（同套件多檔各寫 `using` 會 `[4051] declared twice`）；
  由 `moon run cmd/tools --target native -- deps` 以靜態分析維護，勿手改。
- 只在 `test` 區塊使用的跨套件名稱寫成 `@alias.name`（`cmd/tools qualify` 自動改寫）。
- **倉庫內沒有 Python**：維護腳本全部是 MoonBit（`cmd/tools`），見 `docs/STRUCTURE.md`。
- 命名約定：批次 n 的函式以 `b{n}_` / `b{n}{字母}_` 開頭（例：`b9_cech_h`、`b9r_line`）。
- 目錄歸類理由詳見 `docs/STRUCTURE.md`。

## 工程紀律

- **精確性**：見證一律是整數、精確有理數、BigInt 十進位位數，或殘差 < 1e-12；不使用「取樣成立」。
- **誠實分層**：每條定理標「計算所得」或「框架假設」；反面見證逐條計數（例：批次九 T306 → 3、T321 → 12；批次十 10 例，見 `docs/theorems/THEOREMS10.md`；批次十一 11 例，見 `docs/theorems/THEOREMS11.md`）。
- **公理誠實**：全域公理不靠宣告成立，而是降為有限模型上的可反駁檢核；找不到反例才 `[PASS]`，
  且「哥德爾殘餘」（G2 的 Con、有限域的馬洛性）一律顯式標記為永不可得（見 `docs/theorems/THEOREMS12.md`）；批次十三把 21 個拓撲斯／疊論名詞降為有限可判定模型，逐條列出七項殘餘缺口，並在除錯去重階段
   **主動撤下 6 條判定恆真／循環的定理**（見 `docs/theorems/THEOREMS13.md`）；
   批次十四把 23 個同倫／反常／無窮名詞降為有限可判定模型，並列出八項框架假設與
   一個**被計算推翻的猜想**（K^M₂(F₅) = ℤ/2 → 實算為 0，見 `docs/theorems/THEOREMS14.md`）；
   批次十五以**歸納法與反證法**補上批次十三／十四殘留的 13 個缺口（度 1 → 度 2、n = 1 → 對 n、
   影子 → 真截斷），並修正 b14 的兩處實作錯誤（`cx_ok` 的 δ² 乘積順序、映射錐的底部度偏移），
   見 `docs/theorems/THEOREMS15.md`。
- **零死碼**：未使用的函式會被測試覆蓋或移除；`moon check --deny-warn` 保證無未用變數與可達性問題。
- **CI**：GitHub Actions 依序執行 `moon fmt --check`、`moon check --deny-warn`、`moon test`，
  並要求報告輸出不含任何 `[FAIL]`。

## 授權

見 `LICENSE`。
