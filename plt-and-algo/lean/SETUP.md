# Lean 4 Development Setup

## 1. Install elan (Lean version manager)

**Option A — winget:**
```powershell
winget install -e --id Lean.Elan
```
> **Note:** winget stages `elan-init.exe` but may not run it automatically.
> If `elan` isn't in your PATH after install, run the init manually:
> ```powershell
> & "$env:LOCALAPPDATA\Microsoft\WinGet\Packages\Lean.Elan_Microsoft.Winget.Source_8wekyb3d8bbwe\elan-init.exe" -y
> ```
> Then **restart your shell**. This installs elan to `~/.elan/bin/` and adds it to PATH.

**Option B — manual download:**
1. Download `elan-x86_64-pc-windows-msvc.zip` from https://github.com/leanprover/elan/releases/latest
2. Extract and run `elan-init.exe -y`
3. Restart your shell

After installing, verify:
```powershell
elan --version
lean --version   # should show the toolchain in lean-toolchain
lake --version
```

The `lean-toolchain` file in this repo pins the version automatically — elan will download it on first use.

## 2. Bootstrap the Lake project

```powershell
cd path\to\lean\
lake update     # downloads toolchain + resolves deps
lake build      # builds all libs (Foundations, TaPL, Compilers)
```

## 3. Editor Setup

### VS Code (recommended starting point)
1. Install extension: `leanprover.lean4`
2. Open any `.lean` file — the extension auto-detects the toolchain
3. **Infoview** (`Ctrl+Shift+Enter`): shows current goals and hypotheses in tactic mode. This is your Coq proof-state panel equivalent. Keep it pinned.
4. Useful keybindings:
   - `Ctrl+Shift+Enter` — toggle infoview
   - Click anywhere in a proof — infoview updates to that point's goal state

### Neovim
- Plugin: `Julian/lean.nvim` (setup via lazy.nvim)
- Provides the same infoview via a floating/split window
- `require('lean').setup({ lsp = { on_attach = ... } })`

## 4. WSL2 (optional, but worth considering)

Native Windows works fine for most Lean 4 development. WSL2 becomes worthwhile if you enable mathlib (large builds) or want a more Unix-native workflow.

### Why WSL2?
- **Faster builds**: Lake + mathlib involve thousands of files; Linux filesystem is significantly faster than NTFS for this workload.
- **Shell compatibility**: Lake scripts, CI snippets, and community examples assume Unix shells — no path translation issues.
- **Same tools**: `elan`, `lake`, `lean` all work identically; the Lean 4 toolchain is well-supported on Linux.

### Setup steps

**1. Install WSL2 (if not already):**
```powershell
wsl --install -d Ubuntu
```
Reboot if prompted. Then open Ubuntu from Start menu to finish initial setup (username/password).

**2. Install elan inside WSL:**
```bash
curl https://elan-init.trycloudflare.com -sSf | sh
# Or the direct URL:
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile   # or restart shell
```

**3. Clone/mount your repo:**
- **Option A (recommended)**: Keep your Lean projects on the Linux filesystem (`~/projects/lean/`) for best build performance. Sync with git.
- **Option B**: Access your Windows files via `/mnt/c/Users/Dou/...` — works but builds will be slower due to cross-filesystem I/O.

**4. VS Code remote development:**
```bash
# From inside WSL, in your lean project directory:
code .
```
This opens VS Code on Windows with the **WSL remote** extension, connecting to the WSL filesystem. The `lean4` VS Code extension runs the Lean server inside WSL — you get native Linux build speed with the Windows VS Code GUI. Infoview works normally.

> **Tip**: Install the `WSL` extension in VS Code (`ms-vscode-remote.remote-wsl`) if not already present.

**5. Verify:**
```bash
elan --version
cd ~/projects/lean/   # or wherever you cloned
lake build
```

### When to migrate
- Start on native Windows — it's simpler.
- If `lake build` feels slow (especially after enabling mathlib), or you find yourself fighting path issues, switch to WSL2. Your `.lean` files are plain text and fully portable.

---

## Learning Resources

### Primary — read in roughly this order

| Resource | URL | Notes for Coq users |
|---|---|---|
| **Theorem Proving in Lean 4 (TPIL4)** | https://leanprover.github.io/theorem_proving_in_lean4/ | Closest to SF Vol 1 / Coq reference manual. Start here. Covers dependent types, propositions-as-types, tactic proofs. |
| **Functional Programming in Lean** | https://leanprover.github.io/functional_programming_in_lean/ | Covers the programming side: monads, `do` notation, IO, `partial` defs. Lean 4 is a real programming language — this unlocks it. Essential for compiler work. |
| **Mathematics in Lean** | https://leanprover-community.github.io/mathematics_in_lean/ | Mathlib-heavy. Focuses on math (algebra, topology). Less PL-flavored, but good for learning mathlib idioms once you want the full library. |
| **Lean 4 Metaprogramming** | https://leanprover-community.github.io/lean4-metaprogramming-book/ | Covers macros, tactics-as-programs, `Syntax`, `Elab`. Highly relevant if you want to build custom tactics or AI-tool integrations. |

### TaPL in Lean 4
- No complete Lean 4 port exists yet — good opportunity.
- Start with Ch. 3 (untyped arithmetic) — see `TaPL/Untyped.lean`.
- Ch. 8/9 (simply typed lambda calculus) is the interesting proof target.
- [Software Foundations in Lean 4](https://github.com/leanprover-community/lean4-samples) — partial community ports worth checking.

### Reference
- **Mathlib4 docs**: https://leanprover-community.github.io/mathlib4_docs/ — searchable API reference. Use `exact?`, `apply?`, `simp?` tactics in the editor to find lemmas interactively.
- **Lean Zulip**: https://leanprover.zulipchat.com/ — very active community, fast answers.
- **Lean 4 source / stdlib**: https://github.com/leanprover/lean4

---

## Coq → Lean 4 Cheat Sheet

| Coq | Lean 4 |
|---|---|
| `Lemma` / `Theorem` | `theorem` |
| `Definition` | `def` |
| `Inductive` | `inductive` |
| `match ... with` | `match ... with` (same!) |
| `Proof. ... Qed.` | `by ...` |
| `intros` | `intro` |
| `apply` | `apply` |
| `rewrite <-` | `rw [← ...]` |
| `simpl` | `simp` |
| `auto` | `tauto` / `omega` / `aesop` |
| `omega` | `omega` (same!) |
| `destruct` | `cases` or `rcases` |
| `induction` | `induction ... with` |
| `constructor` | `constructor` |
| `exact ⟨a, b⟩` | `exact ⟨a, b⟩` (same!) |
| `unfold` | `unfold` / `simp only [def]` |
| `Compute` | `#eval` |
| `Check` | `#check` |
| `Print` | `#print` |
| `Set Printing All` | `set_option pp.all true` |

Key differences to internalize:
- Lean 4 is **not** universe-polymorphic by default the same way Coq is — `Sort u` exists but you'll rarely need it early.
- **`simp`** is much more powerful than Coq's `simpl` — it runs a rewrite system. Use `simp?` to see what it did. Use `simp only [...]` to be precise.
- **`omega`** handles linear arithmetic over `Nat` and `Int` — very reliable.
- **`decide`** discharges decidable propositions by computation — great for finite cases.
- There is no `Admitted` — use `sorry` instead.
- Lean's `#check` shows elaborated types; `#print` shows definitions.

---

## Project Structure

```
lean/
├── lakefile.toml       # monorepo config; add modules here
├── lean-toolchain      # pins elan toolchain version
├── SETUP.md            # this file
├── Foundations/        # TPIL4 exercises, basic Lean 4 learning
│   └── Basic.lean
├── TaPL/               # Pierce's TaPL exercises
│   └── Untyped.lean
└── Compilers/          # optimization passes + correctness proofs
    └── Basic.lean
```

To add a new module, create a directory and add a `[[lean_lib]]` entry in `lakefile.toml`.

---

## AI-Assisted Proving

### Current approach
- Open the infoview alongside the AI chat. The infoview shows the exact goal state at each tactic step.
- Paste the goal state into the prompt when asking for help — this is the key context for AI to give precise tactic suggestions.
- Ask for intermediate lemmas rather than full proof scripts; verify each step interactively.

### Lean 4 tools that help AI agents
- **`exact?`** — finds a term that closes the goal from the local context + library.
- **`apply?`** — finds lemmas whose conclusion matches the goal.
- **`simp?`** — shows which simp lemmas fired.
- **`rw?`** — suggests rewrite lemmas.
- These are essentially an interactive premise-retrieval system — analogous to the retrieval step an AI agent would want to do.

### Future ideas (worth exploring)
- **REPL-based agent loop**: Lean 4 has a JSON RPC server (`--server` mode); you can build a tool that feeds goal states to an LLM and applies the suggested tactics, checking the result. The `LeanDojo` project (for Lean 3) pioneered this; Lean 4 ports are emerging.
- **Structured proof search**: the infoview goal state is structured data — more amenable to attention-focused prompting than free text.
- **`Aesop`**: Lean 4's extensible proof-search tactic. You can register your own rules. Relevant for domain-specific automation.
