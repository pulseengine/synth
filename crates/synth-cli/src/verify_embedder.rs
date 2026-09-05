//! `synth verify-embedder` — the EMBEDDER side of the `--relocatable` ARM
//! register contract, checked mechanically (RQ-62-VERIFYEMBED, #1132/#1131).
//!
//! # Why this exists
//!
//! `docs/embedder-abi-relocatable-arm.md` states the contract: R9 (globals
//! base), R10 (linear-memory size) and R11 (linear-memory base) are set by
//! the embedder before the first export runs and NEVER written afterwards —
//! not by synth's code (audited: `scripts/embedder_abi_audit_1131.py`,
//! pinned: `SYNTH-EMBEDDER-ABI-RELOCATABLE-1131`) and not by anything the
//! embedder links beside it. #1131's consumer conformed to that contract
//! correctly BY LUCK, twice: their C shim happened to compile to a bare
//! tail-branch, so GCC never allocated R11 as a frame pointer between boot
//! establishing the registers and synth's code reading them. One more local
//! variable and the linear-memory base silently becomes a frame pointer —
//! the symptom is a wrong value on a control loop, not a build error.
//!
//! `-ffixed-r9 -ffixed-r10 -ffixed-r11` is the fix on the embedder's side,
//! and it is exactly the kind of fix that must be checked on the EMITTED
//! CODE: a flag that silently stopped applying looks identical to one that
//! works. So this subcommand disassembles the linked artifact and REFUSES
//! when any instruction writes R9, R10 or R11.
//!
//! # Design: objdump text, classified fail-closed
//!
//! The disassembly comes from the embedder's own toolchain (`objdump`),
//! which every Cortex-M embedder has and which decodes the full ISA with
//! mapping-symbol code/data separation — synth deliberately does not carry a
//! second, hand-written full-ISA decoder to drift against it (the mirror
//! class this repo keeps deleting). What synth owns is the CLASSIFICATION:
//! for every instruction that MENTIONS a reserved register, decide
//! read-vs-write from the mnemonic's operand semantics, and REFUSE
//! ("cannot classify") on any mnemonic the table does not know. Unknown
//! never passes.
//!
//! The check is deliberately STRICTER than the dynamic contract: a function
//! that saves, repurposes and restores R11 is AAPCS-legal *as long as
//! nothing on that path enters synth code*, but whether it does is not
//! statically evident — so any write refuses, and the establishment site
//! itself (the boot code that legitimately sets the three registers) must be
//! named explicitly with `--allow-writer <symbol>`. The flag is an
//! acknowledgement, not a behaviour change — the honest-refusal shape of
//! `--embedder-data-init`/`--embedder-global-init` (#1041/#1052).
//!
//! # What this CANNOT see (stated, not implied)
//!
//! * **Code not in the ELF you hand it** — a bootloader, ROM routines,
//!   another image, a debugger, or a callee resolved at a later link. Run it
//!   on the final linked image, not only on individual objects.
//! * **Runtime register-context switches** — an RTOS restoring a saved task
//!   context rewrites R9-R11 from memory; the `ldm`/`pop` doing it IS
//!   flagged here, but whether the restored VALUES honour the contract is a
//!   runtime property no static check sees.
//! * **Exception handlers installed at runtime** whose code is outside the
//!   scanned sections, and any runtime-generated or self-modifying code.
//! * **The disassembler's code/data separation.** Literal pools are skipped
//!   as `.word`/`.short` data lines when ARM mapping symbols (`$t`/`$d`) are
//!   present — GNU and LLVM toolchain objects carry them. On a STRIPPED
//!   object the decode of a pool word can desynchronise the stream; the
//!   failure direction is a false refusal or an undecodable line (which also
//!   refuses), but it is objdump's separation being trusted, so it is named
//!   here.
//! * It DOES see inline asm and hand-written `.s` — those are emitted code,
//!   which is the whole point of checking bytes instead of build flags.
//!
//! An indirect STORE through a computed pointer cannot modify a register, so
//! "indirect writes" are not a hole for the registers themselves — the
//! indirect hazard is the context-restore class above.

use anyhow::{Context, Result};
use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;

/// The reserved set of the `--relocatable` embedder contract
/// (docs/embedder-abi-relocatable-arm.md): R9 globals base, R10 linear-memory
/// size in bytes, R11 linear-memory base.
const RESERVED: [&str; 3] = ["r9", "r10", "r11"];

/// How a mnemonic treats its general-purpose register operands.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Class {
    /// Data lines objdump emits for `$d`-mapped regions (`.word`, `.short`,
    /// `.byte`) — not executed, skipped. Counted separately.
    Data,
    /// No GP-register operand of this mnemonic is ever WRITTEN (stores,
    /// compares, branches, hints, `push`/`stm` register lists, `msr`, ...).
    /// Base-register writeback is still caught by the addressing-mode rule,
    /// which applies to every class.
    ReadOnly,
    /// First operand is the destination (the bulk of the ISA: data
    /// processing, single loads, `mrs`, `strex` status, ...).
    DestFirst,
    /// First TWO operands are destinations (`umull`/`smull`/`umlal`/
    /// `smlal`/`umaal`/`smlald`/`smlsld`, `ldrd`, `ldrexd`).
    DestFirstTwo,
    /// Coprocessor read: GP destination is the THIRD operand (`mrc`,
    /// `mrc2`); for `mrrc`/`mrrc2` the third AND fourth.
    MrcThird,
    /// `mrrc`/`mrrc2`: third and fourth operands are GP destinations.
    MrrcThirdFourth,
    /// `pop`/`ldm*`: every register in the `{...}` list is written.
    LoadMultiple,
    /// `vmov` is direction-ambiguous in text: GP operands are written iff
    /// they come BEFORE the FP operand (`vmov r0, s0` writes r0;
    /// `vmov s0, r0` reads it; `vmov r0, r1, d0` writes both).
    Vmov,
}

/// Mnemonic classification table, matched by PREFIX after stripping a
/// trailing `.w`/`.n` width suffix — condition-code and flag-setting
/// suffixes (`moveq`, `adds`, `strexbne`) never change operand direction, so
/// prefix matching absorbs them. LONGEST match wins (`strex*` before `str`,
/// `ldrd`/`ldrexd` before `ldr`, `smull` before `smul`, `bic` before `b`).
///
/// FAIL-CLOSED: a mnemonic matching NO entry, on a line that mentions a
/// reserved register, is a refusal — never a silent pass.
const MNEMONICS: &[(&str, Class)] = &[
    // -- data lines (objdump's $d rendering) ------------------------------
    (".word", Class::Data),
    (".short", Class::Data),
    (".byte", Class::Data),
    (".long", Class::Data),
    // -- loads: multiple, pairs, exclusives, singles ----------------------
    ("ldmia", Class::LoadMultiple),
    ("ldmdb", Class::LoadMultiple),
    ("ldmea", Class::LoadMultiple),
    ("ldmfd", Class::LoadMultiple),
    ("ldm", Class::LoadMultiple),
    ("pop", Class::LoadMultiple),
    ("ldrexd", Class::DestFirstTwo),
    ("ldrex", Class::DestFirst),
    ("ldrd", Class::DestFirstTwo),
    ("ldr", Class::DestFirst), // ldrb/ldrh/ldrsb/ldrsh/ldrbt/... by prefix
    // -- stores (all operands read; writeback caught separately) ----------
    ("strex", Class::DestFirst), // status register destination is first
    ("str", Class::ReadOnly),    // str/strb/strh/strd/strbt/...
    ("push", Class::ReadOnly),
    ("stm", Class::ReadOnly), // stmia/stmdb/...
    // -- VFP/NEON: GP regs appear only as bases (read) except vmov/vmrs ---
    ("vmrs", Class::DestFirst), // vmrs r0, fpscr (APSR_nzcv form: op0 not GP)
    ("vmsr", Class::ReadOnly),
    ("vmov", Class::Vmov),
    ("vldm", Class::ReadOnly), // FP reglist; GP base writeback rule applies
    ("vstm", Class::ReadOnly),
    ("vpop", Class::ReadOnly),
    ("vpush", Class::ReadOnly),
    ("vldr", Class::ReadOnly), // FP destination; GP only as base
    ("vstr", Class::ReadOnly),
    ("vld", Class::ReadOnly), // vld1-4
    ("vst", Class::ReadOnly), // vst1-4
    // every other v* (vadd, vcvt, vcmp, vabs, vneg, vmul, vsqrt, vdiv, vsel,
    // vfma, ...) writes FP registers only; GP regs cannot appear outside the
    // forms above, but keep them classified so an unexpected GP mention
    // fail-closes via ReadOnly? NO — an unknown v-form mentioning a GP reg
    // should refuse, so v* deliberately has NO catch-all entry.
    // -- compares / tests -------------------------------------------------
    ("cmp", Class::ReadOnly),
    ("cmn", Class::ReadOnly),
    ("tst", Class::ReadOnly),
    ("teq", Class::ReadOnly),
    // -- coprocessor ------------------------------------------------------
    ("mrrc2", Class::MrrcThirdFourth),
    ("mrrc", Class::MrrcThirdFourth),
    ("mrc2", Class::MrcThird),
    ("mrc", Class::MrcThird),
    ("mcrr", Class::ReadOnly),
    ("mcr", Class::ReadOnly),
    ("cdp", Class::ReadOnly),
    ("ldc", Class::ReadOnly), // GP only as base; writeback rule applies
    ("stc", Class::ReadOnly),
    // -- system / status --------------------------------------------------
    ("mrs", Class::DestFirst),
    ("msr", Class::ReadOnly),
    // -- branches (LR/PC writes are out of scope: not reserved) -----------
    ("bic", Class::DestFirst), // before the greedy "b"
    ("bfi", Class::DestFirst),
    ("bfc", Class::DestFirst),
    ("bkpt", Class::ReadOnly),
    ("bxns", Class::ReadOnly),
    ("blxns", Class::ReadOnly),
    ("blx", Class::ReadOnly),
    ("bl", Class::ReadOnly),
    ("bx", Class::ReadOnly),
    ("b", Class::ReadOnly), // b/beq/bne.w/ble/... — all conditions
    ("cbz", Class::ReadOnly),
    ("cbnz", Class::ReadOnly),
    ("tbb", Class::ReadOnly),
    ("tbh", Class::ReadOnly),
    // -- hints / barriers / misc no-GP-write ------------------------------
    ("it", Class::ReadOnly), // it/itt/ite/ittt/... (predication only)
    ("nop", Class::ReadOnly),
    ("sev", Class::ReadOnly),
    ("wfe", Class::ReadOnly),
    ("wfi", Class::ReadOnly),
    ("yield", Class::ReadOnly),
    ("dbg", Class::ReadOnly),
    ("dmb", Class::ReadOnly),
    ("dsb", Class::ReadOnly),
    ("isb", Class::ReadOnly),
    ("csdb", Class::ReadOnly),
    ("pldw", Class::ReadOnly),
    ("pld", Class::ReadOnly),
    ("pli", Class::ReadOnly),
    ("svc", Class::ReadOnly),
    ("udf", Class::ReadOnly),
    ("hlt", Class::ReadOnly),
    ("cps", Class::ReadOnly), // cpsie/cpsid
    ("clrex", Class::ReadOnly),
    ("setend", Class::ReadOnly),
    ("sg", Class::ReadOnly),  // v8-M secure gateway
    ("tt", Class::DestFirst), // v8-M tt/tta/ttt/ttat: result into first op
    // -- long multiplies: two destinations --------------------------------
    ("umull", Class::DestFirstTwo),
    ("umlal", Class::DestFirstTwo),
    ("umaal", Class::DestFirstTwo),
    ("smull", Class::DestFirstTwo),
    ("smlald", Class::DestFirstTwo),
    ("smlal", Class::DestFirstTwo), // smlal + smlalbb/bt/tb/tt/d variants
    ("smlsld", Class::DestFirstTwo),
    // -- everything else that writes its first operand --------------------
    ("adc", Class::DestFirst),
    ("addw", Class::DestFirst),
    ("add", Class::DestFirst),
    ("adr", Class::DestFirst),
    ("and", Class::DestFirst),
    ("asr", Class::DestFirst),
    ("clz", Class::DestFirst),
    ("crc32", Class::DestFirst),
    ("eor", Class::DestFirst),
    ("lsl", Class::DestFirst),
    ("lsr", Class::DestFirst),
    ("mla", Class::DestFirst),
    ("mls", Class::DestFirst),
    ("movt", Class::DestFirst),
    ("movw", Class::DestFirst),
    ("mov", Class::DestFirst),
    ("mul", Class::DestFirst),
    ("mvn", Class::DestFirst),
    ("orn", Class::DestFirst),
    ("orr", Class::DestFirst),
    ("pkhbt", Class::DestFirst),
    ("pkhtb", Class::DestFirst),
    ("qadd", Class::DestFirst),
    ("qasx", Class::DestFirst),
    ("qdadd", Class::DestFirst),
    ("qdsub", Class::DestFirst),
    ("qsax", Class::DestFirst),
    ("qsub", Class::DestFirst),
    ("rbit", Class::DestFirst),
    ("rev", Class::DestFirst), // rev/rev16/revsh
    ("ror", Class::DestFirst),
    ("rrx", Class::DestFirst),
    ("rsb", Class::DestFirst),
    ("sadd", Class::DestFirst),
    ("sasx", Class::DestFirst),
    ("sbc", Class::DestFirst),
    ("sbfx", Class::DestFirst),
    ("sdiv", Class::DestFirst),
    ("sel", Class::DestFirst),
    ("shadd", Class::DestFirst),
    ("shasx", Class::DestFirst),
    ("shsax", Class::DestFirst),
    ("shsub", Class::DestFirst),
    ("smla", Class::DestFirst), // smlabb/bt/tb/tt/wb/wt/d/dx (32-bit acc)
    ("smmla", Class::DestFirst),
    ("smmls", Class::DestFirst),
    ("smmul", Class::DestFirst),
    ("smuad", Class::DestFirst),
    ("smul", Class::DestFirst), // smulbb/bt/tb/tt/wb/wt
    ("smusd", Class::DestFirst),
    ("ssat", Class::DestFirst),
    ("ssax", Class::DestFirst),
    ("ssub", Class::DestFirst),
    ("subw", Class::DestFirst),
    ("sub", Class::DestFirst),
    ("sxtab", Class::DestFirst),
    ("sxtah", Class::DestFirst),
    ("sxtb", Class::DestFirst),
    ("sxth", Class::DestFirst),
    ("uadd", Class::DestFirst),
    ("uasx", Class::DestFirst),
    ("ubfx", Class::DestFirst),
    ("udiv", Class::DestFirst),
    ("uhadd", Class::DestFirst),
    ("uhasx", Class::DestFirst),
    ("uhsax", Class::DestFirst),
    ("uhsub", Class::DestFirst),
    ("uqadd", Class::DestFirst),
    ("uqasx", Class::DestFirst),
    ("uqsax", Class::DestFirst),
    ("uqsub", Class::DestFirst),
    ("usad8", Class::DestFirst),
    ("usada8", Class::DestFirst),
    ("usat", Class::DestFirst),
    ("usax", Class::DestFirst),
    ("usub", Class::DestFirst),
    ("uxtab", Class::DestFirst),
    ("uxtah", Class::DestFirst),
    ("uxtb", Class::DestFirst),
    ("uxth", Class::DestFirst),
];

/// One reserved-register write (or unclassifiable instruction) found in the
/// disassembly.
#[derive(Debug)]
pub struct Violation {
    pub symbol: String,
    pub address: String,
    pub text: String,
    pub regs: Vec<String>,
    pub reason: &'static str,
}

/// The result of scanning one disassembly.
#[derive(Debug, Default)]
pub struct ScanReport {
    /// Instruction lines classified (data lines excluded).
    pub instructions: usize,
    /// `<symbol>:` labels seen.
    pub symbols: usize,
    /// Fatal findings, in file order.
    pub violations: Vec<Violation>,
    /// Writes inside `--allow-writer` symbols: symbol -> count.
    pub acknowledged: BTreeMap<String, usize>,
}

/// Normalise one operand token: strip GNU register aliases to plain `rN` and
/// drop syntax adornments that stick to register tokens.
fn norm_reg(tok: &str) -> String {
    let t = tok
        .trim()
        .trim_start_matches('-')
        .trim_end_matches('!')
        .to_ascii_lowercase();
    match t.as_str() {
        "sb" => "r9".into(),
        "sl" => "r10".into(),
        "fp" => "r11".into(),
        "ip" => "r12".into(),
        _ => t,
    }
}

fn is_gp_reg(tok: &str) -> bool {
    matches!(
        tok,
        "r0" | "r1"
            | "r2"
            | "r3"
            | "r4"
            | "r5"
            | "r6"
            | "r7"
            | "r8"
            | "r9"
            | "r10"
            | "r11"
            | "r12"
            | "sp"
            | "lr"
            | "pc"
    )
}

fn is_reserved(tok: &str) -> bool {
    RESERVED.contains(&tok)
}

/// Split an operand string into top-level operands (commas at bracket/brace
/// depth 0), e.g. `"r2, [r11, r12]"` -> `["r2", "[r11, r12]"]`.
fn split_operands(ops: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let (mut depth, mut start) = (0usize, 0usize);
    for (i, c) in ops.char_indices() {
        match c {
            '[' | '{' | '(' => depth += 1,
            ']' | '}' | ')' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                out.push(ops[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    let last = ops[start..].trim();
    if !last.is_empty() {
        out.push(last);
    }
    out.retain(|s| !s.is_empty());
    out
}

/// All register-shaped tokens in a string (any nesting), normalised.
fn reg_tokens(s: &str) -> Vec<String> {
    s.split(|c: char| !c.is_ascii_alphanumeric())
        .filter(|t| !t.is_empty())
        .map(norm_reg)
        .filter(|t| is_gp_reg(t))
        .collect()
}

/// The first register operand of an operand slice, normalised (e.g. the
/// `r2` of `r2, [r11]`, or the `sp` of `sp!, {r4, pc}`).
fn first_reg(op: &str) -> Option<String> {
    let t = norm_reg(op.split([',', ' ']).next()?);
    is_gp_reg(&t).then_some(t)
}

/// Registers WRITTEN via addressing-mode writeback: pre-indexed `[rN, ...]!`
/// and post-indexed `[rN], ...`, plus the `rN!` base of `ldm`/`stm`.
fn writeback_regs(ops: &str) -> Vec<String> {
    let mut out = Vec::new();
    // `[base, ...]!` / `[base]!`  and post-index `[base], ...`
    if let Some(open) = ops.find('[')
        && let Some(close) = ops[open..].find(']').map(|i| open + i)
    {
        let after = ops[close + 1..].trim_start();
        if (after.starts_with('!') || after.starts_with(','))
            && let Some(base) = reg_tokens(&ops[open..close]).first()
        {
            out.push(base.clone());
        }
    }
    // `ldmia sp!, {...}` — a bare `reg!` operand outside brackets.
    for op in split_operands(ops) {
        if let Some(stripped) = op.strip_suffix('!')
            && !op.contains('[')
        {
            let t = norm_reg(stripped);
            if is_gp_reg(&t) {
                out.push(t);
            }
        }
    }
    out
}

/// Classify one mnemonic against [`MNEMONICS`] — longest prefix wins, after
/// stripping the objdump width suffix. `None` = unknown (fail-closed).
fn classify(mnemonic: &str) -> Option<Class> {
    let m = mnemonic.to_ascii_lowercase();
    let m = m
        .strip_suffix(".w")
        .or_else(|| m.strip_suffix(".n"))
        .unwrap_or(&m);
    MNEMONICS
        .iter()
        .filter(|(p, _)| m.starts_with(p))
        .max_by_key(|(p, _)| p.len())
        .map(|(_, c)| *c)
}

/// The set of GP registers this instruction WRITES, per its class — or
/// `Err(reason)` when the line cannot be classified (fail-closed).
fn written_regs(mnemonic: &str, ops: &str) -> Result<Vec<String>, &'static str> {
    let Some(class) = classify(mnemonic) else {
        return Err("unknown mnemonic — cannot classify, refused (fail-closed)");
    };
    if class == Class::Data {
        return Ok(Vec::new());
    }

    let operands = split_operands(ops);
    let mut written = writeback_regs(ops);

    match class {
        Class::Data | Class::ReadOnly => {}
        Class::DestFirst => {
            if let Some(r) = operands.first().and_then(|o| first_reg(o)) {
                written.push(r);
            }
        }
        Class::DestFirstTwo => {
            for op in operands.iter().take(2) {
                if let Some(r) = first_reg(op) {
                    written.push(r);
                }
            }
        }
        Class::MrcThird => {
            if let Some(r) = operands.get(2).and_then(|o| first_reg(o)) {
                written.push(r);
            }
        }
        Class::MrrcThirdFourth => {
            for idx in [2usize, 3] {
                if let Some(r) = operands.get(idx).and_then(|o| first_reg(o)) {
                    written.push(r);
                }
            }
        }
        Class::LoadMultiple => {
            // Every register inside the {...} list is loaded (written).
            if let Some(open) = ops.find('{') {
                let inner = ops[open..].trim_start_matches('{').trim_end_matches('}');
                written.extend(reg_tokens(inner));
            }
        }
        Class::Vmov => {
            // GP operands are destinations iff they LEAD the operand list.
            for op in &operands {
                match first_reg(op) {
                    Some(r) => written.push(r),
                    None => break, // first FP operand — the rest are sources
                }
            }
        }
    }
    Ok(written)
}

/// Parse one objdump line into `(address, mnemonic, operands)` if it is an
/// instruction/data line. Handles both GNU (`   1a:\tf85b 200c \tldr.w\t...`)
/// and LLVM (`      1a: f85b 200c    \tldr.w\t...`) shapes.
fn parse_insn_line(line: &str) -> Option<(String, String, String)> {
    let trimmed = line.trim_start();
    let colon = trimmed.find(':')?;
    let (addr, rest) = trimmed.split_at(colon);
    if addr.is_empty() || !addr.chars().all(|c| c.is_ascii_hexdigit()) {
        return None;
    }
    let rest = &rest[1..]; // past ':'
    // Skip the encoding bytes: whitespace-separated groups of 2/4/8 hex digits.
    let mut toks = rest.split_whitespace().peekable();
    let mut saw_bytes = false;
    while let Some(&t) = toks.peek() {
        let is_bytes = matches!(t.len(), 2 | 4 | 8) && t.chars().all(|c| c.is_ascii_hexdigit());
        if is_bytes {
            saw_bytes = true;
            toks.next();
        } else {
            break;
        }
    }
    if !saw_bytes {
        return None; // symbol line, header, relocation note, ...
    }
    let mnemonic = toks.next()?.to_string();
    // Operands: everything after the mnemonic, up to an objdump comment
    // (`; ...` LLVM, `@ ...` GNU) or a `<symbol+off>` annotation.
    let ops_raw: String = toks.collect::<Vec<_>>().join(" ");
    let mut ops = ops_raw.as_str();
    for sep in [" ;", " @", " //", "<"] {
        if let Some(i) = ops.find(sep) {
            ops = &ops[..i];
        }
    }
    Some((addr.to_string(), mnemonic, ops.trim().to_string()))
}

/// Scan a full objdump disassembly. `allow` lists symbols whose writes are
/// acknowledged (the register-establishment site, e.g. the boot handler).
pub fn scan_disassembly(text: &str, allow: &[String]) -> ScanReport {
    let mut report = ScanReport::default();
    let mut current_symbol = String::from("(before first symbol)");

    for line in text.lines() {
        // Symbol labels: `00000118 <jess_call_rate>:`
        let t = line.trim();
        if t.ends_with(">:")
            && let Some(open) = t.find('<')
        {
            current_symbol = t[open + 1..t.len() - 2].to_string();
            report.symbols += 1;
            continue;
        }
        let Some((addr, mnemonic, ops)) = parse_insn_line(line) else {
            continue;
        };
        // Data lines don't count as instructions; everything else does.
        let is_data = classify(&mnemonic) == Some(Class::Data);
        if !is_data {
            report.instructions += 1;
        }

        // Undecodable code bytes come in several spellings: LLVM `<unknown>`,
        // GNU `.inst 0x...` / `; <UNDEFINED> instruction`. A mnemonic that
        // does not START like a mnemonic is the same class.
        let undecodable = mnemonic.contains("unknown")
            || mnemonic.starts_with(".inst")
            || line.contains("<UNDEFINED>") // GNU's undecodable spelling
            || !mnemonic
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '.');

        let mentioned: Vec<String> = reg_tokens(&ops)
            .into_iter()
            .filter(|r| is_reserved(r))
            .collect();
        if mentioned.is_empty() && !undecodable {
            continue; // cannot write a reserved register it never names
        }

        // Undecodable code bytes: objdump could not classify them, so
        // neither can this check — refuse (fail-closed).
        if undecodable {
            let v = Violation {
                symbol: current_symbol.clone(),
                address: addr,
                text: format!("{mnemonic} {ops}"),
                regs: Vec::new(),
                reason: "undecodable bytes in an executable region — refused (fail-closed)",
            };
            if allow.contains(&current_symbol) {
                *report
                    .acknowledged
                    .entry(current_symbol.clone())
                    .or_default() += 1;
            } else {
                report.violations.push(v);
            }
            continue;
        }

        match written_regs(&mnemonic, &ops) {
            Ok(written) => {
                let hit: Vec<String> = written.into_iter().filter(|r| is_reserved(r)).collect();
                if hit.is_empty() {
                    continue;
                }
                if allow.contains(&current_symbol) {
                    *report
                        .acknowledged
                        .entry(current_symbol.clone())
                        .or_default() += 1;
                } else {
                    report.violations.push(Violation {
                        symbol: current_symbol.clone(),
                        address: addr,
                        text: format!("{mnemonic} {ops}"),
                        regs: hit,
                        reason: "writes a reserved register",
                    });
                }
            }
            Err(reason) => {
                if allow.contains(&current_symbol) {
                    *report
                        .acknowledged
                        .entry(current_symbol.clone())
                        .or_default() += 1;
                } else {
                    report.violations.push(Violation {
                        symbol: current_symbol.clone(),
                        address: addr,
                        text: format!("{mnemonic} {ops}"),
                        regs: mentioned,
                        reason,
                    });
                }
            }
        }
    }
    report
}

/// Run the first working ARM-capable objdump over `input`.
/// Order: `$SYNTH_OBJDUMP` (explicit override, loud failure if it does not
/// work) -> `arm-none-eabi-objdump` -> `llvm-objdump --triple=...` ->
/// `objdump --triple=...` (Apple LLVM) -> `objdump` (GNU multiarch).
fn run_objdump(input: &Path, thumb: bool) -> Result<(String, String)> {
    let triple = if thumb {
        "thumbv7em-none-eabi"
    } else {
        "armv7r-none-eabi"
    };
    let try_tool = |tool: &str, args: &[String]| -> Option<String> {
        let out = Command::new(tool).args(args).arg(input).output().ok()?;
        if !out.status.success() {
            return None;
        }
        let text = String::from_utf8_lossy(&out.stdout).into_owned();
        // Must have decoded at least one instruction to count as "working".
        text.lines()
            .any(|l| parse_insn_line(l).is_some())
            .then_some(text)
    };

    if let Ok(tool) = std::env::var("SYNTH_OBJDUMP") {
        let out = Command::new(&tool)
            .arg("-d")
            .arg(input)
            .output()
            .with_context(|| format!("SYNTH_OBJDUMP={tool} could not be executed"))?;
        anyhow::ensure!(
            out.status.success(),
            "SYNTH_OBJDUMP={tool} failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        return Ok((String::from_utf8_lossy(&out.stdout).into_owned(), tool));
    }

    let candidates: [(&str, Vec<String>); 4] = [
        ("arm-none-eabi-objdump", vec!["-d".into()]),
        (
            "llvm-objdump",
            vec!["-d".into(), format!("--triple={triple}")],
        ),
        ("objdump", vec!["-d".into(), format!("--triple={triple}")]),
        ("objdump", vec!["-d".into()]),
    ];
    for (tool, args) in &candidates {
        if let Some(text) = try_tool(tool, args) {
            return Ok((text, (*tool).to_string()));
        }
    }
    anyhow::bail!(
        "no ARM-capable objdump found (tried arm-none-eabi-objdump, \
         llvm-objdump, objdump; set SYNTH_OBJDUMP=<path> to point at one). \
         verify-embedder checks emitted code, so it needs a disassembler."
    )
}

/// Entry point for `synth verify-embedder`.
pub fn verify_embedder_command(input: &Path, allow_writer: Vec<String>) -> Result<()> {
    anyhow::ensure!(input.exists(), "File not found: {}", input.display());
    let bytes = std::fs::read(input).context("failed to read input")?;
    let Some(thumb) = crate::detect_arm_thumb(&bytes) else {
        anyhow::bail!(
            "{} is not a little-endian ELF32 EM_ARM file — verify-embedder \
             checks the ARM --relocatable embedder contract (R9/R10/R11, \
             docs/embedder-abi-relocatable-arm.md) and has nothing to say \
             about other architectures",
            input.display()
        );
    };

    let (text, tool) = run_objdump(input, thumb)?;
    let report = scan_disassembly(&text, &allow_writer);

    // NON-VACUITY FLOOR: a scan that decoded nothing must not pass — an
    // empty disassembly is indistinguishable from a conforming one only to a
    // check that never looks.
    anyhow::ensure!(
        report.instructions > 0,
        "verify-embedder scanned 0 instructions in {} (via {tool}) — refusing \
         to report conformance about nothing",
        input.display()
    );

    let acknowledged: usize = report.acknowledged.values().sum();
    // --allow-writer names that matched nothing are suspicious: a typo'd
    // symbol silently waives nothing today and masks a future violation.
    for name in &allow_writer {
        if !report.acknowledged.contains_key(name) && !text.contains(&format!("<{name}>:")) {
            anyhow::bail!(
                "--allow-writer {name}: no symbol of that name in {} — refusing \
                 (a misspelled acknowledgement waives nothing and hides drift)",
                input.display()
            );
        }
    }

    if report.violations.is_empty() {
        println!(
            "verify-embedder OK: {} — 0 reserved-register writes in {} \
             instructions across {} symbols (via {tool})",
            input.display(),
            report.instructions,
            report.symbols,
        );
        for (sym, n) in &report.acknowledged {
            println!(
                "  acknowledged (--allow-writer): {sym} — {n} write(s) [the establishment site]"
            );
        }
        println!(
            "  contract: R9=globals base, R10=linmem size, R11=linmem base \
             (docs/embedder-abi-relocatable-arm.md)"
        );
        println!(
            "  bounds: direct writes in THIS ELF's code only — cannot see code \
             outside the image, runtime context switches/exception installs, or \
             stripped-object literal-pool decode; see the doc's verify-embedder \
             section"
        );
        if acknowledged == 0 && allow_writer.is_empty() {
            println!(
                "  note: no --allow-writer given and no writes found — if this \
                 image is supposed to CONTAIN its boot code, the establishment \
                 writes should exist somewhere; an object checked before \
                 linking boot is fine"
            );
        }
        return Ok(());
    }

    eprintln!(
        "verify-embedder REFUSED: {} — {} write(s) to reserved registers \
         R9/R10/R11 (the --relocatable embedder contract, \
         docs/embedder-abi-relocatable-arm.md):",
        input.display(),
        report.violations.len(),
    );
    for v in &report.violations {
        let regs = if v.regs.is_empty() {
            String::new()
        } else {
            format!(" [{}]", v.regs.join(", "))
        };
        eprintln!(
            "  <{}> {}: `{}` — {}{}",
            v.symbol, v.address, v.text, v.reason, regs
        );
    }
    eprintln!(
        "  fix: compile embedder objects with -ffixed-r9 -ffixed-r10 \
         -ffixed-r11; name the register-establishment site (boot code) with \
         --allow-writer <symbol> to acknowledge it"
    );
    anyhow::bail!(
        "{} reserved-register write(s) — the linked code violates the \
         embedder ABI",
        report.violations.len()
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scan(text: &str) -> ScanReport {
        scan_disassembly(text, &[])
    }

    /// GNU-format: a real direct write to R11 (`mov fp, r0`) is refused.
    #[test]
    fn gnu_direct_write_refused() {
        let t = "00000000 <bad_shim>:\n   0:\t4683      \tmov\tfp, r0\n   2:\t4770      \tbx\tlr\n";
        let r = scan(t);
        assert_eq!(r.violations.len(), 1);
        assert_eq!(r.violations[0].regs, vec!["r11"]);
        assert_eq!(r.violations[0].symbol, "bad_shim");
        assert_eq!(r.instructions, 2);
    }

    /// LLVM-format: `mov r11, r0` spelled with plain register names.
    #[test]
    fn llvm_direct_write_refused() {
        let t = "00000000 <bad_shim>:\n       0: 4683         \tmov\tr11, r0\n";
        let r = scan(t);
        assert_eq!(r.violations.len(), 1);
        assert_eq!(r.violations[0].regs, vec!["r11"]);
    }

    /// Reads through the reserved registers are the CONTRACT — never flagged.
    #[test]
    fn reads_pass() {
        let t = concat!(
            "00000008 <run>:\n",
            "   8:\tf85b 200c \tldr.w\tr2, [fp, ip]\n",
            "   c:\tf8d9 3000 \tldr.w\tr3, [r9]\n",
            "  10:\tea4f 451a \tmov.w\tr5, sl, lsr #16\n", // GNU shifted-reg read of sl
            "  14:\t4630      \tmov\tr0, r6\n",
            "  16:\tf8cb 0000 \tstr.w\tr0, [fp]\n",
        );
        let r = scan(t);
        assert!(r.violations.is_empty(), "{:?}", r.violations);
        assert_eq!(r.instructions, 5);
    }

    /// `pop {..., r11, ...}` (frame-pointer save/restore) writes R11.
    #[test]
    fn pop_reglist_refused() {
        let t =
            "00000000 <f>:\n   0:\te8bd 8bf0 \tldmia.w\tsp!, {r4, r5, r6, r7, r8, r9, fp, pc}\n";
        let r = scan(t);
        assert_eq!(r.violations.len(), 1);
        assert_eq!(r.violations[0].regs, vec!["r9", "r11"]);
    }

    /// `push {r11}` READS r11 — allowed (the write is the later pop).
    #[test]
    fn push_reglist_passes() {
        let t = "00000000 <f>:\n   0:\te92d 4880 \tstmdb\tsp!, {r7, fp, lr}\n";
        assert!(scan(t).violations.is_empty());
    }

    /// Writeback addressing writes the base: post-index and pre-index.
    #[test]
    fn writeback_refused() {
        let t = concat!(
            "00000000 <f>:\n",
            "   0:\tf84b 0b04 \tstr.w\tr0, [fp], #4\n",
            "   4:\tf85a 0f04 \tldr.w\tr0, [sl, #4]!\n",
        );
        let r = scan(t);
        assert_eq!(r.violations.len(), 2);
        assert_eq!(r.violations[0].regs, vec!["r11"]);
        assert_eq!(r.violations[1].regs, vec!["r10"]);
    }

    /// Long multiply writes its first TWO operands.
    #[test]
    fn umull_second_dest_refused() {
        let t = "00000000 <f>:\n   0:\tfba0 9b01 \tumull\tr0, fp, r0, r1\n";
        let r = scan(t);
        assert_eq!(r.violations.len(), 1);
        assert_eq!(r.violations[0].regs, vec!["r11"]);
    }

    /// `mrc` writes its THIRD operand (not the first).
    #[test]
    fn mrc_third_operand_refused() {
        let t = "00000000 <f>:\n   0:\tee1d 9f50 \tmrc\tp15, #0, r9, c13, c0, #2\n";
        let r = scan(t);
        assert_eq!(r.violations.len(), 1);
        assert_eq!(r.violations[0].regs, vec!["r9"]);
    }

    /// vmov GP-destination form is a write; FP-destination form is a read.
    #[test]
    fn vmov_direction() {
        let t = "00000000 <f>:\n   0:\tee10 9a10 \tvmov\tr9, s0\n";
        assert_eq!(scan(t).violations.len(), 1);
        let t2 = "00000000 <f>:\n   0:\tee00 9a10 \tvmov\ts0, r9\n";
        assert!(scan(t2).violations.is_empty());
    }

    /// An UNKNOWN mnemonic naming a reserved register refuses (fail-closed).
    #[test]
    fn unknown_mnemonic_fail_closed() {
        let t = "00000000 <f>:\n   0:\tffff ffff \tfrobnicate\tfp, r0\n";
        let r = scan(t);
        assert_eq!(r.violations.len(), 1);
        assert!(r.violations[0].reason.contains("cannot classify"));
    }

    /// An unknown mnemonic NOT touching reserved registers passes — the
    /// check is about the three registers, not about decoding the ISA.
    #[test]
    fn unknown_mnemonic_without_reserved_passes() {
        let t = "00000000 <f>:\n   0:\tffff ffff \tfrobnicate\tr0, r1\n";
        assert!(scan(t).violations.is_empty());
    }

    /// Undecodable bytes in an executable region refuse.
    #[test]
    fn undecodable_refused() {
        let t = "00000000 <f>:\n       0: ffff ffff    \t<unknown>\n";
        let r = scan(t);
        assert_eq!(r.violations.len(), 1);
        assert!(r.violations[0].reason.contains("undecodable"));
    }

    /// Literal-pool data lines (`.word`) are skipped, not refused.
    #[test]
    fn literal_pool_skipped() {
        let t = "00000000 <f>:\n   0:\t4770      \tbx\tlr\n   4:\t20000100 \t.word\t0x20000100\n";
        let r = scan(t);
        assert!(r.violations.is_empty());
        assert_eq!(r.instructions, 1); // .word is not an instruction
    }

    /// --allow-writer converts violations in that symbol to acknowledgements
    /// — and ONLY in that symbol.
    #[test]
    fn allow_writer_scoped() {
        let t = concat!(
            "00000000 <boot_entry>:\n",
            "   0:\t4683      \tmov\tfp, r0\n",
            "00000004 <shim>:\n",
            "   4:\t46b3      \tmov\tfp, r6\n",
        );
        let r = scan_disassembly(t, &["boot_entry".to_string()]);
        assert_eq!(r.violations.len(), 1);
        assert_eq!(r.violations[0].symbol, "shim");
        assert_eq!(r.acknowledged.get("boot_entry"), Some(&1));
    }

    /// Predicated writes (IT blocks) are still writes.
    #[test]
    fn predicated_write_refused() {
        let t = "00000000 <f>:\n   0:\tbf08      \tit\teq\n   2:\t4683      \tmoveq\tfp, r0\n";
        assert_eq!(scan(t).violations.len(), 1);
    }

    /// GNU spells `ldr r9, [pc, #16]` — a load INTO r9 is a write.
    #[test]
    fn load_into_reserved_refused() {
        let t = "00000000 <f>:\n   0:\tf8df 9010 \tldr.w\tr9, [pc, #16]\n";
        let r = scan(t);
        assert_eq!(r.violations.len(), 1);
        assert_eq!(r.violations[0].regs, vec!["r9"]);
    }

    /// A32 (Cortex-R5 path) format: 8-hex-digit encodings parse too.
    #[test]
    fn a32_format_parses() {
        let t = "00000000 <f>:\n   0:\te1a0b000 \tmov\tfp, r0\n   4:\te12fff1e \tbx\tlr\n";
        let r = scan(t);
        assert_eq!(r.violations.len(), 1);
        assert_eq!(r.instructions, 2);
    }

    /// The empty scan reports zero instructions (the caller's non-vacuity
    /// floor turns that into a refusal).
    #[test]
    fn empty_scan_is_vacuous() {
        assert_eq!(scan("no disassembly here\n").instructions, 0);
    }
}
